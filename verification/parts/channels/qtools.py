"""Small exact-arithmetic and linear-algebra helpers shared by the checks of this repository."""
from fractions import Fraction
from functools import reduce
import math

import numpy as np

I2 = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)
HAD = np.array([[1, 1], [1, -1]], dtype=complex) / math.sqrt(2)
LN2 = math.log(2)


def kron(*ops):
    return reduce(np.kron, ops)


def ket(bits, dims=None):
    """Computational-basis ket for a tuple of digits."""
    dims = dims or [2] * len(bits)
    v = np.zeros(int(np.prod(dims)), dtype=complex)
    idx = 0
    for b, d in zip(bits, dims):
        idx = idx * d + b
    v[idx] = 1
    return v


def dm(v):
    v = np.asarray(v, dtype=complex).reshape(-1)
    return np.outer(v, v.conj())


def embed(op, sites, dims):
    """The operator `op`, acting on the listed subsystems (in that order), as an operator on all of `dims`."""
    n = len(dims)
    sites = list(sites)
    rest = [i for i in range(n) if i not in sites]
    full = np.kron(op, np.eye(int(np.prod([dims[i] for i in rest])) if rest else 1))
    order = sites + rest
    shape = [dims[i] for i in order]
    t = full.reshape(shape + shape)
    perm = [order.index(i) for i in range(n)]
    t = t.transpose(perm + [p + n for p in perm])
    d = int(np.prod(dims))
    return t.reshape(d, d)


def ptrace(rho, dims, keep):
    """Partial trace keeping the listed subsystems, in increasing order."""
    n = len(dims)
    keep = sorted(keep)
    t = np.asarray(rho).reshape(list(dims) + list(dims))
    letters = "abcdefghijklmnopqrstuvwxyz"
    row = [letters[i] for i in range(n)]
    col = [letters[i].upper() if i in keep else letters[i] for i in range(n)]
    out = [letters[i] for i in keep] + [letters[i].upper() for i in keep]
    t = np.einsum("".join(row) + "".join(col) + "->" + "".join(out), t)
    dk = int(np.prod([dims[i] for i in keep])) if keep else 1
    return t.reshape(dk, dk)


def entropy(rho):
    """von Neumann entropy in bits."""
    w = np.linalg.eigvalsh((rho + rho.conj().T) / 2)
    w = w[w > 1e-14]
    return float(-np.sum(w * np.log2(w)))


def h2(p):
    if p <= 0 or p >= 1:
        return 0.0
    return -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def shannon(p):
    p = np.asarray(p, float)
    p = p[p > 0]
    return float(-np.sum(p * np.log2(p)))


def random_unitary(d, rng):
    z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / math.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def near_unitary(u, eps, rng):
    """u multiplied by exp(i eps K) for a random Hermitian K of unit operator norm."""
    d = u.shape[0]
    k = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    k = (k + k.conj().T) / 2
    k /= np.linalg.norm(k, 2)
    w, v = np.linalg.eigh(k)
    return (v * np.exp(1j * eps * w)) @ v.conj().T @ u


def random_density(d, rng, rank=None):
    rank = rank or d
    g = rng.standard_normal((d, rank)) + 1j * rng.standard_normal((d, rank))
    rho = g @ g.conj().T
    return rho / np.trace(rho).real


def apply(u, rho):
    return u @ rho @ u.conj().T


def trace_norm(a):
    return float(np.sum(np.abs(np.linalg.eigvalsh((a + a.conj().T) / 2))))


# ----------------------------------------------------------------------------------------------
# Additions for this repository
# ----------------------------------------------------------------------------------------------

def herm(a):
    return (a + a.conj().T) / 2


def mfun(a, f):
    """f applied to the Hermitian matrix a through its spectral decomposition."""
    w, v = np.linalg.eigh(herm(a))
    return (v * f(w)) @ v.conj().T


def msqrt(a):
    return mfun(a, lambda w: np.sqrt(np.clip(w, 0, None)))


def random_herm(d, rng):
    g = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    return (g + g.conj().T) / 2


def relent(rho, sigma):
    """Relative entropy D(rho||sigma) in bits (sigma of full rank on the support of rho)."""
    w, v = np.linalg.eigh(herm(sigma))
    logs = (v * np.log2(np.clip(w, 1e-300, None))) @ v.conj().T
    return -entropy(rho) - float(np.trace(herm(rho) @ logs).real)


def cond_entropy(rho, dims, a):
    """S(A|rest) in bits, A the listed subsystems."""
    rest = [i for i in range(len(dims)) if i not in a]
    return entropy(rho) - entropy(ptrace(rho, dims, rest))


def mutual_info(rho, dims, a, b):
    return entropy(ptrace(rho, dims, a)) + entropy(ptrace(rho, dims, b)) - entropy(ptrace(rho, dims, sorted(a + b)))


def g_afw(D, t):
    """Alicki-Fannes-Winter modulus g_D(t) = 2 t log2 D + (1 + t) h(t/(1 + t)), in bits."""
    return 2 * t * math.log2(D) + (1 + t) * h2(t / (1 + t))


def kraus_apply(K, rho):
    return sum(k @ rho @ k.conj().T for k in K)


def kraus_dual(K, x):
    return sum(k.conj().T @ x @ k for k in K)


def complementary(K, rho):
    """Complementary channel: entries Tr(K_i rho K_j^*)."""
    r = len(K)
    out = np.zeros((r, r), dtype=complex)
    for i in range(r):
        for j in range(r):
            out[i, j] = np.trace(K[i] @ rho @ K[j].conj().T)
    return out


def stinespring(K):
    """Isometry V: A -> O (x) E with V|psi> = sum_k K_k|psi> (x) |k>."""
    dout, din = K[0].shape
    r = len(K)
    V = np.zeros((dout * r, din), dtype=complex)
    for k, A in enumerate(K):
        for i in range(dout):
            V[i * r + k, :] = A[i, :]
    return V


def choi_of_map(fn, din):
    """Unnormalized Choi matrix sum_ij |i><j| (x) fn(|i><j|), input first."""
    blocks = []
    for i in range(din):
        row = []
        for j in range(din):
            e = np.zeros((din, din), dtype=complex)
            e[i, j] = 1
            row.append(fn(e))
        blocks.append(row)
    dout = blocks[0][0].shape[0]
    J = np.zeros((din * dout, din * dout), dtype=complex)
    for i in range(din):
        for j in range(din):
            J[i * dout:(i + 1) * dout, j * dout:(j + 1) * dout] = blocks[i][j]
    return J


def diamond_norm_herm(J, din, dout):
    """Diamond norm of a Hermiticity-preserving map with unnormalized Choi matrix J (input first):
    min lambda_max(Tr_out(P + N)) over P, N >= 0 with P - N = J (Watrous), solved with cvxpy."""
    import cvxpy as cp
    n = din * dout
    P = cp.Variable((n, n), hermitian=True)
    N = cp.Variable((n, n), hermitian=True)
    t = cp.Variable()
    S = P + N
    blocks = [[sum(S[i * dout + k, j * dout + k] for k in range(dout)) for j in range(din)] for i in range(din)]
    TrS = cp.bmat(blocks)
    cons = [P >> 0, N >> 0, P - N == herm(J), t * np.eye(din) - TrS >> 0]
    prob = cp.Problem(cp.Minimize(t), cons)
    import warnings
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        prob.solve(solver=cp.CLARABEL)
        if prob.status != cp.OPTIMAL:
            prob.solve(solver=cp.SCS, eps=1e-9, max_iters=200000)
    if prob.status not in (cp.OPTIMAL, cp.OPTIMAL_INACCURATE):
        raise RuntimeError(f"diamond-norm SDP failed: {prob.status}")
    return float(t.value)


def half_diamond_distance(J1, J2, din, dout):
    return 0.5 * diamond_norm_herm(J1 - J2, din, dout)


def conserving_unitary(Htot, rng, tol=1e-9):
    """A random unitary that commutes exactly (to rounding) with the Hermitian Htot: a Haar unitary inside each
    eigenspace."""
    ev, vecs = np.linalg.eigh(herm(Htot))
    U = np.zeros_like(vecs, dtype=complex)
    done = np.zeros(len(ev), bool)
    for i in range(len(ev)):
        if done[i]:
            continue
        sel = np.abs(ev - ev[i]) < tol
        done |= sel
        blk = vecs[:, sel]
        U += blk @ random_unitary(blk.shape[1], rng) @ blk.conj().T
    return U


def gibbs(H, beta=1.0):
    w, v = np.linalg.eigh(herm(H))
    e = np.exp(-beta * (w - w.min()))
    return (v * (e / e.sum())) @ v.conj().T


def op_from_herm_numbers(H):
    return np.diag(np.asarray(H, float)).astype(complex)


class Report:
    """Collects named checks, prints each one, and exits with status 1 if any failed."""

    def __init__(self, title):
        self.title = title
        self.failed = []
        print(title)

    def check(self, name, ok, detail=""):
        print(("  ok    " if ok else "  FAIL  ") + name + (f"  [{detail}]" if detail else ""), flush=True)
        if not ok:
            self.failed.append(name)

    def close(self):
        if self.failed:
            print(f"{len(self.failed)} check(s) failed.")
            raise SystemExit(1)
        print("All checks passed.")


# ----------------------------------------------------------------------------------------------
# Rigorous rational bounds for logarithms (used where a quoted digit must be certified)
# ----------------------------------------------------------------------------------------------

def _atanh_bounds(z, K=80):
    """Lower and upper rational bounds for atanh(z), 0 <= z < 1 rational, from the series and its tail."""
    s = Fraction(0)
    zz = z * z
    p = z
    for k in range(K):
        s += p / (2 * k + 1)
        p *= zz
    return s, s + p / ((2 * K + 1) * (1 - zz))


_LN2 = None


def ln2_bounds():
    global _LN2
    if _LN2 is None:
        lo, hi = _atanh_bounds(Fraction(1, 3), 160)
        _LN2 = (2 * lo, 2 * hi)
    return _LN2


def ln_bounds(y):
    """Rational interval containing ln y, for rational y > 0."""
    y = Fraction(y)
    assert y > 0
    k = 0
    while y > Fraction(3, 2):
        y /= 2
        k += 1
    while y < Fraction(3, 4):
        y *= 2
        k -= 1
    z = (y - 1) / (y + 1)
    neg = z < 0
    lo, hi = _atanh_bounds(abs(z), 160)
    lo, hi = 2 * lo, 2 * hi
    if neg:
        lo, hi = -hi, -lo
    a, b = ln2_bounds()
    if k >= 0:
        return lo + k * a, hi + k * b
    return lo + k * b, hi + k * a


def log2_bounds(y):
    lo, hi = ln_bounds(y)
    a, b = ln2_bounds()
    c = [lo / a, lo / b, hi / a, hi / b]
    return min(c), max(c)


def h2_bounds(q):
    """Rational interval for the binary entropy (bits) of a rational q in (0, 1)."""
    q = Fraction(q)
    l1, u1 = log2_bounds(q)
    l2, u2 = log2_bounds(1 - q)
    return -q * u1 - (1 - q) * u2, -q * l1 - (1 - q) * l2


def sqrt_bounds(r, digits=60):
    r = Fraction(r)
    S = 10 ** digits
    lo = Fraction(math.isqrt(r.numerator * S * S // r.denominator), S)
    hi = lo + Fraction(1, S)
    assert lo * lo <= r <= hi * hi
    return lo, hi
