"""Small exact-arithmetic and linear-algebra helpers shared by the checks of this repository."""
from functools import reduce
import math
import warnings

import numpy as np

warnings.filterwarnings("ignore", message=".*CUDA path could not be detected.*")
# SDP solutions are used with explicit tolerances and re-verified downstream; cvxpy's reduced-accuracy notice is noise.
warnings.filterwarnings("ignore", message=".*Solution may be inaccurate.*")

I2 = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)
HAD = np.array([[1, 1], [1, -1]], dtype=complex) / math.sqrt(2)
CNOT = np.eye(4, dtype=complex)[[0, 1, 3, 2]]          # control first qubit, target second
CZ = np.diag([1, 1, 1, -1]).astype(complex)
P0 = np.diag([1, 0]).astype(complex)
P1 = np.diag([0, 1]).astype(complex)


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


def permute(rho, dims, order):
    """Reorder the subsystems of an operator: the result has subsystem order[k] in position k."""
    n = len(dims)
    t = np.asarray(rho).reshape(list(dims) + list(dims))
    t = t.transpose(list(order) + [o + n for o in order])
    d = int(np.prod(dims))
    return t.reshape(d, d)


def herm(a):
    return (a + a.conj().T) / 2


def eigh_psd(rho, tol=1e-15):
    w, v = np.linalg.eigh(herm(rho))
    return np.clip(w, 0, None), v


def entropy(rho):
    """von Neumann entropy in bits."""
    w = np.linalg.eigvalsh(herm(rho))
    w = w[w > 1e-14]
    return float(-np.sum(w * np.log2(w)))


def entropy_nat(rho):
    w = np.linalg.eigvalsh(herm(rho))
    w = w[w > 1e-15]
    return float(-np.sum(w * np.log(w)))


def logm_psd(rho, base=2.0, floor=1e-300):
    """Matrix logarithm of a positive operator (on its support; zero eigenvalues are floored)."""
    w, v = np.linalg.eigh(herm(rho))
    w = np.clip(w, floor, None)
    return (v * (np.log(w) / math.log(base))) @ v.conj().T


def sqrtm_psd(rho):
    w, v = np.linalg.eigh(herm(rho))
    return (v * np.sqrt(np.clip(w, 0, None))) @ v.conj().T


def relent(rho, sigma, base=2.0):
    """Relative entropy D(rho||sigma) (assumes supp rho inside supp sigma)."""
    return float(np.trace(rho @ (logm_psd(rho, base) - logm_psd(sigma, base))).real)


def h2(p):
    if p <= 0 or p >= 1:
        return 0.0
    return -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def hnat(p):
    if p <= 0 or p >= 1:
        return 0.0
    return -p * math.log(p) - (1 - p) * math.log(1 - p)


def shannon(p):
    p = np.asarray(p, float)
    p = p[p > 0]
    return float(-np.sum(p * np.log2(p)))


def random_unitary(d, rng):
    z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / math.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def random_isometry(d_out, d_in, rng):
    return random_unitary(d_out, rng)[:, :d_in]


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


def random_state(d, rng):
    v = rng.standard_normal(d) + 1j * rng.standard_normal(d)
    return v / np.linalg.norm(v)


def apply(u, rho):
    return u @ rho @ u.conj().T


def trace_norm(a):
    return float(np.sum(np.abs(np.linalg.eigvalsh((a + a.conj().T) / 2))))


def gibbs(H, beta):
    w, v = np.linalg.eigh(herm(H))
    p = np.exp(-beta * (w - w.min()))
    p /= p.sum()
    return (v * p) @ v.conj().T


def random_energy_conserving_unitary(energies, rng):
    """A random unitary that is block diagonal in the eigenspaces of a diagonal Hamiltonian with the given energies."""
    energies = np.asarray(energies)
    n = len(energies)
    u = np.zeros((n, n), dtype=complex)
    for e in np.unique(np.round(energies, 12)):
        idx = np.where(np.abs(energies - e) < 1e-9)[0]
        u[np.ix_(idx, idx)] = random_unitary(len(idx), rng)
    return u


class Report:
    """Collects named checks, prints each one, and exits with status 1 if any failed."""

    def __init__(self, title):
        self.title = title
        self.failed = []
        print(title)

    def check(self, name, ok, detail=""):
        ok = bool(ok)
        print(("  ok    " if ok else "  FAIL  ") + name + (f"  [{detail}]" if detail else ""), flush=True)
        if not ok:
            self.failed.append(name)

    def close(self):
        if self.failed:
            print(f"{len(self.failed)} check(s) failed.")
            raise SystemExit(1)
        print("All checks passed.")
