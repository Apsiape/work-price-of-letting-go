"""Small exact-arithmetic and linear-algebra helpers shared by the checks of this repository.

The first part is the helper set of the companion repositories (qubit operators, partial traces, entropies in bits,
random states and unitaries, the Report class). The second part adds what the checks of this paper need: entropies in
nats, a channel class with its complementary channel, the half diamond distance by semidefinite programming, and the
batch cost B(Phi) computed from both sides, as a primal lower bound and a dual upper bound.
"""
from functools import reduce
import math

import numpy as np

I2 = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)
HAD = np.array([[1, 1], [1, -1]], dtype=complex) / math.sqrt(2)


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


# ---------------------------------------------------------------------------------------------------------------------
# Additions for this paper: natural-log entropies, Hermitian functional calculus, channels and their complements.
# ---------------------------------------------------------------------------------------------------------------------

def herm(a):
    return (a + a.conj().T) / 2


def dag(a):
    return a.conj().T


def opnorm(a):
    return float(np.linalg.norm(a, 2))


def S(rho):
    """von Neumann entropy in nats."""
    w = np.linalg.eigvalsh(herm(rho))
    w = w[w > 1e-15]
    return float(-np.sum(w * np.log(w)))


def H_nats(p):
    p = np.asarray(p, float)
    p = p[p > 0]
    return float(-np.sum(p * np.log(p)))


def logm_h(a, floor=1e-300):
    w, v = np.linalg.eigh(herm(a))
    return (v * np.log(np.maximum(w, floor))) @ dag(v)


def expm_h(a):
    w, v = np.linalg.eigh(herm(a))
    return (v * np.exp(w)) @ dag(v)


def powm_h(a, p):
    w, v = np.linalg.eigh(herm(a))
    return (v * np.maximum(w, 0) ** p) @ dag(v)


def relent(r, s):
    """Relative entropy D(r||s) in nats."""
    return float(np.real(np.trace(r @ (logm_h(r) - logm_h(s)))))


def fidelity(r, s):
    """Root fidelity ||sqrt(r) sqrt(s)||_1."""
    a = powm_h(r, 0.5) @ powm_h(s, 0.5)
    return float(np.sum(np.linalg.svd(a, compute_uv=False)))


def hermitian_basis(d):
    out = []
    for i in range(d):
        e = np.zeros((d, d), dtype=complex)
        e[i, i] = 1
        out.append(e)
    for i in range(d):
        for j in range(i + 1, d):
            e = np.zeros((d, d), dtype=complex)
            e[i, j] = e[j, i] = 1 / math.sqrt(2)
            out.append(e)
            e = np.zeros((d, d), dtype=complex)
            e[i, j], e[j, i] = -1j / math.sqrt(2), 1j / math.sqrt(2)
            out.append(e)
    return out


def span_residual(target, ops):
    """Hilbert-Schmidt distance of `target` from the complex span of `ops`, relative to ||target|| (or to 1e-9)."""
    m = np.array([o.reshape(-1) for o in ops]).T
    t = target.reshape(-1)
    coef, *_ = np.linalg.lstsq(m, t, rcond=None)
    return float(np.linalg.norm(m @ coef - t) / max(1e-9, np.linalg.norm(t)))


def kraus_from_choi(j, din, dout, tol=1e-10):
    """Kraus operators from a Choi matrix J = sum_{ij} |i><j| (x) Phi(|i><j|) (input first)."""
    w, u = np.linalg.eigh(herm(j))
    out = []
    for lam, vec in zip(w, u.T):
        if lam > tol:
            out.append(math.sqrt(lam) * vec.reshape(din, dout).T)
    return out


class Channel:
    """A channel given by Kraus operators K_k, with Hamiltonian H at input and output and inverse temperature beta.

    Stinespring V = sum_k K_k (x) |k>_E (output first); complementary channel Psi(rho)_{kl} = Tr K_k rho K_l^*,
    so that Psi^*(Y) = sum_{kl} Y_{lk} K_l^* K_k; energy change D = Phi^*(H) - H.
    """

    def __init__(self, kraus, H, beta=1.0):
        self.K = [np.asarray(k, dtype=complex) for k in kraus]
        self.H = np.asarray(H, dtype=complex)
        self.beta = float(beta)
        self.d = self.K[0].shape[1]
        self.r = len(self.K)
        v = np.zeros((self.d * self.r, self.d), dtype=complex)
        for k, kk in enumerate(self.K):
            e = np.zeros((self.r, 1))
            e[k] = 1
            v += np.kron(kk, e)
        self.V = v
        self.D = herm(self.phistar(self.H) - self.H)

    def tp_error(self):
        return opnorm(dag(self.V) @ self.V - np.eye(self.d))

    def phi(self, rho):
        return sum(k @ rho @ dag(k) for k in self.K)

    def phistar(self, x):
        return sum(dag(k) @ x @ k for k in self.K)

    def psi(self, rho):
        out = np.zeros((self.r, self.r), dtype=complex)
        for k in range(self.r):
            for l in range(self.r):
                out[k, l] = np.trace(self.K[k] @ rho @ dag(self.K[l]))
        return out

    def psistar(self, y):
        out = np.zeros((self.d, self.d), dtype=complex)
        for k in range(self.r):
            for l in range(self.r):
                out += y[l, k] * dag(self.K[l]) @ self.K[k]
        return out

    def products(self):
        return [dag(a) @ b for a in self.K for b in self.K]

    def h(self, sigma):
        """h_Phi(sigma) = S(sigma) - S(Phi(sigma)) = S(E|O), in nats."""
        return S(sigma) - S(self.phi(sigma))

    def choi(self):
        d = self.d
        j = np.zeros((d * d, d * d), dtype=complex)
        for i in range(d):
            for k in range(d):
                e = np.zeros((d, d), dtype=complex)
                e[i, k] = 1
                j += np.kron(e, self.phi(e))
        return j

    def balance_residual(self):
        """Relative distance of D from the span of the K_i^* K_j (zero exactly when the channel is balanced)."""
        return span_residual(self.D, self.products())

    def psi_kernel_hermitian(self, tol=1e-10):
        """A real basis of the Hermitian X with Psi(X) = 0."""
        from scipy.linalg import null_space
        hb = hermitian_basis(self.d)
        cols = []
        for e in hb:
            c = self.psi(e).reshape(-1)
            cols.append(np.concatenate([c.real, c.imag]))
        ns = null_space(np.array(cols).T, rcond=tol)
        return [herm(sum(ns[k, j] * hb[k] for k in range(len(hb)))) for j in range(ns.shape[1])]


def gmax(ch, Xop, iters=20000, tol=1e-14, sigma0=None):
    """max over states of F(sigma) = h_Phi(sigma)/beta + Tr sigma X, a concave function.

    Entropic mirror ascent with backtracking. Returns (lower, upper, sigma): `lower` = F(sigma) at the final iterate and
    `upper` = F(sigma) + lambda_max(G) - Tr sigma G, with G the gradient at sigma; by concavity `upper` bounds the maximum
    from above whenever sigma is faithful (the Frank-Wolfe gap).
    """
    b = ch.beta
    d = ch.d
    Xh = herm(Xop)

    def F(s):
        return ch.h(s) / b + float(np.real(np.trace(s @ Xh)))

    def grad(s):
        return herm((-logm_h(s) + ch.phistar(logm_h(ch.phi(s)))) / b + Xh)

    sig = np.eye(d, dtype=complex) / d if sigma0 is None else herm(sigma0)
    val = F(sig)
    step = 1.0
    for it in range(iters):
        ls = logm_h(sig)
        target = ch.phistar(logm_h(ch.phi(sig))) + b * Xh
        while True:
            m = herm((1 - step) * ls + step * target)
            m -= np.max(np.linalg.eigvalsh(m)) * np.eye(d)
            new = expm_h(m)
            new /= np.trace(new).real
            nv = F(new)
            if nv >= val - 1e-16 or step < 1e-8:
                break
            step *= 0.5
        done = abs(nv - val) < tol and it > 20
        sig, val = new, nv
        step = min(1.0, step * 1.5)
        if done:
            break
    g = grad(sig)
    gap = float(np.max(np.linalg.eigvalsh(g)) - np.real(np.trace(sig @ g)))
    return val, val + max(gap, 0.0), sig


def capacity(ch, **kw):
    """Thermodynamic capacity max_rho [F(Phi rho) - F(rho)] = max_sigma [h(sigma)/beta + Tr sigma D]: (lower, upper)."""
    lo, up, s = gmax(ch, ch.D, **kw)
    return lo, up, s


def dual_value(ch, y, **kw):
    """Upper bound t_Y + g_Y on B(Phi) for a Hermitian Y on the environment (g_Y bounded from above)."""
    py = herm(ch.psistar(y))
    t = float(np.max(np.linalg.eigvalsh(herm(ch.D - py))))
    lo, up, s = gmax(ch, py, **kw)
    return t + up, t + lo, s


def _inner_programs(ch):
    """The primal and dual inner programs of a channel, compiled once (and stored on the channel) with Psi(sigma) as a
    parameter."""
    import cvxpy as cp
    if getattr(ch, "_inner", None) is not None:
        return ch._inner
    d, r = ch.d, ch.r
    # real parametrisation of the Hermitian matrix Psi(sigma): its real and imaginary parts
    pre = cp.Parameter((r, r))
    pim = cp.Parameter((r, r))
    rho = cp.Variable((d, d), hermitian=True)
    cons = [rho >> 0]
    for k in range(r):
        for l in range(r):
            m = dag(ch.K[l]) @ ch.K[k]
            val = cp.trace(m @ rho)
            cons += [cp.real(val) == pre[k, l], cp.imag(val) == pim[k, l]]
    prob = cp.Problem(cp.Maximize(cp.real(cp.trace(rho @ ch.D))), cons)
    yv = cp.Variable((r, r), hermitian=True)
    t = cp.Variable()
    pys = sum(yv[l, k] * (dag(ch.K[l]) @ ch.K[k]) for k in range(r) for l in range(r))
    mm = t * np.eye(d) - (ch.D - pys)
    # Tr(Psi(sigma) Y) for Hermitian Psi(sigma) and Y: sum over entries of Re(P) Re(Y) + Im(P) Im(Y)
    obj = t + cp.sum(cp.multiply(pre, cp.real(yv))) + cp.sum(cp.multiply(pim, cp.imag(yv)))
    dprob = cp.Problem(cp.Minimize(obj), [(mm + mm.H) / 2 >> 0, cp.norm(yv, "fro") <= 1e3])
    ch._inner = (pre, pim, rho, prob, yv, dprob)
    return ch._inner


def _solve(prob):
    import cvxpy as cp
    try:
        prob.solve(solver="CLARABEL")
        if prob.status in ("optimal", "optimal_inaccurate"):
            return
    except cp.error.SolverError:
        pass
    prob.solve(solver="SCS", eps=1e-10, max_iters=200000)


def inner_sdp(ch, sigma, dual=True):
    """f(sigma) = max{Tr rho D : Psi(rho) = Psi(sigma), rho >= 0} and its dual: (value, rho, Y).

    The dual is min{t + Tr Psi(sigma) Y : t I >= D - Psi^*(Y)}, solved as a separate program (skipped if dual=False).
    """
    pre, pim, rho, prob, yv, dprob = _inner_programs(ch)
    ps = herm(ch.psi(sigma))
    pre.value, pim.value = np.real(ps), np.imag(ps)
    _solve(prob)
    yval = None
    if dual:
        _solve(dprob)
        yval = herm(np.asarray(yv.value))
    return prob.value, herm(np.asarray(rho.value)), yval


def primal_value(ch, sigma, rho):
    """Exact objective of a pair (rho, sigma) and its feasibility residual ||Psi(rho) - Psi(sigma)||."""
    val = float(np.real(np.trace(rho @ ch.D))) + ch.h(sigma) / ch.beta
    res = float(np.linalg.norm(ch.psi(rho) - ch.psi(sigma)))
    neg = float(min(0.0, np.min(np.linalg.eigvalsh(herm(rho)))))
    return val, res, neg


def batch_cost(ch, iters=150, seed=0, sigma0=None, dual=True):
    """B(Phi) from both sides: (lower, upper, sigma, Y).

    `lower` is the objective of a feasible pair (rho, sigma), with rho from the inner SDP; `upper` is t_Y + g_Y for the
    best dual Y found, with g_Y bounded from above. Supergradient ascent on sigma; dual iterates are averaged. With
    dual=False only the primal ascent runs and `upper` is inf.
    """
    d = ch.d
    sig = np.eye(d, dtype=complex) / d if sigma0 is None else (1 - 1e-6) * herm(sigma0) + 1e-6 * np.eye(d) / d
    best_lo, best_up = -np.inf, np.inf
    best_sig, best_y = sig, None
    ysum, wsum = None, 0.0
    for it in range(iters):
        f, rho, y = inner_sdp(ch, sig)
        val, res, neg = primal_value(ch, sig, rho)
        if res < 1e-7 and neg > -1e-8 and val > best_lo:
            best_lo, best_sig = val, sig
        w = 1 / math.sqrt(it + 1)
        ysum = w * y if ysum is None else ysum + w * y
        wsum += w
        if dual and (it % 50 == 0 or it == iters - 1):
            for yc in (y, ysum / wsum):
                up, _, _ = dual_value(ch, yc, iters=4000, tol=1e-13)
                if up < best_up:
                    best_up, best_y = up, yc
        g = herm((-logm_h(sig) + ch.phistar(logm_h(ch.phi(sig)))) / ch.beta + ch.psistar(y))
        s = 0.5 / math.sqrt(it + 1)
        m = herm(logm_h(sig) + s * ch.beta * g)
        m -= np.max(np.linalg.eigvalsh(m)) * np.eye(d)
        sig = expm_h(m)
        sig /= np.trace(sig).real
        sig = (1 - 1e-12) * sig + 1e-12 * np.eye(d) / d
    return best_lo, best_up, best_sig, best_y


def _y_from(p, r):
    y = np.zeros((r, r), dtype=complex)
    idx = 0
    for i in range(r):
        y[i, i] = p[idx]
        idx += 1
    for i in range(r):
        for j in range(i + 1, r):
            y[i, j] = p[idx] + 1j * p[idx + 1]
            y[j, i] = p[idx] - 1j * p[idx + 1]
            idx += 2
    return y


def _p_from(y):
    r = y.shape[0]
    out = [np.real(y[i, i]) for i in range(r)]
    for i in range(r):
        for j in range(i + 1, r):
            out += [np.real(y[i, j]), np.imag(y[i, j])]
    return np.array(out)


def batch_cost_smooth(ch, y0=None, mus=(1e-2, 1e-3, 1e-4, 1e-5, 1e-6)):
    """B(Phi) from both sides by smoothed dual minimization: (lower, upper, sigma, Y).

    The dual function Y -> lambda_max(D - Psi^*Y) + g_Y is convex; lambda_max is replaced by the soft maximum
    mu ln Tr exp(M/mu), whose gradient is -Psi(rho_mu), while g_Y has gradient Psi(sigma_Y). After BFGS at decreasing mu
    the final Y gives the certified upper bound t_Y + g_Y, and sigma_Y with the inner SDP gives a feasible pair, hence
    a lower bound.
    """
    from scipy.optimize import minimize
    r = ch.r
    p0 = np.zeros(r * r) if y0 is None else _p_from(herm(y0))
    state = {"sig": None}

    def fun(p, mu):
        y = _y_from(p, r)
        py = herm(ch.psistar(y))
        m = herm(ch.D - py)
        w, v = np.linalg.eigh(m)
        wm = w.max()
        ex = np.exp((w - wm) / mu)
        lse = wm + mu * math.log(ex.sum())
        rho_mu = (v * (ex / ex.sum())) @ dag(v)
        glo, _, sig = gmax(ch, py, iters=4000, tol=1e-15, sigma0=state["sig"])
        state["sig"] = sig
        g = herm(ch.psi(sig) - ch.psi(rho_mu))
        grad = []
        for i in range(r):
            grad.append(np.real(g[i, i]))
        for i in range(r):
            for j in range(i + 1, r):
                grad += [2 * np.real(g[i, j]), 2 * np.imag(g[i, j])]
        return lse + glo, np.array(grad)

    p = p0
    for mu in mus:
        res = minimize(fun, p, args=(mu,), jac=True, method="BFGS", options={"gtol": 1e-9, "maxiter": 400})
        p = res.x
    y = _y_from(p, r)
    up, _, sig = dual_value(ch, y, iters=20000, tol=1e-16, sigma0=state["sig"])
    up0, _, _ = dual_value(ch, _y_from(p0, r), iters=20000, tol=1e-16)       # the starting point is also a certificate
    if up0 < up:
        up, y = up0, _y_from(p0, r)
    f, rho, _ = inner_sdp(ch, sig, dual=False)
    lo, res_, neg = primal_value(ch, sig, rho)
    if res_ > 1e-7 or neg < -1e-8:
        lo = -np.inf
    if up - lo > 1e-7:
        # a degenerate maximizer of g_Y need not be primal optimal: improve the lower bound by primal ascent
        lo2, _, sig2, _ = batch_cost(ch, iters=200, sigma0=sig, dual=False)
        if lo2 > lo:
            lo, sig = lo2, sig2
    return lo, up, sig, y


def diamond_half(choi_a, choi_b, din, dout):
    """Half diamond distance between two channels given by their Choi matrices (input first), by Watrous's SDP."""
    import cvxpy as cp
    j = herm(choi_a - choi_b)
    w = cp.Variable((din * dout, din * dout), hermitian=True)
    rho = cp.Variable((din, din), hermitian=True)
    cons = [w >> 0, cp.kron(rho, np.eye(dout)) - w >> 0, rho >> 0, cp.real(cp.trace(rho)) == 1]
    prob = cp.Problem(cp.Maximize(cp.real(cp.trace(j @ w))), cons)
    prob.solve(solver="CLARABEL")
    return float(prob.value)


def choi_of(fn, din):
    """Choi matrix sum_{ij} |i><j| (x) fn(|i><j|) of a linear map given as a function."""
    out = None
    for i in range(din):
        for k in range(din):
            e = np.zeros((din, din), dtype=complex)
            e[i, k] = 1
            blk = np.kron(e, fn(e))
            out = blk if out is None else out + blk
    return out
