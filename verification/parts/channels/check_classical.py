"""Classical channels pay no surcharge (Theorems 4.2(a) and G.2, Appendix G.3, "Classical channels").

Checks:
  1. Lemma "Coherence is free": a flat register J and the controlled phases Z^j make the input marginal diag(rho); the
     new dilation implements Phi exactly and f_{U'}(rho) <= f_U(diag rho) (random classical channels and dilations);
  2. Lemma "A nearly flat bath", exactly (rationals): a_r <= mu_N(r) for r <= N and sum_{r > N} a_r <= (1 + ln k)/ln N,
     with equality in the first for point masses;
  3. the diagonal-input construction for random stochastic matrices (d = 2, 3): a seed R with at most d^2 values (from
     the merged cumulative breakpoints) and a function f give Y = f(X, R) with law exactly P(.|X); fibres have at most
     d^3 elements; the ranking permutation is injective, f_U(p) = H(p) - H(Pp) + I(Y:B') exactly, and
     I(Y:B') <= g_d((1 + 3 ln d)/ln N), decreasing in N;
  4. all inputs: Phi(rho) = Phi(diag rho), the energy term depends only on diag rho, and the batch maximand at rho is at
     most its value at diag rho, so the supremum may be taken over diagonal inputs;
  5. the attainment remark: unital P is a mixture of permutations (Birkhoff, computed) and the controlled unitary
     leaves the bath marginal unchanged, f_U = 0; for deterministic P the index dilation has f_U <= log2 max fibre
     = T_cap; for P(0|0) = 1, P(0|1) = a the batch-optimal input has full rank;
  6. coherent inputs: the correlation term of a classical channel need not vanish there. Complete qubit dephasing at
     (I + 0.6X)/2 has m_rho = S(Delta rho) - S(rho) = 1 - h2(0.8) for every exact dilation (controlled Z attains it,
     random exact dilations never go below), while m_p = 0 on diagonal inputs, which set both optimized rates.
"""
from fractions import Fraction
import itertools
import math

import numpy as np
from scipy.optimize import linprog, minimize

from qtools import Report, dm, entropy, g_afw, h2, kraus_apply, ptrace, random_density, random_unitary, shannon

R = Report("Classical channels")
rng = np.random.default_rng(20261020)


def classical_kraus(P):
    d = P.shape[0]
    return [math.sqrt(P[y, x]) * np.outer(np.eye(d)[y], np.eye(d)[x]) for x in range(d) for y in range(d) if P[y, x] > 0]


def random_stochastic(d, rng, sparse=False):
    P = rng.dirichlet(np.ones(d), size=d).T            # columns P(.|x)
    if sparse:
        P = np.where(rng.random((d, d)) < 0.4, 0, P) + 1e-9
        P /= P.sum(axis=0)
    return P


# ---------------------------------------------------------------------------------------------------- 1. dephase
ok_marg, ok_impl, ok_ineq = True, True, True
for trial in range(200):
    d, dB = int(rng.integers(2, 4)), int(rng.integers(2, 4))
    P = random_stochastic(d, rng)
    # a dilation U of Phi on diagonal inputs: classical dilation via seeds (permutation) or a random dilation of
    # the dephased channel
    U = random_unitary(d * dB, rng)
    tau = random_density(dB, rng)
    Zd = np.diag(np.exp(2j * math.pi * np.arange(d) / d))
    # U' = (U x I_J) (sum_j Z^j x |j><j|_J), bath B (x) J with J flat
    ctrl = sum(np.kron(np.kron(np.linalg.matrix_power(Zd, j), np.eye(dB)), dm(np.eye(d)[j])) for j in range(d))
    Up = np.kron(U, np.eye(d)) @ ctrl
    tauJ = np.kron(tau, np.eye(d) / d)
    rho = random_density(d, rng)
    out = Up @ np.kron(rho, tauJ) @ Up.conj().T
    dims = [d, dB, d]
    # the input marginal after the phases is diag(rho): compare with U on diag(rho)
    outdiag = U @ np.kron(np.diag(np.diag(rho)), tau) @ U.conj().T
    ok_impl &= np.allclose(ptrace(out, dims, [0]), ptrace(outdiag, [d, dB], [0]), atol=1e-12)
    ok_marg &= np.allclose(ptrace(out, dims, [1]), ptrace(outdiag, [d, dB], [1]), atol=1e-12)
    fUp = entropy(ptrace(out, dims, [1, 2])) - entropy(tauJ)
    fU = entropy(ptrace(outdiag, [d, dB], [1])) - entropy(tau)
    ok_ineq &= fUp <= fU + 1e-10
R.check("controlled phases from a flat register make the input diag(rho): output and bath output are those of U on "
        "diag(rho) (200 random)", bool(ok_impl and ok_marg))
R.check("f_{U'}(rho) <= f_U(diag rho) (subadditivity, the register's entropy cancels)", bool(ok_ineq))


# ---------------------------------------------------------------------------------------------------- 2. log-uniform
def loguniform_check(N, w):
    HN = sum(Fraction(1, l) for l in range(1, N + 1))
    mu = [Fraction(1, l) / HN for l in range(1, N + 1)]
    prods = sorted((m * ws for m in mu for ws in w if ws > 0), reverse=True)
    first = all(prods[r] <= mu[r] for r in range(min(N, len(prods))))
    tail = sum(prods[N:], Fraction(0))
    k = len(w)
    return first, float(tail), (1 + math.log(k)) / math.log(N), prods, mu


ok1, ok2, eq_pm = True, True, True
ratio = 0.0
for trial in range(150):
    N = int(rng.choice([2, 5, 10, 40, 100]))
    k = int(rng.integers(1, 7))
    if trial % 10 == 0:
        w = [Fraction(1)] + [Fraction(0)] * (k - 1)
    elif trial % 10 == 1:
        w = [Fraction(1, k)] * k
    else:
        raw = [int(x) for x in rng.integers(1, 30, k)]
        w = [Fraction(x, sum(raw)) for x in raw]
    first, tail, bnd, prods, mu = loguniform_check(N, w)
    ok1 &= first
    ok2 &= tail <= bnd + 1e-15
    ratio = max(ratio, tail / bnd)
    if trial % 10 == 0:
        eq_pm &= all(prods[r] == mu[r] for r in range(N))
R.check("Lemma: a_r <= mu_N(r) for r <= N (exact rationals; equality for point masses)", bool(ok1 and eq_pm))
R.check("Lemma: sum_{r > N} a_r <= (1 + ln k)/ln N", bool(ok2), f"largest ratio {ratio:.3f}")


# ---------------------------------------------------------------------------------------------------- 3. construction
def seed_function(P):
    """R uniform-interval seed from the merged cumulative breakpoints of the columns P(.|x) (exact rationals)."""
    d = len(P)
    cuts = {Fraction(0), Fraction(1)}
    for x in range(d):
        c = Fraction(0)
        for y in range(d - 1):
            c += P[y][x]
            cuts.add(c)
    cuts = sorted(cuts)
    lengths = [b - a for a, b in zip(cuts, cuts[1:]) if b > a]
    mids = [(a + b) / 2 for a, b in zip(cuts, cuts[1:]) if b > a]

    def f(x, r):
        c = Fraction(0)
        for y in range(d):
            c += P[y][x]
            if mids[r] < c:
                return y
        return d - 1
    return lengths, f


ok_seed, ok_fib, ok_perm, ok_id, ok_mi = True, True, True, True, True
mi_trend = []
for trial in range(12):
    d = 2 + trial % 2
    raw = rng.integers(0, 6, (d, d)) + (rng.random((d, d)) < 0.7)
    raw[0, :] += 1
    P = [[Fraction(int(raw[y, x]), int(raw[:, x].sum())) for x in range(d)] for y in range(d)]
    lengths, f = seed_function(P)
    ok_seed &= len(lengths) <= d * d
    for x in range(d):
        for y in range(d):
            ok_seed &= sum((lengths[r] for r in range(len(lengths)) if f(x, r) == y), Fraction(0)) == P[y][x]
    rawp = rng.integers(1, 6, d)
    p = [Fraction(int(v), int(rawp.sum())) for v in rawp]
    fib = {y: [(x, r) for x in range(d) for r in range(len(lengths)) if f(x, r) == y and p[x] * lengths[r] > 0]
           for y in range(d)}
    ok_fib &= all(len(v) <= d ** 3 for v in fib.values())
    Py = {y: sum((p[x] * lengths[r] for (x, r) in fib[y]), Fraction(0)) for y in range(d)}
    prev = None
    for N in (10, 100, 1000):
        HN = sum(1.0 / l for l in range(1, N + 1))
        mu = [1.0 / (l * HN) for l in range(1, N + 1)]
        # ranking within each fibre: label b = rank of mu(l) w_y(x, r)
        images = set()
        joint = {}
        for y in range(d):
            if Py[y] == 0:
                continue
            items = sorted(((mu[l] * float(p[x] * lengths[r] / Py[y]), (x, r, l)) for (x, r) in fib[y] for l in range(N)),
                           reverse=True)
            for b, (val, lab) in enumerate(items):
                images.add((y, b))
                joint[(y, b)] = float(Py[y]) * val
        ok_perm &= len(images) == sum(len(fib[y]) * N for y in range(d) if Py[y] > 0)
        pY = np.array([float(Py[y]) for y in range(d)])
        maxb = max(b for (_, b) in joint) + 1
        J = np.zeros((d, maxb))
        for (y, b), v in joint.items():
            J[y, b] = v
        pB = J.sum(axis=0)
        I = shannon(pY) + shannon(pB) - shannon(J.reshape(-1))
        Hp = shannon([float(v) for v in p])
        PP = np.array([[float(P[y][x]) for x in range(d)] for y in range(d)])
        HPp = shannon(PP @ np.array([float(v) for v in p]))
        Hseed = shannon([float(v) for v in lengths]) + shannon(mu)
        fU = shannon(pB) - Hseed
        ok_id &= abs(fU - (Hp - HPp + I)) < 1e-9
        bound = g_afw(d, min(1.0, (1 + 3 * math.log(d)) / math.log(N)))
        ok_mi &= I <= bound + 1e-12
        if prev is not None:
            ok_mi &= I <= prev + 1e-12
        prev = I
    mi_trend.append(prev)
R.check("the merged-breakpoint seed has at most d^2 values and Y = f(X, R) has law exactly P(.|X) (exact)", bool(ok_seed))
R.check("fibres have at most d^3 elements and the ranking map (x, r, l) -> (y, b) is injective", bool(ok_fib and ok_perm))
R.check("f_U(p) = H(p) - H(Pp) + I(Y:B') exactly, I(Y:B') <= g_d((1 + 3 ln d)/ln N) and decreases with N",
        bool(ok_id and ok_mi), f"I(Y:B') at N = 1000: max {max(mi_trend):.4f}")

# ---------------------------------------------------------------------------------------------------- 4. all inputs
ok = True
for _ in range(300):
    d = int(rng.integers(2, 4))
    P = random_stochastic(d, rng)
    K = classical_kraus(P)
    H = np.diag(np.sort(rng.uniform(0, 2, d)))
    beta = rng.uniform(0.1, 3)
    rho = random_density(d, rng)
    dg = np.diag(np.diag(rho))
    ok &= np.allclose(kraus_apply(K, rho), kraus_apply(K, dg), atol=1e-12)
    e1 = np.trace(H @ (kraus_apply(K, rho) - rho)).real
    e2 = np.trace(H @ (kraus_apply(K, dg) - dg)).real
    ok &= abs(e1 - e2) < 1e-12
    val = lambda r: entropy(r) - entropy(kraus_apply(K, r)) + beta / math.log(2) * np.trace(H @ (kraus_apply(K, r) - r)).real
    ok &= val(rho) <= val(dg) + 1e-12
R.check("Phi(rho) = Phi(diag rho), the energy term depends only on diag rho, and the batch maximand at rho is at most "
        "its value at diag rho", bool(ok))


# ---------------------------------------------------------------------------------------------------- 5. attainment
def birkhoff(P, tol=1e-12):
    """Greedy Birkhoff decomposition of a doubly stochastic matrix (perfect matchings on the positive support)."""
    P = P.copy()
    d = P.shape[0]
    terms = []
    while P.max() > tol:
        best = None
        for perm in itertools.permutations(range(d)):
            m = min(P[perm[x], x] for x in range(d))
            if m > tol and (best is None or m > best[0]):
                best = (m, perm)
        if best is None:
            break
        m, perm = best
        terms.append((m, perm))
        for x in range(d):
            P[perm[x], x] -= m
    return terms


ok_b, ok_f0 = True, True
for _ in range(30):
    d = 3
    perms = list(itertools.permutations(range(d)))
    wts = rng.dirichlet(np.ones(len(perms)))
    P = sum(w * np.eye(d)[list(pm)].T for w, pm in zip(wts, perms))
    terms = birkhoff(P)
    rec = sum(m * np.eye(d)[list(pm)].T for m, pm in terms)
    ok_b &= np.allclose(rec, P, atol=1e-10) and abs(sum(m for m, _ in terms) - 1) < 1e-10
    # controlled unitary: bath register over (k, j) with weights lambda_k / d, unitary Pi_k Z^j
    Zd = np.diag(np.exp(2j * math.pi * np.arange(d) / d))
    units = [(m / d, np.eye(d)[list(pm)].T @ np.linalg.matrix_power(Zd, j)) for m, pm in terms for j in range(d)]
    nb = len(units)
    Uc = sum(np.kron(Uk, dm(np.eye(nb)[i])) for i, (_, Uk) in enumerate(units))
    tau = np.diag([w for w, _ in units])
    rho = random_density(d, rng)
    out = Uc @ np.kron(rho, tau) @ Uc.conj().T
    ok_f0 &= np.allclose(ptrace(out, [d, nb], [1]), tau, atol=1e-12)
    ok_f0 &= np.allclose(ptrace(out, [d, nb], [0]), kraus_apply(classical_kraus(P), rho), atol=1e-10)
R.check("unital P: a computed Birkhoff decomposition reproduces P, and the controlled unitary Pi_k Z^j implements Phi "
        "with an unchanged bath marginal, so f_U = 0 = T_cap", bool(ok_b and ok_f0))
ok = True
for _ in range(30):
    d = int(rng.integers(2, 5))
    fmap = rng.integers(0, d, d)
    P = np.zeros((d, d))
    P[fmap, np.arange(d)] = 1
    maxfib = max(np.sum(fmap == y) for y in range(d))
    best = max(shannon(p) - shannon(P @ p) for p in rng.dirichlet(np.ones(d) * 0.5, 3000))
    # uniform on the largest fibre attains log2 max fibre
    y0 = int(np.argmax([np.sum(fmap == y) for y in range(d)]))
    pu = (fmap == y0) / maxfib
    ok &= best <= math.log2(maxfib) + 1e-12 and abs(shannon(pu) - shannon(P @ pu) - math.log2(maxfib)) < 1e-12
    # the index dilation: bath output = index of x in its fibre (entropy <= log2 max fibre)
    idx = np.array([np.sum(fmap[:x] == fmap[x]) for x in range(d)])
    for p in rng.dirichlet(np.ones(d), 20):
        lawB = np.bincount(idx, weights=p, minlength=maxfib)
        ok &= shannon(lawB) <= math.log2(maxfib) + 1e-12
R.check("deterministic P: T_cap = log2 max fibre and the index dilation has f_U <= log2 max fibre", bool(ok))
ok = True
for a in (0.1, 0.5, 0.9):
    P = np.array([[1, a], [0, 1 - a]])
    res = minimize(lambda v: -(h2(v[0]) - h2(v[0] * (1 - a))), [0.3], bounds=[(1e-9, 1 - 1e-9)])
    ok &= 1e-3 < res.x[0] < 1 - 1e-3 and -res.fun > 0
R.check("P(0|0) = 1, P(0|1) = a: the batch-optimal input has full rank and T_cap > 0", bool(ok))


# ---------------------------------------------------------------------------------------------------- 6. coherent inputs
# Complete dephasing of a qubit, H = 0. Exact dilations act as |i>|v> -> |i> V_i|v> on supp(tau), with
# Tr(V_1^* V_0 tau) = 0 for exactness on coherent inputs; the bath ends in sum_i rho_ii V_i tau V_i^*, so s_rho >= 0
# and m_rho = S(Delta rho) - S(rho), positive on coherent inputs. Random exact dilations: V_1 = V_0 M^*, with
# M = G diag(e^{2 pi i j/k}) G^* and G a Fourier basis of tau's eigenbasis (random phases), so Tr(M tau) = 0 exactly.
def controlled_pair(V0, V1):
    return np.kron(dm([1, 0]), V0) + np.kron(dm([0, 1]), V1)


def mutual_out_bath(joint, k):
    return entropy(ptrace(joint, [2, k], [0])) + entropy(ptrace(joint, [2, k], [1])) - entropy(joint)


Xq = np.array([[0, 1], [1, 0]], dtype=complex)
rho = (np.eye(2) + 0.6 * Xq) / 2
deph = np.diag(np.diag(rho))
bound = entropy(deph) - entropy(rho)
CZ = controlled_pair(np.eye(2), np.diag([1, -1]))
out = CZ @ np.kron(rho, np.eye(2) / 2) @ CZ.conj().T
ok_cz = (np.allclose(ptrace(out, [2, 2], [0]), deph, atol=1e-12)
         and abs(entropy(ptrace(out, [2, 2], [1])) - 1) < 1e-12
         and abs(mutual_out_bath(out, 2) - bound) < 1e-12 and abs(bound - (1 - h2(0.8))) < 1e-12)
worst = math.inf
for _ in range(400):
    k = int(rng.integers(2, 6))
    Wb = random_unitary(k, rng)
    tau = Wb @ np.diag(rng.dirichlet(np.ones(k))) @ Wb.conj().T
    Fk = np.exp(2j * math.pi * np.outer(np.arange(k), np.arange(k)) / k) / math.sqrt(k)
    G = Wb @ Fk @ np.diag(np.exp(2j * math.pi * rng.random(k)))
    M = G @ np.diag(np.exp(2j * math.pi * np.arange(k) / k)) @ G.conj().T
    V0 = random_unitary(k, rng)
    U = controlled_pair(V0, V0 @ M.conj().T)
    out = U @ np.kron(rho, tau) @ U.conj().T
    ok_cz &= np.allclose(ptrace(out, [2, k], [0]), deph, atol=1e-10)
    worst = min(worst, mutual_out_bath(out, k) - bound)
pdiag = np.diag([0.8, 0.2])
out = CZ @ np.kron(pdiag, np.eye(2) / 2) @ CZ.conj().T
ok_diag = abs(mutual_out_bath(out, 2)) < 1e-12
R.check("coherent inputs: complete dephasing of (I + 0.6X)/2 has m_rho = 1 - h2(0.8) > 0 (controlled Z attains it; "
        "400 random exact dilations never go below), while m_p = 0 on the diagonal input (0.8, 0.2)",
        bool(ok_cz and worst > -1e-9 and ok_diag), f"m_rho = {bound:.10f}, min excess {worst:.1e}")
R.close()
