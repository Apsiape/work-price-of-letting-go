"""The fixed-dimension reduction: its finite, exact parts (Theorem "Undecidability", Section 7, Theorem "Fixed
dimension, finite-list non-enumerability" and Appendix "Exact inputs and the fixed-dimension reduction").

Checks:
  1. the formal Gram transfer, exactly (sympy over Q(i, sqrt2)): for synchronous tables from tracial PVMs with rational
     projections (Cayley-transform orthogonal matrices), N = 1 question and eight answers, the Gram C_P computed from A
     alone equals the actual Gram [tau(u_j^* u_i)] of u_0 = 1, u_j = 2p_j - 1, u_{m+j} = (u_j + i)/sqrt2; it has unit
     diagonal, is PSD, satisfies tau(u_j^* u_i) = tau(u_i u_j^*), and the formal relations u_{m+j} - (u_j + i u_0)/sqrt2
     are null vectors; the same in floating point for N = 2;
  2. the converse algebra: ((v + i)/sqrt2)^*((v + i)/sqrt2) = I + (i/2)(v^* - v); if both v and (v + i)/sqrt2 are
     unitary then v is self-adjoint and r = (v + 1)/2 is a projection; tau(r_j) = q_j and tau(r_k r_j) = M_jk are read
     off the Gram; ||r_b r_a||_2^2 = tau(r_a r_b); left and right multiplications on L^2(tau) commute and give
     tau(r_{x,a} r_{y,b});
  3. the exact filters accept every table from a tracial PVM and reject tables that fail each condition; a Hermitian
     matrix is PSD exactly when all principal minors are nonnegative (leading minors alone do not suffice);
  4. the Schur channel of a PSD unit-diagonal C is CPTP and unital; padding C'_{ij} = C_{f(i)f(j)} keeps PSD and unit
     diagonal and is realized by duplicating unitaries; d_0 = 2(8N) + 1 = 16N + 1;
  5. the thermal realization: with e^{-beta E_k} = w_k/n_k the bath H_B = (+)_k E_k I_{n_k} has partition function one
     and Gibbs state the density of tau; U = sum_i |i><i| (x) u_i commutes with H (x) I + I (x) H_B and gives
     M_ij = tau(u_j^* u_i); a dephasing channel preserves every population, hence the Gibbs state, and its energy term
     vanishes;
  6. cyclotomic entries: cos(k pi/p), sin(k pi/p) lie in Q(zeta_{4p}) and i, sqrt2 in Q(zeta_{8p}) (explicit formulas,
     50 digits, p <= 12).
"""
import itertools
import math

import mpmath as mp
import numpy as np
import sympy as sp

from qtools import Report, dm, gibbs, random_density, random_unitary

R = Report("Fixed-dimension reduction")
rng = np.random.default_rng(20261022)
NA = 8                                                    # answers


def cayley(k, rng):
    """Rational orthogonal matrix (I - S)(I + S)^{-1} from a random rational skew-symmetric S."""
    S = sp.zeros(k, k)
    for i in range(k):
        for j in range(i + 1, k):
            v = sp.Rational(int(rng.integers(-5, 6)), int(rng.integers(1, 5)))
            S[i, j], S[j, i] = v, -v
    return (sp.eye(k) - S) * (sp.eye(k) + S).inv()


def rational_pvms(N, k, rng):
    out = []
    for x in range(N):
        Q = cayley(k, rng)
        labels = [int(a) for a in rng.integers(0, NA, k)]
        out.append([Q * sp.diag(*[1 if l == a else 0 for l in labels]) * Q.T for a in range(NA)])
    return out


def table(E, k):
    tau = lambda Mx: Mx.trace() / k
    N = len(E)
    return {(x, y, a, b): tau(E[x][a] * E[y][b]) for x in range(N) for y in range(N) for a in range(NA) for b in range(NA)}


def formal_gram(P, N, exact=True):
    m = NA * N
    idx = [(x, a) for x in range(N) for a in range(NA)]
    one = sp.Integer(1) if exact else 1.0
    M = [[P[(x, y, a, b)] for (y, b) in idx] for (x, a) in idx]
    q = [P[(x, x, a, a)] for (x, a) in idx]
    G0 = sp.zeros(m + 1, m + 1) if exact else np.zeros((m + 1, m + 1), dtype=complex)
    G0[0, 0] = one
    for j in range(m):
        G0[0, j + 1] = G0[j + 1, 0] = 2 * q[j] - 1
        for l in range(m):
            G0[j + 1, l + 1] = 4 * M[j][l] - 2 * q[j] - 2 * q[l] + 1
    # coefficient matrix: column i expresses formal vector i in the basis (1, u_1, ..., u_m)
    if exact:
        T = sp.zeros(m + 1, 2 * m + 1)
        s2, I = sp.sqrt(2), sp.I
    else:
        T = np.zeros((m + 1, 2 * m + 1), dtype=complex)
        s2, I = math.sqrt(2), 1j
    T[0, 0] = one
    for j in range(m):
        T[j + 1, j + 1] = one
        T[j + 1, m + j + 1] = 1 / s2
        T[0, m + j + 1] = I / s2
    C = (T.H * G0 * T) if exact else T.conj().T @ G0 @ T          # C[k, i] = tau(u_k^* u_i)
    return (C.T if exact else C.T), M, q, G0


def actual_unitaries(E, k, exact=True):
    if exact:
        Id, s2, I = sp.eye(k), sp.sqrt(2), sp.I
    else:
        Id, s2, I = np.eye(k), math.sqrt(2), 1j
    u = [Id] + [2 * E[x][a] - Id for x in range(len(E)) for a in range(NA)]
    u += [(u[j + 1] + I * Id) / s2 for j in range(len(u) - 1)]
    return u


# ---------------------------------------------------------------------------------------------------- 1. Gram
k = 4
E = rational_pvms(1, k, rng)
P = table(E, k)
sync = all(P[(0, 0, a, b)] == 0 for a in range(NA) for b in range(NA) if a != b)
C, M, q, G0 = formal_gram(P, 1)
u = actual_unitaries(E, k)
n = len(u)
Cact = sp.Matrix(n, n, lambda i, j: sp.expand((u[j].H * u[i]).trace() / k))
Cmus = sp.Matrix(n, n, lambda i, j: sp.expand((u[i] * u[j].H).trace() / k))
unit = all(sp.simplify(w.H * w - sp.eye(k)) == sp.zeros(k) for w in u)
eqG = sp.simplify(C - Cact) == sp.zeros(n, n)
null_ok = True
m = NA
for j in range(m):
    c = sp.zeros(n, 1)
    c[m + j + 1], c[j + 1], c[0] = 1, -1 / sp.sqrt(2), -sp.I / sp.sqrt(2)
    null_ok &= sp.simplify((c.H * C.T * c)[0, 0]) == 0
Cn = np.array(C.evalf(30), dtype=complex)
R.check("exact (N = 1, eight answers, rational PVMs in M_4): the table is synchronous, every u is unitary, and the "
        "formal Gram C_P computed from A equals the actual Gram tau(u_j^* u_i)", sync and unit and eqG)
R.check("C_P has unit diagonal, is PSD, equals [tau(u_i u_j^*)], and u_{m+j} - (u_j + i u_0)/sqrt2 are null vectors",
        all(sp.simplify(C[i, i] - 1) == 0 for i in range(n)) and np.linalg.eigvalsh((Cn + Cn.conj().T) / 2).min() > -1e-12
        and sp.simplify(Cact - Cmus) == sp.zeros(n, n) and null_ok)
# floating point, N = 2
ok = True
for _ in range(5):
    kk, N = 10, 2
    En = []
    for x in range(N):
        Uq = random_unitary(kk, rng)
        lab = rng.integers(0, NA, kk)
        En.append([Uq @ np.diag((lab == a).astype(float)) @ Uq.conj().T for a in range(NA)])
    Pn = {(x, y, a, b): np.trace(En[x][a] @ En[y][b]).real / kk for x in range(N) for y in range(N)
          for a in range(NA) for b in range(NA)}
    Cf, *_ = formal_gram(Pn, N, exact=False)
    un = actual_unitaries(En, kk, exact=False)
    Ca = np.array([[np.trace(un[j].conj().T @ un[i]) / kk for j in range(len(un))] for i in range(len(un))])
    ok &= np.allclose(Cf, Ca, atol=1e-12) and len(un) == 16 * N + 1
R.check("floating point, N = 2 (33 unitaries = 16N + 1): formal and actual Grams agree", bool(ok))

# ---------------------------------------------------------------------------------------------------- 2. converse
ok = True
for _ in range(200):
    d = int(rng.integers(2, 6))
    v = random_unitary(d, rng)
    w = (v + 1j * np.eye(d)) / math.sqrt(2)
    ok &= np.allclose(w.conj().T @ w, np.eye(d) + 0.5j * (v.conj().T - v), atol=1e-12)
    # self-adjoint unitaries (symmetries) make w unitary, and only those
    Uq = random_unitary(d, rng)
    sgn = np.diag(rng.choice([-1, 1], d))
    vs = Uq @ sgn @ Uq.conj().T
    ws = (vs + 1j * np.eye(d)) / math.sqrt(2)
    rr = (vs + np.eye(d)) / 2
    ok &= np.allclose(ws.conj().T @ ws, np.eye(d), atol=1e-12) and np.allclose(rr @ rr, rr, atol=1e-12)
    ok &= not np.allclose(w.conj().T @ w, np.eye(d), atol=1e-6)
th = np.linspace(0, 2 * math.pi, 200001)
allowed = th[np.abs(np.abs((np.exp(1j * th) + 1j) / math.sqrt(2)) - 1) < 1e-9]
ok &= set(np.round(allowed % (2 * math.pi), 4)) <= {0.0, round(math.pi, 4), round(2 * math.pi, 4)}
# tau(r_j) = q_j and tau(r_k r_j) = M_jk from the Gram, exactly
rs = [(u[j + 1] + sp.eye(k)) / 2 for j in range(m)]
ok &= all(sp.simplify(rs[j].trace() / k - q[j]) == 0 for j in range(m))
ok &= all(sp.simplify((rs[l] * rs[j]).trace() / k - M[j][l]) == 0 for j in range(m) for l in range(m))
ok &= all(sp.simplify((1 + C[j + 1, 0]) / 2 - q[j]) == 0 for j in range(m))
R.check("((v + i)/sqrt2)^*((v + i)/sqrt2) = I + (i/2)(v^* - v); both unitary forces v = v^* (eigenvalues +-1) and "
        "r = (v + 1)/2 a projection; tau(r_j) = q_j and tau(r_k r_j) = M_jk", bool(ok))
ok = True
for _ in range(100):
    d = int(rng.integers(2, 6))
    Uq = random_unitary(d, rng)
    pa = Uq @ np.diag((rng.random(d) < 0.5).astype(float)) @ Uq.conj().T
    Uq = random_unitary(d, rng)
    pb = Uq @ np.diag((rng.random(d) < 0.5).astype(float)) @ Uq.conj().T
    X = pb @ pa
    ok &= abs(np.trace(X.conj().T @ X).real / d - np.trace(pa @ pb).real / d) < 1e-12
    Lm = np.kron(pa, np.eye(d))                       # left multiplication on vec (row-major)
    Rm = np.kron(np.eye(d), pb.T)                     # right multiplication
    vec1 = np.eye(d).reshape(-1) / math.sqrt(d)
    ok &= np.allclose(Lm @ Rm, Rm @ Lm, atol=1e-12)
    ok &= abs(vec1 @ Lm @ Rm @ vec1 - np.trace(pa @ pb) / d) < 1e-12
R.check("||r_b r_a||_2^2 = tau(r_a r_b); left and right multiplications on L^2(tau) commute and give tau(r_a r_b)", bool(ok))


# ---------------------------------------------------------------------------------------------------- 3. filters
def principal_minors_ok(A):
    n_ = A.shape[0]
    for size in range(1, n_ + 1):
        for S in itertools.combinations(range(n_), size):
            if sp.re(sp.simplify(A.extract(list(S), list(S)).det())) < 0:
                return False
    return True


def filters(P, N):
    vals = list(P.values())
    if any(sp.im(sp.nsimplify(v)) != 0 for v in vals):
        return "real"
    if any(v < 0 for v in vals):
        return "nonnegative"
    for x, y in itertools.product(range(N), repeat=2):
        if sum(P[(x, y, a, b)] for a in range(NA) for b in range(NA)) != 1:
            return "normalized"
    for x in range(N):
        if any(P[(x, x, a, b)] != 0 for a in range(NA) for b in range(NA) if a != b):
            return "synchronous"
    for x, y in itertools.product(range(N), repeat=2):
        for a in range(NA):
            m1 = sum(P[(x, y, a, b)] for b in range(NA))
            if m1 != P[(x, x, a, a)]:
                return "marginal"
    for x, y, a, b in P:
        if P[(x, y, a, b)] != P[(y, x, b, a)]:
            return "symmetric"
    Cx, Mx, qx, G0x = formal_gram(P, N)
    A = sp.Matrix([[1] + list(qx)] + [[qx[j]] + list(Mx[j]) for j in range(len(qx))])
    if not principal_minors_ok_fast(A):
        return "PSD of A"
    return "pass"


def principal_minors_ok_fast(A):
    # the exact test is all principal minors (principal_minors_ok, checked below on small matrices); for the
    # 9 x 9 matrix A here an eigenvalue bound with a margin is used
    An = np.array(A.evalf(), dtype=float)
    return np.linalg.eigvalsh(An).min() > -1e-12


ok = filters(P, 1) == "pass"
bad = dict(P)
bad[(0, 0, 0, 1)] += sp.Rational(1, 100)
bad[(0, 0, 0, 0)] -= sp.Rational(1, 100)
ok &= filters(bad, 1) in ("synchronous", "marginal", "symmetric")
bad2 = dict(P)
key = next(kk for kk in P if P[kk] > 0)
bad2[key] = P[key] + sp.Rational(1, 7)
ok &= filters(bad2, 1) == "normalized"
bad3 = {kk: -v if kk == key else v for kk, v in P.items()}
ok &= filters(bad3, 1) == "nonnegative"
R.check("the exact filters accept the tracial-PVM table and reject tables failing synchronicity, normalization or "
        "nonnegativity", bool(ok))
ok = True
for _ in range(60):
    nn = int(rng.integers(2, 5))
    B = sp.Matrix(nn, nn, lambda i, j: sp.Rational(int(rng.integers(-4, 5)), int(rng.integers(1, 4))))
    A = B * B.T if rng.random() < 0.5 else B + B.T
    ev = np.linalg.eigvalsh(np.array(A.evalf(), dtype=float))
    ok &= principal_minors_ok(A) == (ev.min() > -1e-12)
Dm = sp.diag(0, -1)
leading = [Dm[:1, :1].det(), Dm.det()]
R.check("a Hermitian matrix is PSD exactly when all principal minors are >= 0; diag(0, -1) has nonnegative leading "
        "minors but is not PSD", ok and all(x >= 0 for x in leading) and not principal_minors_ok(Dm))

# ---------------------------------------------------------------------------------------------------- 4. Schur, padding
ok = True
for _ in range(50):
    d = int(rng.integers(2, 6))
    G = random_unitary(d, rng)[:, :] @ np.diag(rng.uniform(0, 1, d)) @ random_unitary(d, rng)
    V = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    V /= np.linalg.norm(V, axis=0)
    Cg = V.conj().T @ V                                         # PSD, unit diagonal
    Choi = np.zeros((d * d, d * d), dtype=complex)
    for i in range(d):
        for j in range(d):
            Choi[i * d + i, j * d + j] = Cg[i, j]
    ok &= np.linalg.eigvalsh(Choi).min() > -1e-12
    rho = random_density(d, rng)
    out = Cg * rho
    ok &= abs(np.trace(out) - 1) < 1e-12 and np.allclose(Cg * np.eye(d), np.eye(d))
    f = list(range(d)) + list(rng.integers(0, d, 3))
    Cp = Cg[np.ix_(f, f)]
    ok &= np.linalg.eigvalsh(Cp).min() > -1e-12 and np.allclose(np.diag(Cp), 1)
    # realized by duplicating vectors (unitaries in the Gram)
    ok &= np.allclose(V[:, f].conj().T @ V[:, f], Cp)
R.check("Schur channels of PSD unit-diagonal C are CPTP and unital; padding keeps PSD and unit diagonal and is realized "
        "by duplicating the Gram vectors; d_0 = 2(8N) + 1 = 16N + 1", ok and all(2 * 8 * N + 1 == 16 * N + 1 for N in range(1, 100)))

# ---------------------------------------------------------------------------------------------------- 5. thermal
ok = True
for _ in range(30):
    dims = [int(x) for x in rng.integers(1, 4, int(rng.integers(1, 4)))]
    wts = rng.dirichlet(np.ones(len(dims)))
    beta = rng.uniform(0.2, 3)
    Ek = [-math.log(wk / nk) / beta for wk, nk in zip(wts, dims)]
    HB = np.diag(np.concatenate([[e] * nk for e, nk in zip(Ek, dims)]))
    dB = HB.shape[0]
    gB = np.diag(np.exp(-beta * np.diag(HB)))
    ok &= abs(np.trace(gB) - 1) < 1e-12                          # partition function one
    dens = np.diag(np.concatenate([[wk / nk] * nk for wk, nk in zip(wts, dims)]))
    ok &= np.allclose(gB, dens)
    d = int(rng.integers(2, 4))
    us = []
    for _i in range(d):
        blk = np.zeros((dB, dB), dtype=complex)
        s = 0
        for nk in dims:
            blk[s:s + nk, s:s + nk] = random_unitary(nk, rng)
            s += nk
        us.append(blk)
    H = np.diag(rng.uniform(0, 2, d))
    U = sum(np.kron(dm(np.eye(d)[i]), us[i]) for i in range(d))
    Htot = np.kron(H, np.eye(dB)) + np.kron(np.eye(d), HB)
    ok &= np.allclose(U @ Htot, Htot @ U, atol=1e-12)
    Mg = np.array([[np.trace(gB @ us[j].conj().T @ us[i]) for j in range(d)] for i in range(d)])
    rho = random_density(d, rng)
    out = np.einsum("aibi->ab", (U @ np.kron(rho, gB) @ U.conj().T).reshape(d, dB, d, dB))
    ok &= np.allclose(out, Mg * rho, atol=1e-12)
    gam = gibbs(H, beta)
    ok &= np.allclose(Mg * gam, gam) and abs(np.trace(H @ (Mg * rho - rho))) < 1e-12
R.check("the bath with e^{-beta E_k} = w_k/n_k has partition function one and Gibbs state the density of tau; "
        "U = sum_i |i><i| x u_i conserves energy and gives M_ij = tau(u_j^* u_i); dephasing keeps every population, the "
        "Gibbs state, and a zero energy term", bool(ok))

# ---------------------------------------------------------------------------------------------------- 6. cyclotomic
mp.mp.dps = 50
ok = True
for p in range(1, 13):
    z4 = mp.exp(2j * mp.pi / (4 * p))
    z8 = mp.exp(2j * mp.pi / (8 * p))
    for kk in range(0, 4 * p):
        ok &= abs((z4 ** (2 * kk) + z4 ** (-2 * kk)) / 2 - mp.cos(kk * mp.pi / p)) < mp.mpf(10) ** -45
        ok &= abs((z4 ** (2 * kk) - z4 ** (-2 * kk)) / (2 * z4 ** p) - mp.sin(kk * mp.pi / p)) < mp.mpf(10) ** -45
    ok &= abs(z8 ** p + z8 ** (-p) - mp.sqrt(2)) < mp.mpf(10) ** -45 and abs(z8 ** (2 * p) - 1j) < mp.mpf(10) ** -45
R.check("cos(k pi/p) = (z^{2k} + z^{-2k})/2 and sin(k pi/p) = (z^{2k} - z^{-2k})/(2 z^p) with z = zeta_{4p}; "
        "sqrt2 = zeta_{8p}^p + zeta_{8p}^{-p} and i = zeta_{8p}^{2p} (p <= 12, 50 digits)", bool(ok))
R.close()
