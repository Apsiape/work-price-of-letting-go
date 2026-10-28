"""A process and its time reverse (Section "A process and its time reverse", Propositions "A process and its reverse
can cost differently" and "The asymmetry is not generic", and their proofs in Appendix "A process and its reverse").

Checks:
  1. exact structure (sympy): gamma = diag(1/2, 1/3, 1/6) from H, the M_i sum to I, Tr P_+- gamma = 5/12,
     Tr P_2 gamma = 1/6, N(gamma) = gamma; the Petz reverse in the stated form, N#(gamma) = gamma; D in the basis
     |+>, |->, |2>; <+|H - N^*(H)|-> = -(1/2) kT ln(3/2); N(|+>) and N(|->) orthogonal;
  2. the Kraus products of N span B(span{+,2}) + B(span{-,2}) (dimension 7), the Hermitian kernel of Psi is spanned by
     the +- coherences; N# reads only populations, its Kraus products contain every |i><i| and D# is diagonal;
  3. the reduction: dephasing sigma and pinching rho never lower the objective, and the reduced three-variable
     objective equals the matrix objective;
  4. the value: the two equations have one positive solution t = 1.02099, z = 0.16236; Euler's relation
     c = ln(1+z) + (1/2) ln(3/2)(t-1) = 0.15471030022...; strict concavity; an interval-arithmetic bracket
     0.1547103002210 < c < 0.1547103002225 from a rational point (value and tangent plane);
  5. the dual certificate: beta(D - Psi^*(Y)) = -(a/2)[[t,-1,0],[-1,1/t,0],[0,0,0]] <= 0 for every t > 0 (symbolic), and
     at the faithful sigma_* the stationarity -ln sigma + N^*(ln N sigma) + beta Psi^*(Y) = cI holds to 40 digits, so
     g_Y = c; B(N) from both sides numerically; B(N#) = 0 and both capacities 0;
  6. the two linear tests, the rewritten reverse test against the direct one on random Gibbs-preserving channels, and
     examples where both, one, or neither hold;
  7. Proposition "generic": full Kraus rank passes both tests, Petz of a mixture with gamma Tr, the Choi matrix
     I (x) gamma; the theta family (symbolic Gibbs preservation, POVM, no u-v Kraus product, <u|H|v> =
     kT ln(3/2) sin cos) is a separated pair for every 0 < theta < pi/2, and coincides with N at theta = pi/4.
"""
import math

import mpmath as mp
import numpy as np
import sympy as sp

from qtools import (Channel, Report, batch_cost_smooth, capacity, choi_of, dag, dm, herm, kraus_from_choi, opnorm,
                    powm_h, random_density, span_residual)

R = Report("A process and its time reverse")
rng = np.random.default_rng(20261016)

# ---------------------------------------------------------------------------------------------------------------------
# 1. exact structure
a, b = sp.log(sp.Rational(3, 2)), sp.log(3)
Hs = sp.diag(0, a, b)
gs = sp.diag(*[sp.exp(-h) for h in (0, a, b)])
gs = gs / gs.trace()
s2 = sp.sqrt(2)
plus = sp.Matrix([1, 1, 0]) / s2
minus = sp.Matrix([1, -1, 0]) / s2
two = sp.Matrix([0, 0, 1])
Pp, Pm, P2 = plus * plus.T, minus * minus.T, two * two.T
M = [Pp + P2 / 2, sp.Rational(4, 5) * Pm, sp.Rational(1, 5) * Pm + P2 / 2]
N = lambda r: sp.diag(*[(Mi * r).trace() for Mi in M])
Nstar = lambda Xm: sum((Xm[i, i] * M[i] for i in range(3)), sp.zeros(3))
ok1 = gs == sp.diag(sp.Rational(1, 2), sp.Rational(1, 3), sp.Rational(1, 6))
ok1 &= sp.simplify(sum(M, sp.zeros(3)) - sp.eye(3)) == sp.zeros(3)
ok1 &= sp.simplify((Pp * gs).trace() - sp.Rational(5, 12)) == 0 and sp.simplify((Pm * gs).trace() - sp.Rational(5, 12)) == 0
ok1 &= (P2 * gs).trace() == sp.Rational(1, 6)
ok1 &= sp.simplify(N(gs) - gs) == sp.zeros(3)
gh, gmh = gs.applyfunc(sp.sqrt), gs.applyfunc(lambda v: 1 / sp.sqrt(v) if v != 0 else 0)
Nsharp = lambda r: sum((r[i, i] * gh * M[i] * gh / gs[i, i] for i in range(3)), sp.zeros(3))
rsym = sp.Matrix(3, 3, lambda i, j: sp.Symbol(f"r{i}{j}"))
ok1 &= sp.simplify(gh * Nstar(gmh * rsym * gmh) * gh - Nsharp(rsym)) == sp.zeros(3)
ok1 &= sp.simplify(Nsharp(gs) - gs) == sp.zeros(3)
U = sp.Matrix.hstack(plus, minus, two)
Dpm = sp.simplify(U.T * (Nstar(Hs) - Hs) * U)
ok1 &= sp.simplify(Dpm - sp.Matrix([[-a / 2, a / 2, 0], [a / 2, 3 * a / 10 + b / 5, 0], [0, 0, -b / 2]])) == sp.zeros(3)
ok1 &= sp.simplify((plus.T * (Hs - Nstar(Hs)) * minus)[0] + a / 2) == 0
ok1 &= sp.simplify((N(Pp) * N(Pm)).trace()) == 0
R.check("exact: gamma = diag(1/2,1/3,1/6), sum M_i = I, Tr P_+- gamma = 5/12, Tr P_2 gamma = 1/6, N(gamma) = gamma; "
        "N#(rho) = sum rho_ii gamma^{1/2} M_i gamma^{1/2}/gamma_i is the Petz map and fixes gamma; D in (+,-,2) is "
        "[[-a/2, a/2, 0], [a/2, 3a/10 + b/5, 0], [0, 0, -b/2]]; <+|H - N^*(H)|-> = -(1/2) ln(3/2); N(|+>), N(|->) orthogonal",
        bool(ok1))

# numerical channels
af, bf = math.log(1.5), math.log(3.0)
Hn = np.diag([0, af, bf]).astype(complex)
gn = np.diag([0.5, 1 / 3, 1 / 6]).astype(complex)
pl, mi, tw = np.array([1, 1, 0]) / math.sqrt(2), np.array([1, -1, 0]) / math.sqrt(2), np.array([0, 0, 1.0])


def mp_channel(Ms, basis_out=None):
    """Kraus operators sqrt(m)|i><v| of the measure-and-prepare channel rho -> sum_i Tr(M_i rho)|i><i|."""
    K = []
    for i, Mi in enumerate(Ms):
        w, v = np.linalg.eigh(herm(Mi))
        for lam, vec in zip(w, v.T):
            if lam > 1e-12:
                K.append(math.sqrt(lam) * np.outer(np.eye(3)[i], vec.conj()))
    return K


Mn = [dm(pl) + dm(tw) / 2, 0.8 * dm(mi), 0.2 * dm(mi) + dm(tw) / 2]
chN = Channel(mp_channel(Mn), Hn, 1.0)


def petz_kraus(K, g):
    out = sum(k @ g @ dag(k) for k in K)
    return [powm_h(g, 0.5) @ dag(k) @ powm_h(out, -0.5) for k in K]


chR = Channel(petz_kraus(chN.K, gn), Hn, 1.0)

# 2. Kraus products and kernels
prods = chN.products()
mat = np.array([p.reshape(-1) for p in prods]).T
rank = np.linalg.matrix_rank(mat, tol=1e-10)
sub1 = [np.outer(x, y.conj()) for x in (pl, tw) for y in (pl, tw)]
sub2 = [np.outer(x, y.conj()) for x in (mi, tw) for y in (mi, tw)]
ok2 = rank == 7 and all(span_residual(p, sub1 + sub2) < 1e-12 for p in prods) and \
    all(span_residual(s_, prods) < 1e-12 for s_ in sub1 + sub2)
ker = chN.psi_kernel_hermitian()
cohs = [herm(np.outer(pl, mi)) * 2, herm(1j * np.outer(pl, mi)) * 2]
ok2 &= len(ker) == 2 and all(span_residual(k, cohs) < 1e-10 for k in ker)
ok2 &= chN.balance_residual() > 0.1
rprods = chR.products()
ok2 &= all(span_residual(dm(np.eye(3)[i]), rprods) < 1e-10 for i in range(3))
ok2 &= opnorm(chR.D - np.diag(np.diag(chR.D))) < 1e-12 and chR.balance_residual() < 1e-10
for _ in range(20):
    r_ = random_density(3, rng)
    ok2 &= opnorm(chR.phi(r_) - chR.phi(np.diag(np.diag(r_)))) < 1e-12
R.check("the Kraus products of N span B(span{+,2}) + B(span{-,2}) (dimension 7); ker Psi is spanned by the +- "
        "coherences; D is outside the span; N# ignores input coherences, its products contain every |i><i|, D# is "
        "diagonal and inside the span", bool(ok2))

# 3. the reduction
Ub = np.array([pl, mi, tw]).T


def reduced(p, q):
    r = 1 - p - q
    o = np.array([p + r / 2, 0.8 * q, 0.2 * q + r / 2])
    H = lambda v: -sum(x * math.log(x) for x in v if x > 0)
    return -af / 2 * p + (3 * af / 10 + bf / 5) * q - bf / 2 * r + af * math.sqrt(p * q) + H([p, q, r]) - H(o)


ok3, cnt3 = True, 0
for trial in range(400):
    sig = random_density(3, rng)
    X_ = sum(c * k for c, k in zip(rng.standard_normal(2), ker))
    lo_, hi_ = 0.0, 10.0
    for _ in range(60):
        mid = (lo_ + hi_) / 2
        lo_, hi_ = (mid, hi_) if np.min(np.linalg.eigvalsh(sig + mid * X_)) >= 0 else (lo_, mid)
    rho = sig + lo_ * rng.uniform(0, 1) * X_
    obj = np.real(np.trace(rho @ chN.D)) + chN.h(sig)
    sd = Ub @ np.diag(np.diag(dag(Ub) @ sig @ Ub)) @ dag(Ub)            # dephase sigma in (+,-,2)
    Pab = Ub[:, :2] @ dag(Ub[:, :2])
    rp = Pab @ rho @ Pab + dm(tw) @ rho @ dm(tw)                         # remove the +-/2 coherence of rho
    ok3 &= opnorm(chN.psi(rp) - chN.psi(sd)) < 1e-10 and np.min(np.linalg.eigvalsh(rp)) > -1e-10
    obj2 = np.real(np.trace(rp @ chN.D)) + chN.h(sd)
    ok3 &= obj2 >= obj - 1e-10
    p_, q_ = np.real(np.diag(dag(Ub) @ sd @ Ub))[:2]
    ok3 &= reduced(p_, q_) >= obj2 - 1e-10
    cnt3 += 1
for p_, q_ in ((0.4, 0.35), (0.2, 0.7), (0.05, 0.05)):
    r_ = 1 - p_ - q_
    sd = Ub @ np.diag([p_, q_, r_]) @ dag(Ub)
    v = math.sqrt(p_) * pl + math.sqrt(q_) * mi
    rd = np.outer(v, v.conj()) + r_ * dm(tw)
    ok3 &= opnorm(chN.psi(rd) - chN.psi(sd)) < 1e-12
    ok3 &= abs(reduced(p_, q_) - (np.real(np.trace(rd @ chN.D)) + chN.h(sd))) < 1e-12
R.check("the reduction: dephasing sigma and pinching rho keep feasibility and never lower the objective, and the "
        "reduced objective (with h the Shannon entropy in nats) equals the matrix objective at the reduced pair",
        bool(ok3), f"{cnt3} random feasible pairs")

# 4. the value
mp.mp.dps = 50
A, Bc = mp.log(mp.mpf(3) / 2), mp.log(3)
e1 = lambda t, z: 12 * z ** 2 * (1 + z) * mp.power(mp.mpf(3) / 2, t - 1) - z - t ** 2 / 5
e2 = lambda t, z: (1 + z) ** 5 - 3 * (mp.mpf(4) / 5) ** 4 * (mp.mpf(1) / 5 + z / t ** 2) * mp.power(mp.mpf(3) / 2, 4 + mp.mpf(5) / 2 * (1 / t - t))
roots = []
for t0 in (0.2, 0.5, 0.9, 1.2, 1.7, 3.0, 6.0):
    for z0 in (0.02, 0.1, 0.3, 0.8, 2.0, 5.0):
        try:
            rt = mp.findroot([e1, e2], (mp.mpf(t0), mp.mpf(z0)))
        except (ZeroDivisionError, ValueError):
            continue
        if rt[0] > 0 and rt[1] > 0 and all(abs(rt[0] - q[0]) > 1e-20 or abs(rt[1] - q[1]) > 1e-20 for q in roots):
            roots.append(rt)
# sign scan of the two equations on a grid, as an independent count of positive solutions
tt = np.linspace(0.05, 6, 600)
zz = np.linspace(0.005, 6, 600)
T_, Zg = np.meshgrid(tt, zz)
f1 = 12 * Zg ** 2 * (1 + Zg) * 1.5 ** (T_ - 1) - Zg - T_ ** 2 / 5
f2 = (1 + Zg) ** 5 - 3 * 0.8 ** 4 * (0.2 + Zg / T_ ** 2) * 1.5 ** (4 + 2.5 * (1 / T_ - T_))
cells = np.sum((np.sign(f1[:-1, :-1]) != np.sign(f1[1:, 1:])) & (np.sign(f2[:-1, :-1]) != np.sign(f2[1:, 1:])))
t, z = roots[0]
c = mp.log(1 + z) + A / 2 * (t - 1)
p = 1 / (1 + t ** 2 + 2 * z)
q, r = t ** 2 * p, 2 * z * p


def Fmp(p_, q_):
    r_ = 1 - p_ - q_
    o = [p_ + r_ / 2, mp.mpf(4) / 5 * q_, q_ / 5 + r_ / 2]
    Hh = lambda v: -mp.fsum(x * mp.log(x) for x in v)
    return -A / 2 * p_ + (3 * A / 10 + Bc / 5) * q_ - Bc / 2 * r_ + A * mp.sqrt(p_ * q_) + Hh([p_, q_, r_]) - Hh(o)


grad = [mp.diff(lambda x: Fmp(x, q), p), mp.diff(lambda x: Fmp(p, x), q)]
ok4 = len(roots) == 1 and mp.nstr(t, 6) == "1.02099" and mp.nstr(z, 5) == "0.16236"
ok4 &= abs(Fmp(p, q) - c) < mp.mpf(10) ** -40 and max(abs(g) for g in grad) < mp.mpf(10) ** -30
ok4 &= mp.nstr(c, 11) == "0.15471030022"
R.check("the equations have one positive solution t = 1.02099, z = 0.16236 (root search from 42 starts and a sign "
        "scan); at p = 1/(1+t^2+2z), q = t^2 p, r = 2zp the gradient vanishes and Euler's relation gives "
        "c = ln(1+z) + (1/2) ln(3/2)(t-1) = F(p, q) = 0.15471030022", bool(ok4),
        f"t = {mp.nstr(t, 12)}, z = {mp.nstr(z, 12)}, c = {mp.nstr(c, 20)}, sign-change cells {cells}")
# strict concavity of the reduced objective on the open simplex
worst_eig = -np.inf
for i in range(1, 120):
    for j in range(1, 120 - i):
        pp, qq = i / 120, j / 120
        hh = 1e-4
        fpp = (reduced(pp + hh, qq) - 2 * reduced(pp, qq) + reduced(pp - hh, qq)) / hh ** 2
        fqq = (reduced(pp, qq + hh) - 2 * reduced(pp, qq) + reduced(pp, qq - hh)) / hh ** 2
        fpq = (reduced(pp + hh, qq + hh) - reduced(pp + hh, qq - hh) - reduced(pp - hh, qq + hh) + reduced(pp - hh, qq - hh)) / (4 * hh * hh)
        worst_eig = max(worst_eig, np.max(np.linalg.eigvalsh(np.array([[fpp, fpq], [fpq, fqq]]))))
R.check("the reduced objective is strictly concave on the open simplex (Hessian on a grid of 7000 points)",
        worst_eig < -0.05, f"largest Hessian eigenvalue {worst_eig:.3f}")
# interval arithmetic: value at a rational point (lower bound), tangent plane over the simplex (upper bound)
iv = mp.iv
iv.dps = 40
pr, qr = mp.mpf(mp.nstr(p, 25)), mp.mpf(mp.nstr(q, 25))
P0, Q0 = iv.mpf(str(mp.nstr(pr, 25))), iv.mpf(str(mp.nstr(qr, 25)))
R0 = 1 - P0 - Q0
Ai, Bi = iv.log(iv.mpf(3) / 2), iv.log(iv.mpf(3))
o0, o1, o2 = P0 + R0 / 2, iv.mpf(4) / 5 * Q0, Q0 / 5 + R0 / 2
xlx = lambda x: x * iv.log(x)
Fi = -Ai / 2 * P0 + (3 * Ai / 10 + Bi / 5) * Q0 - Bi / 2 * R0 + Ai * iv.sqrt(P0 * Q0) - xlx(P0) - xlx(Q0) - xlx(R0) \
    + xlx(o0) + xlx(o1) + xlx(o2)
gp = -Ai / 2 + Ai / 2 * iv.sqrt(Q0 / P0) - iv.log(P0) + iv.log(o0)
gq = (3 * Ai / 10 + Bi / 5) + Ai / 2 * iv.sqrt(P0 / Q0) - iv.log(Q0) + iv.mpf(4) / 5 * iv.log(o1) + iv.mpf(1) / 5 * iv.log(o2)
gr = -Bi / 2 - iv.log(R0) + iv.log(o0) / 2 + iv.log(o2) / 2
gdot = gp * P0 + gq * Q0 + gr * R0
upper = max((Fi + gv - gdot).b for gv in (gp, gq, gr))
lower = Fi.a
R.check("interval arithmetic at a rational point: 0.1547103002210 < c < 0.1547103002225 (lower bound from the value, "
        "upper bound from the tangent plane of the concave objective over the simplex)",
        mp.mpf("0.1547103002210") < lower and upper < mp.mpf("0.1547103002225"),
        f"[{mp.nstr(lower, 22)}, {mp.nstr(upper, 22)}]")

# 5. the dual certificate
ts = sp.symbols("t", positive=True)
Xd = sp.diag(a / 2 * (ts - 1), (3 * a + 2 * b) / 10 + a / (2 * ts), -b / 2)
# Psi^*(Y) for Y_(i,s) = X_s on the five Kraus labels is sum_s X_s (sum_i m_is) |s><s| = diag(X) in (+,-,2)
Q = sp.Matrix([[1, 0, sp.Rational(1, 2)], [0, sp.Rational(4, 5), 0], [0, sp.Rational(1, 5), sp.Rational(1, 2)]])
psiY = sp.diag(*[sum(Q[i, s] for i in range(3)) * Xd[s, s] for s in range(3)])
cert = sp.simplify(Dpm - psiY + a / 2 * sp.Matrix([[ts, -1, 0], [-1, 1 / ts, 0], [0, 0, 0]]))
ok5 = cert == sp.zeros(3)
Mt = sp.Matrix([[ts, -1], [-1, 1 / ts]])
ok5 &= sp.simplify(Mt.det()) == 0 and sp.simplify(Mt.trace() - ts - 1 / ts) == 0
R.check("beta(D - Psi^*(Y)) = -(a/2)[[t,-1,0],[-1,1/t,0],[0,0,0]] for every t > 0 (symbolic), a negative "
        "semidefinite matrix (determinant 0, trace -(a/2)(t + 1/t)), so t_Y = 0", bool(ok5))
Xs = [A / 2 * (t - 1), (3 * A + 2 * Bc) / 10 + A / (2 * t), -Bc / 2]
o = [p + r / 2, mp.mpf(4) / 5 * q, q / 5 + r / 2]
Mdiag = [[1, 0, 0], [0, mp.mpf(4) / 5, mp.mpf(1) / 5], [mp.mpf(1) / 2, 0, mp.mpf(1) / 2]]   # Mdiag[s][i] = (M_i)_ss in (+,-,2)
sig = [p, q, r]
stat = [-mp.log(sig[s]) + mp.fsum(Mdiag[s][i] * mp.log(o[i]) for i in range(3)) + Xs[s] for s in range(3)]
gval = -mp.fsum(x * mp.log(x) for x in sig) + mp.fsum(x * mp.log(x) for x in o) + mp.fsum(sig[s] * Xs[s] for s in range(3))
R.check("at the faithful sigma_* = diag(p, q, r) in (+,-,2): -ln sigma + N^*(ln N sigma) + Psi^*(Y) = cI and "
        "g_Y = c to 40 digits; since the objective of g_Y is concave and sigma_* is interior, g_Y = c and B(N) <= c",
        max(abs(s_ - c) for s_ in stat) < mp.mpf(10) ** -40 and abs(gval - c) < mp.mpf(10) ** -40 and min(sig) > 0.1,
        f"residual {mp.nstr(max(abs(s_ - c) for s_ in stat), 3)}")
lo, up, _, _ = batch_cost_smooth(chN)
loR, upR, _, _ = batch_cost_smooth(chR)
cN, cR = capacity(chN), capacity(chR)
R.check("numerically (two-sided engine): B(N) = c and B(N#) = 0, and both capacities vanish",
        abs(lo - float(c)) < 1e-6 and abs(up - float(c)) < 1e-6 and abs(loR) < 1e-7 and abs(upR) < 1e-6
        and abs(cN[0]) < 1e-8 and cN[1] < 1e-6 and abs(cR[0]) < 1e-8 and cR[1] < 1e-6,
        f"B(N) in [{lo:.10f}, {up:.10f}], B(N#) in [{loR:.1e}, {upR:.1e}]")

# ---------------------------------------------------------------------------------------------------------------------
# 6. the two linear tests


def forward_free(ch):
    return span_residual(herm(ch.H - ch.phistar(ch.H)), ch.products()) < 1e-8


def reverse_free_rewritten(K, g, H):
    target = g @ H - sum(k @ (g @ H) @ dag(k) for k in K)
    return span_residual(target, [ka @ g @ dag(kb) for ka in K for kb in K]) < 1e-8


def random_gp_qutrit(rng):
    import cvxpy as cp
    d = 3
    J = cp.Variable((9, 9), hermitian=True)
    Rm = herm(rng.standard_normal((9, 9)) + 1j * rng.standard_normal((9, 9)))
    cons = [J >> 0, cp.partial_trace(J, [3, 3], axis=1) == np.eye(3),
            cp.partial_trace(cp.kron(gn.T, np.eye(3)) @ J, [3, 3], axis=0) == gn]
    cp.Problem(cp.Maximize(cp.real(cp.trace(Rm @ J))), cons).solve(solver="CLARABEL")
    K = kraus_from_choi(np.asarray(J.value), 3, 3, tol=1e-7)
    s_ = sum(dag(k) @ k for k in K)
    w, v = np.linalg.eigh(s_)
    return [k @ (v * w ** -0.5) @ dag(v) for k in K]


def family(th):
    u = np.array([math.cos(th), math.sin(th), 0])
    v = np.array([-math.sin(th), math.cos(th), 0])
    zz_ = math.sin(th) ** 2
    return [dm(u) + zz_ * dm(tw), 2 / (2 + zz_) * dm(v), zz_ / (2 + zz_) * dm(v) + (1 - zz_) * dm(tw)]


agree, total, kinds = 0, 0, set()
for trial in range(120):
    if trial < 40:
        K = random_gp_qutrit(rng)
    else:
        w_ = rng.dirichlet(np.ones(3)) if rng.random() < 0.5 else np.eye(3)[int(rng.integers(3))]
        th = rng.uniform(0.05, math.pi / 2 - 0.05, 2)
        comps = [mp_channel(family(th[0])), petz_kraus(mp_channel(family(th[1])), gn), mp_channel(family(th[1]))]
        K = [math.sqrt(wi) * k for wi, c_ in zip(w_, comps) if wi > 0 for k in c_]
    chF = Channel(K, Hn, 1.0)
    if opnorm(chF.phi(gn) - gn) > 1e-6:
        continue
    direct = forward_free(Channel(petz_kraus(K, gn), Hn, 1.0))
    rew = reverse_free_rewritten(K, gn, Hn)
    agree += direct == rew
    total += 1
    kinds.add((forward_free(chF), rew))
R.check("reverse free <=> gamma H - Phi(gamma H) in span{A_i gamma A_j^*}: agrees with the direct test on the Petz map",
        agree == total and total >= 100, f"{agree}/{total} Gibbs-preserving channels; (forward, reverse) seen: {sorted(kinds)}")
KNN = [np.kron(k1, k2) for k1 in chN.K for k2 in chR.K]
H2 = np.kron(Hn, np.eye(3)) + np.kron(np.eye(3), Hn)
g2 = np.kron(gn, gn)
chNN = Channel(KNN, H2, 1.0)
Kmix = [math.sqrt(0.9) * k for k in chN.K] + [math.sqrt(0.1 * gn[i, i].real) * np.outer(np.eye(3)[i], np.eye(3)[j])
                                            for i in range(3) for j in range(3)]
ex = {"full rank (N mixed with gamma Tr)": (forward_free(Channel(Kmix, Hn)), reverse_free_rewritten(Kmix, gn, Hn)),
      "N": (forward_free(chN), reverse_free_rewritten(chN.K, gn, Hn)),
      "N#": (forward_free(chR), reverse_free_rewritten(chR.K, gn, Hn)),
      "N x N#": (forward_free(chNN), reverse_free_rewritten(KNN, g2, H2))}
R.check("both, one or neither test can hold: full rank (both), N (reverse only), N# (forward only), N x N# (neither)",
        ex == {"full rank (N mixed with gamma Tr)": (True, True), "N": (False, True), "N#": (True, False),
               "N x N#": (False, False)}, str(ex))

# ---------------------------------------------------------------------------------------------------------------------
# 7. Proposition "generic"
ok7 = True
for delta in (1e-3, 0.1, 0.7):
    Kd = [math.sqrt(1 - delta) * k for k in chN.K] + [math.sqrt(delta * gn[i, i].real) * np.outer(np.eye(3)[i], np.eye(3)[j])
                                                      for i in range(3) for j in range(3)]
    chd = Channel(Kd, Hn)
    ok7 &= np.min(np.linalg.eigvalsh(chd.choi())) > 0 and len(kraus_from_choi(chd.choi(), 3, 3)) == 9
    ok7 &= np.linalg.matrix_rank(np.array([p_.reshape(-1) for p_ in chd.products()]).T, tol=1e-12) == 9
    Kr = petz_kraus(Kd, gn)
    ok7 &= len(kraus_from_choi(Channel(Kr, Hn).choi(), 3, 3)) == 9
    for _ in range(5):
        s_ = random_density(3, rng)
        ok7 &= opnorm(Channel(Kr, Hn).phi(s_) - (1 - delta) * chR.phi(s_) - delta * gn) < 1e-10
    ok7 &= forward_free(chd) and reverse_free_rewritten(Kd, gn, Hn)
gTr = choi_of(lambda r_: np.trace(r_) * gn, 3)
ok7 &= opnorm(gTr - np.kron(np.eye(3), gn)) < 1e-14
R.check("full Kraus rank: the products span all matrices and both tests hold; (1-delta)Phi + delta gamma Tr has full "
        "rank, Choi(gamma Tr) = I (x) gamma, and its Petz map is (1-delta)Phi# + delta gamma Tr", bool(ok7))
th_s = sp.symbols("theta", positive=True)
cs_, sn_ = sp.cos(th_s), sp.sin(th_s)
u_s = sp.Matrix([cs_, sn_, 0])
v_s = sp.Matrix([-sn_, cs_, 0])
zs = sn_ ** 2
Mth = [u_s * u_s.T + zs * P2, 2 / (2 + zs) * v_s * v_s.T, zs / (2 + zs) * v_s * v_s.T + (1 - zs) * P2]
ok7b = sp.simplify(sum(Mth, sp.zeros(3)) - sp.eye(3)) == sp.zeros(3)
ok7b &= sp.simplify((u_s.T * gs * u_s)[0] - (sp.Rational(1, 2) - zs / 6)) == 0
ok7b &= sp.simplify((v_s.T * gs * v_s)[0] - (2 + zs) / 6) == 0
pops = [sp.simplify((Mi * gs).trace()) for Mi in Mth]
ok7b &= [sp.simplify(x - y) for x, y in zip(pops, (sp.Rational(1, 2), sp.Rational(1, 3), sp.Rational(1, 6)))] == [0, 0, 0]
ok7b &= sp.simplify((u_s.T * Hs * v_s)[0] - a * sn_ * cs_) == 0
ok7b &= all(sp.simplify(Mi.subs(th_s, sp.pi / 4) - Mo) == sp.zeros(3) for Mi, Mo in zip(Mth, M))
R.check("theta family (symbolic): a POVM, Gibbs-preserving (<u|gamma|u> = 1/2 - z/6, <v|gamma|v> = (2+z)/6), "
        "<u|H|v> = kT ln(3/2) sin(theta) cos(theta), and N at theta = pi/4", bool(ok7b))
ok7c, rows7 = True, []
for frac in (0.02, 0.15, 0.35, 0.65, 0.9, 0.98):
    th = frac * math.pi / 2
    u = np.array([math.cos(th), math.sin(th), 0])
    v = np.array([-math.sin(th), math.cos(th), 0])
    K = mp_channel(family(th))
    chF = Channel(K, Hn, 1.0)
    chB = Channel(petz_kraus(K, gn), Hn, 1.0)
    ok7c &= all(abs(np.vdot(u, p_ @ v)) < 1e-12 for p_ in chF.products())
    ok7c &= (not forward_free(chF)) and forward_free(chB) and opnorm(chF.phi(gn) - gn) < 1e-12
    lo_, up_, _, _ = batch_cost_smooth(chF)
    ok7c &= lo_ > 1e-4
    rows7.append(f"theta = {frac:.2f} pi/2: B = {lo_:.5f}")
R.check("every 0 < theta < pi/2 gives a separated pair: no u-v Kraus product, forward test fails and B > 0, reverse "
        "test holds", ok7c, "; ".join(rows7))
R.close()
