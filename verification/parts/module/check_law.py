"""The work law: the construction of Section 3 and Appendix B.

Checks:
  1. B.2, the joint tangent: for t_* maximizing S(omega_t) + e_beta(t) and zeta = omega_{t_*}, the support of zeta contains
     the support of every omega_t, and Tr omega_t(-log2 zeta) + e_beta(t) <= v for every tester (SDP over testers), with
     equality at t_*; random collisions, a collision with an idle register (singular zeta) and an energy-dominated one;
  2. B.2, rounding: q obtained from zeta_s = (1-s) zeta + s omega_0 by rounding its logarithmic energies to the mesh h
     satisfies e^{-h} zeta_s <= q <= e^h zeta_s and omega_t <= (e^h d^2/s) q, and the tangent (eq. (tangent))
     Tr omega_t(-log2 q) - S(p) + e_beta(t) <= g + c_s + h/ln2 holds for every tester (SDP);
  3. B.3: each imaginary-time filtered contact has singular values within e^{+-|x| beta span(H_j)/2}, so the whole episode
     map satisfies e^{-C|x|} <= W_z^* W_z <= e^{C|x|} with C = beta sum_j span(H_j);
  4. B.4: optimizing t in exp[t Delta + N(ta + C K_s t^2)] with K_s ~ 1/s and s = gamma = N^{-1/8} gives an exponent of
     order N^{5/8} at t of order N^{-1/4} <= 1/4 (sympy);
  5. B.6-B.7: the constant chain: kappa = 1 + O(N^-40); the error N N^-3 + N(rho + e^h - 1) + 2(kappa - 1) + delta_f -> 0 with
     rho = h = N^-12; the geometric-tail bound Z_{P_X} <= Z_M e^{-beta E_cap} e^{d_N} L_N/(1 - e^{-h}) by direct summation;
     the overheads O(log N/N + h) of the nominal debit;
  6. B.7: an integer-valued variable with second moment mu has entropy at most lambda mu + ln sum_b e^{-lambda b^2}
     (equality at the Gibbs law), and with lambda = (1/2) ln(1/mu) the bound tends to zero;
  7. B.1: averaging a collision over a finite grid of common phases, controlled by a uniform flag in the bath, makes the
     process commute with the common time translation and does not increase its gain (certified Frank-Wolfe bounds).
"""
import itertools
import math

import numpy as np
import sympy as sp

from qtools import Report, dm, embed, entropy, gibbs, herm, ket, logm_psd, random_density, random_unitary
from combs import Realization, TesterLP, bath_functional, energy_matrix, flat_record, maximize_score, omega_map, random_tester

R = Report("The work law: construction")
rng = np.random.default_rng(2718)
LN2 = math.log(2)
beta = 1.0
lp = TesterLP([2, 2])
SW = np.eye(4)[[0, 2, 1, 3]].astype(complex)

# 1-2. joint tangent ---------------------------------------------------------------------------------------------
cases = []
for _ in range(4):
    dB = int(rng.integers(2, 4))
    cases.append(("random", Realization.collision([2, 2], random_density(dB, rng), [random_unitary(2 * dB, rng) for _ in range(2)]),
                  [np.diag([0.0, rng.uniform(0.3, 2)]).astype(complex) for _ in range(2)]))
# idle pure register: bath (B, idle) with the idle register never touched
dB = 2
tau = np.kron(random_density(dB, rng), dm(ket((0,))))
U = [embed(random_unitary(2 * dB, rng), [0, 1], [2, dB, 2]) for _ in range(2)]
cases.append(("idle register", Realization.collision([2, 2], tau, U), [np.diag([0.0, 1.0]).astype(complex)] * 2))
# energy dominated: the delay device at beta E = 8
cases.append(("beta E = 8", Realization.collision([2, 2], dm(ket((0,))), [SW, SW]), [np.diag([0.0, 8.0]).astype(complex)] * 2))

ok1, ok1s, ok2a, ok2b, ok2c = True, True, True, True, True
details = []
for name, real, H in cases:
    d = 4
    Zs, val, up = maximize_score(real, H, beta, lp, iters=80)
    om, Mt = omega_map(real)
    Ge = energy_matrix(real, H)
    zeta = herm(om(Zs))
    v = entropy(zeta) + beta / LN2 * float(np.trace(Ge @ Zs).real)      # max of S(omega_t) + e_beta(t)
    w0 = herm(om(flat_record([2, 2])))
    # support: zeta is positive on the support of omega_0, which contains every omega_t
    wv, vv = np.linalg.eigh(w0)
    Ps = vv[:, wv > 1e-12]
    ok1s &= np.linalg.eigvalsh(herm(Ps.conj().T @ zeta @ Ps)).min() > 1e-9
    Lz = -logm_psd(zeta, 2, floor=1e-300)
    Lz = Ps @ (Ps.conj().T @ Lz @ Ps) @ Ps.conj().T                      # read on the support
    G = bath_functional(Mt, Lz) + beta / LN2 * Ge
    _, best = lp.solve(G)
    at_star = float(np.trace(G @ Zs).real)
    ok1 &= best <= v + 1e-6 and abs(at_star - v) < 1e-9
    details.append(f"{name}: max {best:.7f} vs v {v:.7f}")
    # rounding and eq. (tangent)
    S_p = real.S_tau()
    g = v - S_p
    for s, h in ((0.1, 0.05), (0.01, 0.01), (0.3, 0.2)):
        zs = (1 - s) * zeta + s * w0
        w, V = np.linalg.eigh(herm(zs))
        keep = w > 1e-14
        xi = -np.log(w[keep])
        qt = np.exp(-h * np.floor(xi / h))
        q = (V[:, keep] * (qt / qt.sum())) @ V[:, keep].conj().T
        Pk = V[:, keep]
        A = Pk.conj().T @ q @ Pk
        Bm = Pk.conj().T @ zs @ Pk
        ok2a &= np.linalg.eigvalsh(herm(A - math.exp(-h) * Bm)).min() > -1e-12 and np.linalg.eigvalsh(herm(math.exp(h) * Bm - A)).min() > -1e-12
        # omega_t <= (e^h d^2/s) q on random testers
        qi = Pk @ np.diag(1 / np.sqrt(np.linalg.eigvalsh(herm(A)).clip(1e-300))) @ Pk.conj().T
        wq, Vq = np.linalg.eigh(herm(A))
        q_inv_half = Pk @ Vq @ np.diag(wq ** -0.5) @ Vq.conj().T @ Pk.conj().T
        for _ in range(5):
            wt = om(random_tester([2, 2], rng).record())
            ok2b &= np.linalg.eigvalsh(herm(q_inv_half @ wt @ q_inv_half)).max() <= math.exp(h) * d * d / s + 1e-9
        Lq = -logm_psd(q, 2, floor=1e-300)
        Lq = Pk @ (Pk.conj().T @ Lq @ Pk) @ Pk.conj().T
        Gq = bath_functional(Mt, Lq) + beta / LN2 * Ge
        _, bq = lp.solve(Gq)
        c_s = math.log2(1 / (1 - s))
        ok2c &= bq - S_p <= g + c_s + h / LN2 + 1e-6
R.check("B.2: zeta is positive on the support of omega_0, which contains every omega_t", ok1s)
R.check("B.2: Tr omega_t(-log2 zeta) + e_beta(t) <= v for every tester (SDP), with equality at t_*", ok1, "; ".join(details))
R.check("B.2: rounding to the mesh h gives e^{-h} zeta_s <= q <= e^h zeta_s", ok2a)
R.check("B.2: omega_t <= (e^h d^2/s) q on random testers", ok2b)
R.check("eq. (tangent): Tr omega_t(-log2 q) - S(p) + e_beta(t) <= g + c_s + h/ln2 for every tester (SDP)", ok2c)

# 3. filtered contacts --------------------------------------------------------------------------------------------
ok3 = True
for _ in range(50):
    d, dB = 2, int(rng.integers(1, 4))
    Hj = np.diag(rng.uniform(0, 3, d))
    U = random_unitary(d * dB, rng)
    x, y = rng.uniform(-1, 1), rng.uniform(-3, 3)
    z = x + 1j * y
    Fp = np.kron(np.diag(np.exp(z * beta * np.diag(Hj) / 2)), np.eye(dB))
    Fm = np.kron(np.diag(np.exp(-z * beta * np.diag(Hj) / 2)), np.eye(dB))
    sv = np.linalg.svd(Fp @ U @ Fm, compute_uv=False)
    sp_ = np.ptp(np.diag(Hj))
    ok3 &= sv.max() <= math.exp(abs(x) * beta * sp_ / 2) + 1e-12 and sv.min() >= math.exp(-abs(x) * beta * sp_ / 2) - 1e-12
R.check("B.3: e^{z beta H/2} U e^{-z beta H/2} has singular values within e^{+-|Re z| beta span(H)/2}", ok3)

# 4. the B.4 exponent -------------------------------------------------------------------------------------------
N, C, t = sp.symbols("N C t", positive=True)
s_ = N ** sp.Rational(-1, 8)
gam = s_
Ks = C / s_
expo = -t * N * gam * sp.log(2) + N * C * Ks * t ** 2              # log of the Markov bound at the excess N gamma ln2
tstar = sp.solve(sp.diff(expo, t), t)[0]
val = sp.simplify(expo.subs(t, tstar))
R.check("B.4: the optimal t is of order N^{-1/4} and the exponent of order -N^{5/8}",
        sp.simplify(sp.diff(tstar * N ** sp.Rational(1, 4), N)) == 0
        and sp.simplify(val / N ** sp.Rational(5, 8) + sp.log(2) ** 2 / (4 * C ** 2)) == 0,
        f"t* = {sp.simplify(tstar)}, exponent = {val}")

# 5. constants of B.6-B.7 ----------------------------------------------------------------------------------------
ok5 = True
errs = []
for Nn in (10, 100, 1000, 10 ** 4):
    rho = hh = Nn ** -12.0
    th = df = Nn ** -40.0
    kap = 1 / ((1 - th) ** 2 * (1 - df))
    err = Nn * Nn ** -3.0 + Nn * (rho + math.expm1(hh)) + 2 * (kap - 1) + df
    errs.append(err)
    ok5 &= kap - 1 <= 4 * Nn ** -40.0
    overhead = (math.log2(1 / -math.expm1(-hh)) + 2 * math.log2(Nn)) / Nn      # log2 L_N with L_N = O(N^2), r = 2
    ok5 &= overhead <= 30 * math.log2(Nn) / Nn
R.check("B.6-B.7: kappa = 1 + O(N^-40); the error N N^-3 + N(rho + e^h - 1) + 2(kappa - 1) + delta_f tends to 0, "
        "and the tail overheads are O(log N/N)", ok5 and all(a > b for a, b in zip(errs, errs[1:])) and errs[-1] < 1e-7,
        ", ".join(f"{e:.1e}" for e in errs))
# geometric-tail bound for Z_{P_X}
ok5b = True
for _ in range(30):
    h = float(rng.choice([0.1, 0.5, 1.0]))
    om_ = np.array([1.0, math.sqrt(3)])
    payload = list(itertools.product(range(-3, 4), repeat=2))
    dN = float(rng.uniform(0, 5))
    total = 0.0
    for b in payload:
        e_b = beta * (np.array(b) @ om_)
        b0min = math.ceil((-dN - e_b) / h - 1e-12)
        for b0 in range(b0min, b0min + 4000):
            Y = -(h * b0 + e_b)                           # Y = beta(E_cap - H_bank)
            if Y <= dN:
                total += math.exp(Y)
    bound = math.exp(dN) * len(payload) / (1 - math.exp(-h))
    ok5b &= total <= bound * (1 + 1e-12)
R.check("B.7: summing the geometric tails gives Z_{P_X} <= Z_M e^{-beta E_cap} e^{d_N} L_N/(1 - e^{-h})", ok5b)

# 6. entropy of an integer variable --------------------------------------------------------------------------------
ok6, near6 = True, 0
for k in range(300):
    support = np.arange(-6, 7)
    lam = float(rng.uniform(0.05, 3))
    if k % 3 == 0:
        P = np.exp(-lam * support ** 2)
        P /= P.sum()
    else:
        P = rng.dirichlet(np.ones(len(support)) * float(rng.choice([0.2, 1, 5])))
    mu = float(P @ support ** 2)
    Hn = float(-np.sum(P[P > 0] * np.log(P[P > 0])))
    bound = lam * mu + math.log(np.sum(np.exp(-lam * np.arange(-200, 201) ** 2)))
    ok6 &= Hn <= bound + 1e-12
    near6 += bound - Hn < 1e-3
lim = []
for mu in (1e-2, 1e-4, 1e-8, 1e-12):
    lam = 0.5 * math.log(1 / mu)
    lim.append(lam * mu + math.log(np.sum(np.exp(-lam * np.arange(-50, 51) ** 2.0))))
R.check("B.7: H <= lambda mu + ln sum_b e^{-lambda b^2} for integer variables (equality at the Gibbs law), and the bound "
        "with lambda = (1/2) ln(1/mu) tends to 0", ok6 and near6 >= 90 and all(a > b for a, b in zip(lim, lim[1:])) and lim[-1] < 1e-5,
        ", ".join(f"{x:.2e}" for x in lim))

# 7. B.1: covariance by a flagged grid of common phases ---------------------------------------------------------------
from combs import translation_generator
ok7, rows7 = True, []
Kg = 8
for _ in range(3):
    dB = 2
    tau = random_density(dB, rng)
    U = [random_unitary(2 * dB, rng) for _ in range(2)]
    H = [np.diag([0.0, 1.0]).astype(complex), np.diag([0.0, 1.0]).astype(complex)]
    orig = Realization.collision([2, 2], tau, U)
    # flag u in a grid of K phases (uniform, purified by F); contact j applies D(u) U_j D(u)^* on (port, B)
    taup = np.kron(np.eye(Kg) / Kg, tau).astype(complex)
    Uf = []
    for j in range(2):
        W = np.zeros((2 * Kg * dB, 2 * Kg * dB), dtype=complex)
        for u_i in range(Kg):
            u = 2 * math.pi * u_i / Kg
            Dm = np.diag(np.exp(-1j * u * np.diag(H[j]).real))
            Uu = np.kron(Dm, np.eye(dB)) @ U[j] @ np.kron(Dm.conj().T, np.eye(dB))      # (port, B)
            W += embed(Uu, [0, 2], [2, Kg, dB]) @ embed(dm(ket((u_i,), [Kg])), [1], [2, Kg, dB])
        Uf.append(W)
    cov = Realization.collision([2, 2], taup, Uf)
    G = translation_generator([2, 2], H)
    comm = np.abs(cov.R @ G - G @ cov.R).max()
    _, g0, g0_up = maximize_score(orig, H, beta, lp, iters=60)
    _, g1, g1_up = maximize_score(cov, H, beta, lp, iters=60)
    ok7 &= comm < 1e-12 and np.abs(orig.R @ G - G @ orig.R).max() > 1e-3 and g1_up <= g0 + 1e-6
    rows7.append(f"gain {g0:.5f} -> {g1:.5f}")
R.check("B.1: a flagged grid of common phases makes the collision covariant and does not increase its gain", ok7,
        "; ".join(rows7))
R.close()
