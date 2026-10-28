"""The examples of the batch law (Theorem "Waiting does not help", Propositions "Which channels reach the capacity in
batch", "Gibbs preservation is not enough" and "A Gibbs-preserving channel that reaches its capacity", with their
appendices).

Checks:
  1. X-dephasing: B = E/2 with rho = |0><0|, sigma = I/2 and the dual certificate Y = 0; capacity
     beta^{-1} ln cosh(beta E/2) < E/2 and the excess beta^{-1} ln[2/(1 + e^{-beta E})];
  2. phase noise: channels fixing a basis have diagonal Kraus operators and an environment that sees only the diagonal;
     for mixtures of commuting unitaries B = w = lambda_max(Phi^*(H) - H), and the capacity reaches w exactly when
     the top eigenspace of Phi^*(H) - H contains a common eigenvector of the V_j^* V_k (random, constructed, pinchings,
     Hadamard x energy dephasing);
  3. a protected subsystem: B = L, the capacity equals L exactly for additive H; the Bell example (3E/4 at every
     temperature, capacity -E/4 + beta^{-1} ln[(e^{beta E}+3)/4], 0.072E at beta E = ln 2, mixed outputs) and the exact
     gain (3/4)E I - 2zH of its finite construction;
  4. the Gibbs-preserving qutrit: completeness, Gibbs preservation, Psi(rho) = Psi(sigma) = diag(1-y^2, y^2), Phi(sigma)
     = sigma, Tr rho D = y^2 E_1 (exact, symbolic), non-covariance, B >= y^2 E_1 and capacity 0;
  5. the channel that reaches its capacity: sigma_0 and sigma_1 (det 1/6 and 0), Gibbs preservation, Phi o Delta = Phi,
     Delta o Phi = gamma Tr, capacity 0 and B = 0; the time-covariant Psi and its capacity E(3/4 - ln2/ln3) = 0.119E;
     the Stage 2 swap; the clock increments (3/16, 5/8, 3/16, variance 3/8 = 2 Var_gamma(H)/E^2); the return bound
     sqrt(2 E|K|/L) <= sqrt(2 sqrt(3n/8)/L); the qubit family c_1 = -(gamma_0/gamma_1) c_0 and its extreme point.
"""
import itertools
import math

import numpy as np
import sympy as sp
from scipy.linalg import expm

from qtools import (HAD, Channel, Report, X, Z, batch_cost, batch_cost_smooth, capacity, choi_of, dag, dm, dual_value, gmax, herm,
                    kraus_from_choi, opnorm, random_density, random_unitary, relent, span_residual)

R = Report("Examples of the batch law")
rng = np.random.default_rng(20261015)


def covariance_defect(ch, ts=(0.37, 1.1, 2.3)):
    worst = 0.0
    for t in ts:
        Ut = expm(-1j * ch.H * t)
        for _ in range(3):
            rho = random_density(ch.d, rng)
            worst = max(worst, opnorm(ch.phi(Ut @ rho @ dag(Ut)) - Ut @ ch.phi(rho) @ dag(Ut)))
    return worst


# ---------------------------------------------------------------------------------------------------------------------
# 1. X-dephasing
ok1, rows1 = True, []
for E, beta in ((1.0, 1.0), (1.0, math.log(2)), (2.0, 0.3), (0.5, 4.0)):
    Hq = np.diag([0.0, E]).astype(complex)
    ch = Channel([np.eye(2) / math.sqrt(2), X / math.sqrt(2)], Hq, beta)
    rho0, sig = dm([1, 0]), np.eye(2) / 2
    ok1 &= opnorm(ch.psi(rho0) - ch.psi(sig)) < 1e-15
    pair = np.real(np.trace(rho0 @ ch.D)) + ch.h(sig) / beta
    up, _, _ = dual_value(ch, np.zeros((2, 2)))
    ok1 &= abs(pair - E / 2) < 1e-14 and abs(up - E / 2) < 1e-9 and ch.balance_residual() > 0.5
    clo, cup, _ = capacity(ch)
    tb = math.log(math.cosh(beta * E / 2)) / beta
    ok1 &= abs(clo - tb) < 1e-8 and abs(cup - tb) < 1e-8 and tb < E / 2
    ok1 &= abs(E / 2 - tb - math.log(2 / (1 + math.exp(-beta * E))) / beta) < 1e-12
    rows1.append(f"beta E = {beta * E:.3f}: capacity {clo:.6f} E")
bE = sp.symbols("bE", positive=True)
# E/2 - ln cosh(x)/beta = ln[2/(1+e^{-beta E})]/beta with x = beta E/2 is e^{x}(1 + e^{-2x})/2 = cosh x
ok1 &= sp.simplify((sp.exp(bE / 2) * (1 + sp.exp(-bE)) / 2 - sp.cosh(bE / 2)).rewrite(sp.exp)) == 0
R.check("X-dephasing: Psi(|0><0|) = Psi(I/2) gives B >= E/2, the dual Y = 0 gives B <= E/2; capacity "
        "beta^{-1} ln cosh(beta E/2) < E/2, excess exactly beta^{-1} ln[2/(1 + e^{-beta E})]; unbalanced", ok1,
        "; ".join(rows1))

# ---------------------------------------------------------------------------------------------------------------------
# 2. phase noise


def top_space(Dm, tol=1e-9):
    w, U = np.linalg.eigh(herm(Dm))
    return w[-1], U[:, w >= w[-1] - tol]


def criterion(Vs, Dm, tol=1e-8):
    """Does the top eigenspace of D contain a common eigenvector of all V_j^* V_k (commuting unitaries)?"""
    wmax, P = top_space(Dm)
    d = Dm.shape[0]
    rel = [dag(Vs[j]) @ Vs[k] for j in range(len(Vs)) for k in range(len(Vs)) if j != k]
    if not rel:
        return wmax, True
    G = herm(sum(rng.normal() * (Rm + dag(Rm)) + rng.normal() * 1j * (Rm - dag(Rm)) for Rm in rel))
    ev, B = np.linalg.eigh(G)
    used = np.zeros(d, bool)
    for i in range(d):
        if used[i]:
            continue
        idx = np.where(np.abs(ev - ev[i]) < 1e-7)[0]
        used[idx] = True
        s = np.linalg.svd(dag(P) @ B[:, idx], compute_uv=False)
        if np.any(s > 1 - tol):
            return wmax, True
    return wmax, False


ok2a = True
for trial in range(100):
    d = int(rng.integers(2, 5))
    Ub = random_unitary(d, rng)
    r = int(rng.integers(1, 4))
    cs = rng.standard_normal((r, d)) + 1j * rng.standard_normal((r, d))
    cs /= np.linalg.norm(cs, axis=0)
    K = [Ub @ np.diag(cs[k]) @ dag(Ub) for k in range(r)]
    ch = Channel(K, herm(rng.standard_normal((d, d))))
    rho = random_density(d, rng)
    rdiag = Ub @ np.diag(np.diag(dag(Ub) @ rho @ Ub)) @ dag(Ub)
    ok2a &= all(opnorm(ch.phi(dm(Ub[:, i])) - dm(Ub[:, i])) < 1e-12 for i in range(d))
    ok2a &= opnorm(ch.psi(rho) - ch.psi(rdiag)) < 1e-12 and abs(ch.h(rdiag)) < 1e-10
R.check("a channel fixing every state of a basis has Kraus operators diagonal in it; its environment sees only the "
        "diagonal, and S(sigma) = S(Phi sigma) on the diagonal sigma", ok2a)

ok2, rows2 = True, []


def joint_basis(Vs):
    G = herm(sum(rng.normal() * (V + dag(V)) + rng.normal() * 1j * (V - dag(V)) for V in Vs))
    return np.linalg.eigh(G)[1]


def run_mu(name, ps, Vs, H, beta, expect=None):
    global ok2
    ch = Channel([math.sqrt(p) * V for p, V in zip(ps, Vs)], H, beta)
    wmax, crit = criterion(Vs, ch.D)
    # B = w: the pair rho = psi (top eigenvector of D), sigma = psi dephased in the joint eigenbasis gives w, and the dual
    # Y = 0 gives t_0 + g_0 = w + 0, since a mixture of unitaries never lowers the entropy
    psi = np.linalg.eigh(ch.D)[1][:, -1]
    Jb = joint_basis(Vs)
    ok2 &= all(opnorm(dag(Jb) @ V @ Jb - np.diag(np.diag(dag(Jb) @ V @ Jb))) < 1e-9 for V in Vs)
    sig = Jb @ np.diag(np.abs(dag(Jb) @ psi) ** 2) @ dag(Jb)
    lo = np.real(np.vdot(psi, ch.D @ psi)) + ch.h(sig) / beta
    ok2 &= opnorm(ch.psi(dm(psi)) - ch.psi(sig)) < 1e-10 and abs(ch.h(sig)) < 1e-10
    up, _, _ = dual_value(ch, np.zeros((ch.r, ch.r)))
    clo, cup, _ = capacity(ch)
    ok2 &= abs(lo - wmax) < 1e-9 and abs(up - wmax) < 1e-9              # B = w
    reach = clo > wmax - 1e-6
    ok2 &= reach == crit and (expect is None or crit == expect)
    if not crit:
        ok2 &= cup < wmax - 1e-4
    rows2.append(f"{name}: w = {wmax:.4f}, capacity in [{clo:.4f}, {cup:.4f}], criterion {crit}")


Hq = np.diag([0.0, 1.0]).astype(complex)
run_mu("X-dephasing", [0.5, 0.5], [np.eye(2), X], Hq, 1.0, expect=False)
HA, HB = np.diag([0.0, 1.0]), np.diag([0.0, 0.7])
Hab = (np.kron(HA, np.eye(2)) + np.kron(np.eye(2), HB)).astype(complex)
run_mu("Hadamard x energy dephasing", [0.5, 0.5], [np.kron(HAD, np.eye(2)), np.kron(HAD, Z)], Hab, 1.0, expect=True)
chHZ = Channel([math.sqrt(0.5) * np.kron(HAD, np.eye(2)), math.sqrt(0.5) * np.kron(HAD, Z)], Hab, 1.0)
ok2 &= covariance_defect(chHZ) > 1e-2 and len(kraus_from_choi(chHZ.choi(), 4, 4)) == 2
for trial in range(3):
    U = random_unitary(3, rng)
    Vs = [U @ np.diag(np.exp(1j * rng.uniform(0, 2 * math.pi, 3))) @ dag(U) for _ in range(3)]
    run_mu(f"random commuting mixture {trial}", rng.dirichlet(np.ones(3)), Vs, herm(rng.standard_normal((3, 3))), 1.0)
Wb = HAD
Hblk = np.zeros((3, 3), dtype=complex)
Hblk[:2, :2] = Hq
Hblk[2, 2] = 0.4
Vblk = []
for gph in (0.0, 2.1, 4.0):
    V = np.zeros((3, 3), dtype=complex)
    V[:2, :2] = Wb
    V[2, 2] = np.exp(1j * gph)
    Vblk.append(V)
run_mu("noiseless block with a gate, noise on the rest", [0.3, 0.3, 0.4], Vblk, Hblk, 1.0, expect=True)
v = random_unitary(3, rng)[:, 0]
P1 = dm(v)
Hd = np.diag([0.0, 0.6, 1.3]).astype(complex)
run_mu("pinching, not covariant", [0.5, 0.5], [np.eye(3), P1 - (np.eye(3) - P1)], Hd, 1.0, expect=False)
run_mu("pinching, covariant", [0.5, 0.5], [np.eye(3), np.diag([1, -1, -1]).astype(complex)], Hd, 1.0, expect=True)
R.check("mixtures of commuting unitaries: B = w = lambda_max(Phi^*(H) - H), and the capacity reaches w exactly when the "
        "top eigenspace contains a common eigenvector of all V_j^* V_k; a pinching reaches it exactly when covariant; "
        "Hadamard x energy dephasing reaches it although it is neither covariant nor unitary", ok2, "; ".join(rows2[:2]))

# ---------------------------------------------------------------------------------------------------------------------
# 3. a protected subsystem: Phi = id_A x R_B


def reset_B_kraus(dA, dB):
    return [np.kron(np.eye(dA), np.outer(np.eye(dB)[i], np.eye(dB)[j])) / math.sqrt(dB) for i in range(dB) for j in range(dB)]


def L_of(ch, rho, dA, dB):
    """Objective of L at rho: Tr rho D + kT[S(rho_B) - ln d_B]."""
    from qtools import S
    rb = np.trace(rho.reshape(dA, dB, dA, dB), axis1=0, axis2=2)
    return float(np.real(np.trace(rho @ ch.D))) + (S(rb) - math.log(dB)) / ch.beta


ok3, rows3 = True, []
for trial in range(6):
    dA, dB = 2, 2
    beta = rng.uniform(0.4, 2)
    if trial % 2 == 0:
        H = np.kron(herm(rng.standard_normal((dA, dA))), np.eye(dB)) + np.kron(np.eye(dA), herm(rng.standard_normal((dB, dB))))
    else:
        H = herm(rng.standard_normal((dA * dB, dA * dB)) + 1j * rng.standard_normal((dA * dB, dA * dB)))
    ch = Channel(reset_B_kraus(dA, dB), H, beta)
    lo, up, sg, _ = batch_cost_smooth(ch)
    clo, cup, _ = capacity(ch)
    # B = L: the optimal pair has sigma_B = rho_B, so L(rho) >= B; and (rho, rho_A x rho_B) is feasible, so L <= B
    from qtools import inner_sdp
    _, rh, _ = inner_sdp(ch, sg)
    Lr = L_of(ch, rh, dA, dB)
    ok3 &= lo - 1e-6 <= Lr <= up + 1e-6
    if trial % 2 == 0:
        ok3 &= abs(lo - clo) < 1e-6 and abs(up - cup) < 1e-5 and covariance_defect(ch) < 1e-10
    else:
        ok3 &= cup < lo - 1e-4 and covariance_defect(ch) > 1e-3
    rows3.append(f"{'additive' if trial % 2 == 0 else 'non-additive'}: B in [{lo:.5f}, {up:.5f}], capacity {clo:.5f}")
R.check("id_A x R_B: B = L; covariant and L = capacity for additive H; not covariant and L > capacity for "
        "non-additive H", ok3,
        "; ".join(rows3[:2]))

phip = np.array([1, 0, 0, 1]) / math.sqrt(2)
ok3b, rows3b = True, []
for E, beta in ((1.0, math.log(2)), (1.0, 0.3), (2.0, 1.0), (1.0, 5.0)):
    Hbell = E * (np.eye(4) - dm(phip))
    ch = Channel(reset_B_kraus(2, 2), Hbell, beta)
    ok3b &= opnorm(ch.phistar(Hbell) - 0.75 * E * np.eye(4)) < 1e-12
    lo, up, _, _ = batch_cost_smooth(ch)
    ok3b &= abs(lo - 0.75 * E) < 1e-6 and abs(up - 0.75 * E) < 1e-6
    # L attained at rho = Phi+: Tr rho D = 3E/4 and S(rho_B) = ln 2
    ok3b &= abs(np.real(np.trace(dm(phip) @ ch.D)) - 0.75 * E) < 1e-12
    clo, cup, _ = capacity(ch)
    formula = -E / 4 + math.log((math.exp(beta * E) + 3) / 4) / beta
    ok3b &= abs(clo - formula) < 1e-7 and abs(cup - formula) < 1e-6
    for _ in range(5):
        out = ch.phi(random_density(4, rng, rank=1))
        ok3b &= np.sum(np.linalg.eigvalsh(out) > 1e-9) >= 2
    rows3b.append(f"beta E = {beta * E:.3f}: capacity {clo / E:.5f} E")
ok3b &= round(-0.25 + math.log(5 / 4) / math.log(2), 3) == 0.072
R.check("Bell example: Phi^*(H) = (3/4)E I, B = 3E/4 at every temperature (attained at Phi+), capacity "
        "-E/4 + beta^{-1} ln[(e^{beta E}+3)/4] = 0.072E at beta E = ln 2, every output mixed", ok3b, "; ".join(rows3b))
# the finite construction for the Bell example: hot qubit with B_hot = H, then swap B with a flat zero-energy cell
ok3c = True
for E, M in ((1.0, 15.0), (1.0, 40.0), (2.0, 25.0)):
    Hbell = E * (np.eye(4) - dm(phip))
    z = 1 / (1 + math.exp(M))
    w_, v_ = np.linalg.eigh(Hbell)
    C0 = (v_ * np.sqrt(1 - w_ / M)) @ dag(v_)
    F0 = (v_ * np.sqrt(w_ / M)) @ dag(v_)
    J = np.block([[C0, -F0], [F0, C0]])                         # G outermost
    for _ in range(5):
        rho = random_density(4, rng)
        gain = 0.0
        for g, pg in ((0, 1 - z), (1, z)):
            st = J @ np.kron(dm(np.eye(2)[g]), rho) @ dag(J)
            eG = M * np.real(np.trace(st[4:, 4:]))
            sAB = st[:4, :4] + st[4:, 4:]
            # swap B with a flat cell: the payload becomes rho_A x I/2, the cell (zero Hamiltonian) keeps B
            rA = np.trace(sAB.reshape(2, 2, 2, 2), axis1=1, axis2=3)
            ePay = np.real(np.trace(Hbell @ np.kron(rA, np.eye(2) / 2)))
            gain += pg * (eG + ePay - np.real(np.trace(Hbell @ rho)) - M * g)
        ok3c &= abs(gain - np.real(np.trace(rho @ (0.75 * E * np.eye(4) - 2 * z * Hbell)))) < 1e-12
R.check("Bell example construction: the gain operator is exactly (3/4)E I - 2zH", ok3c)

# ---------------------------------------------------------------------------------------------------------------------
# 4. Gibbs preservation is not enough
y, e = sp.symbols("y e", positive=True)          # e = exp(-beta E_1) <= 1, x^2 = y^2/e
x = y / sp.sqrt(e)
K0 = sp.diag(sp.sqrt(1 - y ** 2), sp.sqrt(1 - x ** 2), 1)
K1 = sp.Matrix([[0, x, 0], [y, 0, 0], [0, 0, 0]])
g2 = sp.symbols("g2", positive=True)             # exp(-beta E_2)
Zg = 1 + e + g2
gam = sp.diag(1, e, g2) / Zg
ok4 = sp.simplify(K0.T * K0 + K1.T * K1 - sp.eye(3)) == sp.zeros(3)
ok4 &= sp.simplify(K0 * gam * K0.T + K1 * gam * K1.T - gam) == sp.zeros(3)
g0p = 1 / (1 + e)
a_ = 1 / (2 * g0p)
rho = sp.diag(1, 0, 0)
sig = sp.diag(a_ * g0p, a_ * (1 - g0p), 1 - a_)
Ks = [K0, K1]
psi = lambda m: sp.Matrix(2, 2, lambda i, j: (Ks[i] * m * Ks[j].T).trace())
ok4 &= sp.simplify(psi(rho) - sp.diag(1 - y ** 2, y ** 2)) == sp.zeros(2)
ok4 &= sp.simplify(psi(sig) - sp.diag(1 - y ** 2, y ** 2)) == sp.zeros(2)
ok4 &= sp.simplify(K0 * sig * K0.T + K1 * sig * K1.T - sig) == sp.zeros(3)
E1, E2 = sp.symbols("E1 E2", positive=True)
Hs = sp.diag(0, E1, E2)
Dsym = K0.T * Hs * K0 + K1.T * Hs * K1 - Hs
ok4 &= sp.simplify((rho * Dsym).trace() - y ** 2 * E1) == 0
ok4 &= sp.simplify(sig[2, 2] - (1 - e) / 2) == 0                     # sigma is a state exactly when e <= 1
R.check("GP qutrit (symbolic in y, e = e^{-beta E_1}, e^{-beta E_2}): completeness, Gibbs preservation, "
        "Psi(|0><0|) = Psi(sigma) = diag(1 - y^2, y^2), Phi(sigma) = sigma, Tr rho D = y^2 E_1, and a = 1/(2 gamma_0') <= 1",
        bool(ok4))
ok4b, rows4 = True, []
for yv, bE1, E2v in ((0.5, math.log(2), 1.3), (0.3, 1.0, 2.0), (0.6, 0.2, 0.9)):
    xv = yv * math.exp(bE1 / 2)
    Hn = np.diag([0.0, bE1, E2v]).astype(complex)
    Kn = [np.diag([math.sqrt(1 - yv ** 2), math.sqrt(1 - xv ** 2), 1]).astype(complex),
          np.array([[0, xv, 0], [yv, 0, 0], [0, 0, 0]], dtype=complex)]
    ch = Channel(Kn, Hn, 1.0)
    # the supergradient engine (the optimum of g_Y sits near the boundary here, which slows the smoothed dual)
    lo, up, _, _ = batch_cost(ch, iters=300)
    clo, cup, _ = capacity(ch)
    ok4b &= lo >= yv ** 2 * bE1 - 1e-7 and up >= lo - 1e-7 and abs(clo) < 1e-7 and cup < 1e-5 and covariance_defect(ch) > 1e-3
    rows4.append(f"y = {yv}: B in [{lo:.5f}, {up:.5f}] >= y^2 E_1 = {yv ** 2 * bE1:.5f}")
R.check("GP qutrit numerically: not covariant, capacity 0, and B >= y^2 E_1", ok4b, "; ".join(rows4))

# ---------------------------------------------------------------------------------------------------------------------
# 5. a Gibbs-preserving channel that reaches its capacity
r3 = sp.sqrt(3)
s0 = sp.Matrix([[sp.Rational(3, 4), r3 / 12], [r3 / 12, sp.Rational(1, 4)]])
s1 = sp.Matrix([[sp.Rational(3, 4), -r3 / 4], [-r3 / 4, sp.Rational(1, 4)]])
gq = sp.diag(sp.Rational(3, 4), sp.Rational(1, 4))
ok5 = s0.trace() == 1 and s1.trace() == 1 and sp.simplify(s0.det() - sp.Rational(1, 6)) == 0 and sp.simplify(s1.det()) == 0
ok5 &= sp.simplify(sp.Rational(3, 4) * s0 + sp.Rational(1, 4) * s1 - gq) == sp.zeros(2)
ok5 &= s0[0, 0] == gq[0, 0] and s1[0, 0] == gq[0, 0]                 # Delta o Phi = gamma Tr
ok5 &= sp.simplify(s0 * sp.diag(0, 1) - sp.diag(0, 1) * s0) != sp.zeros(2)
R.check("sigma_0, sigma_1 are states (det 1/6 and 0), (3/4)sigma_0 + (1/4)sigma_1 = gamma, both have the populations "
        "of gamma, and sigma_0 = Phi(|0><0|) does not commute with H", bool(ok5))
E = 1.0
beta = math.log(3) / E
Hq = np.diag([0.0, E]).astype(complex)
S0, S1 = np.array(s0.evalf(), dtype=complex), np.array(s1.evalf(), dtype=complex)
phiR = lambda r: r[0, 0] * S0 + r[1, 1] * S1
KR = kraus_from_choi(choi_of(phiR, 2), 2, 2)
chR = Channel(KR, Hq, beta)
gqn = np.diag([0.75, 0.25]).astype(complex)
ok5b = opnorm(chR.phi(gqn) - gqn) < 1e-12 and chR.tp_error() < 1e-12
for _ in range(50):
    rho = random_density(2, rng)
    dlt = np.diag(np.diag(rho))
    ok5b &= opnorm(chR.phi(dlt) - chR.phi(rho)) < 1e-12 and opnorm(np.diag(np.diag(chR.phi(rho))) - gqn) < 1e-12
    ok5b &= relent(chR.phi(rho), gqn) <= relent((1 - 1e-12) * rho + 1e-12 * np.eye(2) / 2, gqn) + 1e-9
clo, cup, _ = capacity(chR)
lo, up, _, _ = batch_cost_smooth(chR)
ok5b &= abs(clo) < 1e-7 and abs(lo) < 1e-6 and abs(up) < 1e-6 and covariance_defect(chR) > 1e-2
R.check("the channel is Gibbs-preserving, Phi o Delta = Phi, Delta o Phi = gamma Tr, F(Phi rho) <= F(rho), not "
        "covariant, capacity 0 and B = 0", bool(ok5b), f"B in [{lo:.1e}, {up:.1e}]")
# Psi(rho_AD) = gamma_A (x) Phi(rho_A)_D on A (energy H) and D (zero Hamiltonian)
def psiAD(r):
    rA = np.trace(r.reshape(2, 2, 2, 2), axis1=1, axis2=3)
    return np.kron(gqn, phiR(rA))
KAD = kraus_from_choi(choi_of(psiAD, 4), 4, 4)
HAD_ = np.kron(Hq, np.eye(2))
chAD = Channel(KAD, HAD_, beta)
cap_lo, cap_up, cap_s = capacity(chAD)
aval = E * (0.75 - math.log(2) / math.log(3))
Es = sp.symbols("E", positive=True)
Sg = -(sp.Rational(3, 4) * sp.log(sp.Rational(3, 4)) + sp.Rational(1, 4) * sp.log(sp.Rational(1, 4)))
ok5c = sp.simplify((sp.log(2) - Sg) / (sp.log(3) / Es) - Es * (sp.Rational(3, 4) - sp.log(2) / sp.log(3))) == 0
ok5c &= abs(cap_lo - aval) < 1e-7 and abs(cap_up - aval) < 1e-6 and round(aval, 3) == 0.119 and covariance_defect(chAD) < 1e-10
ok5c &= opnorm(cap_s - np.kron(gqn, np.eye(2) / 2)) < 1e-4
R.check("Psi = gamma_A (x) Phi(.)_D is time-covariant with capacity a = beta^{-1}[ln 2 - S(gamma)] = E(3/4 - ln2/ln3) "
        "= 0.119E, attained at gamma (x) I/2", bool(ok5c), f"capacity in [{cap_lo:.7f}, {cap_up:.7f}], a = {aval:.7f}")
# Stage 2 swap |a>_A |z>_D |j>_C -> |z>_A |a>_D |j + |a| - |z|>_C on a finite ladder, identity off the ladder
ok5d = True
for n in (1, 2, 3):
    for Lc in (2, 3, 5):
        top = 2 * n + Lc
        states = [(a, z, j) for a in itertools.product((0, 1), repeat=n) for z in itertools.product((0, 1), repeat=n)
                  for j in range(top)]
        def f(s):
            a, z, j = s
            t = (z, a, j + sum(a) - sum(z))
            return t if 0 <= t[2] < top else s
        img = [f(s) for s in states]
        ok5d &= len(set(img)) == len(states) and all(f(f(s)) == s for s in states)
        ok5d &= all(sum(s[0]) + s[2] == sum(t[0]) + t[2] for s, t in zip(states, img))
        # starting levels n .. n+L-1 never leave the ladder
        ok5d &= all(0 <= s[2] + sum(s[0]) - sum(s[1]) < top for s in states if n <= s[2] < n + Lc)
R.check("Stage 2: |a,z,j> -> |z,a,j+|a|-|z|> (identity off the ladder) is an energy-conserving permutation, and from "
        "levels n..n+L-1 of a ladder of 2n+L levels it never leaves the ladder", ok5d)
pa = {1: sp.Rational(3, 16), 0: sp.Rational(5, 8), -1: sp.Rational(3, 16)}
ga = [sp.Rational(3, 4), sp.Rational(1, 4)]
inc = {}
for a in (0, 1):
    for z in (0, 1):
        inc[a - z] = inc.get(a - z, 0) + ga[a] * ga[z]
varH = sum(g * h ** 2 for g, h in zip(ga, (0, 1))) - sum(g * h for g, h in zip(ga, (0, 1))) ** 2
ok5e = inc == pa and sum(k * p for k, p in inc.items()) == 0 and sum(k * k * p for k, p in inc.items()) == sp.Rational(3, 8)
ok5e &= 2 * varH == sp.Rational(3, 8)
worst = 0.0
for n in (1, 2, 5, 20, 100):
    dist = {0: sp.Integer(1)}
    for _ in range(n):
        new = {}
        for k, p in dist.items():
            for s, q in inc.items():
                new[k + s] = new.get(k + s, 0) + p * q
        dist = new
    ok5e &= sum(k * k * p for k, p in dist.items()) == sp.Rational(3 * n, 8)
    EK = float(sum(abs(k) * p for k, p in dist.items()))
    for Lc in (n + 1, 4 * n, 50 * n):
        exact = float(sum(p * sp.sqrt(1 - (1 - sp.Rational(abs(k), Lc)) ** 2) for k, p in dist.items() if abs(k) <= Lc))
        bound = math.sqrt(2 * EK / Lc)
        ok5e &= exact <= bound + 1e-12 and bound <= math.sqrt(2 * math.sqrt(3 * n / 8) / Lc) + 1e-12
        worst = max(worst, exact / bound)
    for eps in (0.5, 0.1, 0.03):
        Lc = math.ceil(2 * math.sqrt(3 * n / 8) / eps ** 2)
        ok5e &= math.sqrt(2 * math.sqrt(3 * n / 8) / Lc) <= eps + 1e-12
Lc = 7
chi = np.ones(Lc) / math.sqrt(Lc)
ok5e &= all(abs(np.dot(chi[:Lc - k], chi[k:]) - max(0, 1 - k / Lc)) < 1e-12 for k in range(Lc + 2) if k <= Lc)
R.check("clock increments +-1 w.p. 3/16 and 0 w.p. 5/8, mean 0, E K^2 = 3n/8 = 2n Var_gamma(H)/E^2 (exact); the "
        "uniform clock has overlap max(0, 1-|k|/L) with its translate; the return distance is at most "
        "sqrt(2 E|K|/L) <= sqrt(2 sqrt(3n/8)/L) <= eps for L >= 2 sqrt(3n/8)/eps^2", bool(ok5e),
        f"exact distance reaches {worst:.3f} of sqrt(2E|K|/L)")
g0, g1, c0, c1 = sp.symbols("g0 g1 c0 c1", real=True)
fam_c1 = sp.solve(sp.Eq(g0 * c0 + g1 * c1, 0), c1)[0]
ok5f = sp.simplify(fam_c1 + g0 / g1 * c0) == 0
c1e = -sp.sqrt(sp.Rational(3, 4) * sp.Rational(1, 4))
c0e = sp.simplify(-sp.Rational(1, 4) / sp.Rational(3, 4) * c1e)
ok5f &= sp.simplify(c1e + r3 / 4) == 0 and sp.simplify(c0e - r3 / 12) == 0
R.check("qubit family: Gibbs preservation forces c_1 = -(gamma_0/gamma_1) c_0; its extreme point |c_1|^2 = gamma_0 "
        "gamma_1 is c_1 = -sqrt3/4, c_0 = sqrt3/12 (sigma_1 pure), the channel of the proposition", bool(ok5f))
R.close()
