"""The batch law (Section "Batch with a returned clock", Appendices "The single-letter bound", "A returned clock reaches
the capacity", "The batch law", and Appendix "Physical construction for the batch law and the noise horizon").

Checks:
  1. conventions: Tr Psi(rho) Y = Tr rho Psi^*(Y), range Psi^* = span{A_i^* A_j}, and V^*(H + K)V = Phi^*(H) + Psi^*(K),
     so D is in the range exactly when some environment Hamiltonian makes the dilation conserve mean energy;
  2. B(Phi) from both sides (primal pairs and dual Y) on random channels: weak duality for arbitrary Y, a small gap at
     the optimum, B >= capacity with equality for balanced channels (generic qubit channels, covariant channels,
     unitaries) and strict inequality for generic unbalanced qutrit channels;
  3. B(Phi x Phi) = 2 B(Phi) for partial X-dephasing, and subadditivity of the entropy decrease;
  4. Proposition "single" (c): Gibbs-preserving qubit channels are balanced, a Gibbs-preserving qubit channel whose
     complement has a traceless kernel is unital and phase-covariant, and an unbalanced Gibbs-preserving channel has
     B > 0 through rho = gamma +- tX; in the proof of Theorem "balanced" the environment carries
     D(omega_OF || omega_O x gamma_F) = ln Z_F + beta[F(rho) - F(Phi rho)];
  5. Lemma "Active-dimension continuity" and the constants of Proposition "Actual-budget finite-error lower bound";
  6. the faithful auxiliary balance: stationarity, V_n^*(H_O' + H_E)V_n = H_in' + aI, V_n^*R = 0, the bounds on the
     logarithms and on ||R||, ||R^(n)|| <= sqrt(n)||R||, and the conditional free energy >= lambda_max(Y) - g_Y on
     entangled inputs;
  7. the kernel k: normalization, Fourier support [-1, 1], int |s| k = 12 ln2/pi; and, at small N, the exact test
     inequalities (Duhamel, pinching, the weighted partial-trace certificates) of the uniform test; the shell count
     (n+1)^K and the entropy budget h(p) + p ln(dim - 1) of a nearly pure block;
  8. the decoder: the Hayashi-Nagaoka inequality, the contraction D_dec, the Halmos square, overlap bounds;
  9. the mechanical factory: source and target counts, the stock partition function, the bad-tile probability,
     energy conservation of every pair, and the rounding of the nominal work; the fallback constant c >= 0;
 10. the rare excitation: the exact gain w_0 I + E_n, ||E_n|| <= chi_n, w_0 >= 0, and the disturbance 3||B||/(2M);
 11. the bank: the lift is a unital *-homomorphism that conserves energy; the sine packet's phase law; k_front.
"""
from math import comb
import math

import numpy as np
import sympy as sp

from qtools import (Channel, Report, S, X, batch_cost, batch_cost_smooth, capacity, choi_of, dag, diamond_half, dm, dual_value, expm_h,
                    fidelity, gmax, herm, kraus_from_choi, logm_h, opnorm, powm_h, primal_value, random_density,
                    random_unitary, relent, span_residual, trace_norm)

R = Report("The batch law")
rng = np.random.default_rng(20261014)


def random_channel(d, r, rng):
    g = rng.standard_normal((d * r, d)) + 1j * rng.standard_normal((d * r, d))
    q, _ = np.linalg.qr(g)
    return [q.reshape(d, r, d)[:, k, :] for k in range(r)]


def random_gp_channel(d, H, beta, rng):
    """An extreme-ish Gibbs-preserving channel: a random linear functional maximized over the Gibbs-preserving set."""
    import cvxpy as cp
    g = np.exp(-beta * np.real(np.diag(H)))
    gam = np.diag(g / g.sum())
    J = cp.Variable((d * d, d * d), hermitian=True)
    Rm = herm(rng.standard_normal((d * d, d * d)) + 1j * rng.standard_normal((d * d, d * d)))
    cons = [J >> 0, cp.partial_trace(J, [d, d], axis=1) == np.eye(d),
            cp.partial_trace(cp.kron(gam.T, np.eye(d)) @ J, [d, d], axis=0) == gam]
    cp.Problem(cp.Maximize(cp.real(cp.trace(Rm @ J))), cons).solve(solver="CLARABEL")
    K = kraus_from_choi(np.asarray(J.value), d, d, tol=1e-7)
    s = sum(dag(k) @ k for k in K)
    w, v = np.linalg.eigh(s)
    K = [k @ (v * w ** -0.5) @ dag(v) for k in K]
    return K, gam


# ---------------------------------------------------------------------------------------------------------------------
# 1. conventions
ok1 = True
for trial in range(100):
    d, r = int(rng.integers(2, 4)), int(rng.integers(1, 4))
    ch = Channel(random_channel(d, r, rng), herm(rng.standard_normal((d, d))))
    rho = random_density(d, rng)
    Yh = herm(rng.standard_normal((r, r)) + 1j * rng.standard_normal((r, r)))
    ok1 &= abs(np.trace(ch.psi(rho) @ Yh) - np.trace(rho @ ch.psistar(Yh))) < 1e-12
    ok1 &= span_residual(ch.psistar(Yh), ch.products()) < 1e-10
    lhs = dag(ch.V) @ (np.kron(ch.H, np.eye(r)) + np.kron(np.eye(d), Yh)) @ ch.V
    ok1 &= opnorm(lhs - ch.phistar(ch.H) - ch.psistar(Yh)) < 1e-12
R.check("Tr Psi(rho) Y = Tr rho Psi^*(Y); Psi^*(Y) lies in span{A_i^* A_j}; V^*(H (x) I + I (x) K)V = Phi^*(H) + Psi^*(K)",
        ok1)

# ---------------------------------------------------------------------------------------------------------------------
# 2. B from both sides
E = 1.0
Hq = np.diag([0.0, E]).astype(complex)
H3 = np.diag([0.0, 0.7, 1.6]).astype(complex)
rows, ok2, ok_weak = [], True, True
cases = []
for i in range(3):
    cases.append(("random qubit channel, Kraus rank 2 (balanced)", Channel(random_channel(2, 2, rng), Hq, beta=1.0), True))
for i in range(3):
    cases.append(("random qutrit channel, Kraus rank 2 (unbalanced)", Channel(random_channel(3, 2, rng), H3, beta=1.0), False))
gam_ = 0.4
cases.append(("amplitude damping (covariant)", Channel([np.array([[1, 0], [0, math.sqrt(1 - gam_)]]),
                                                        np.array([[0, math.sqrt(gam_)], [0, 0]])], Hq, beta=1.3), True))
from qtools import HAD
cases.append(("Hadamard gate (unitary)", Channel([HAD], Hq, beta=0.7), None))
for name, ch, balanced in cases:
    res = ch.balance_residual()
    lo, up, sig, Yopt = batch_cost_smooth(ch)
    clo, cup, _ = capacity(ch)
    # weak duality for arbitrary Y
    for _ in range(5):
        Yr = herm(rng.standard_normal((ch.r, ch.r)) + 1j * rng.standard_normal((ch.r, ch.r)))
        ok_weak &= dual_value(ch, Yr)[0] >= lo - 1e-8
    gap = up - lo
    if balanced:
        ok2 &= res < 1e-8 and abs(lo - clo) < 1e-6 and up - cup < 1e-6
    elif balanced is None:                  # a gate: unbalanced (span{A^*A} = span{I}), yet B = capacity
        ok2 &= res > 0.5 and abs(lo - clo) < 1e-6 and up - cup < 1e-6
    else:
        ok2 &= res > 1e-3 and lo > cup + 1e-3
    ok2 &= abs(gap) < 1e-6
    if name.startswith("random qutrit"):
        # second engine: supergradient ascent on sigma with the inner SDP, dual iterates averaged
        lo2_, up2_, _, _ = batch_cost(ch, iters=600)
        ok2 &= lo2_ <= up + 1e-7 and up2_ >= lo - 1e-7 and up2_ - lo2_ < 5e-4
    rows.append(f"{name}: B in [{lo:.6f}, {up:.6f}], capacity {clo:.6f}")
R.check("weak duality: B(Phi) <= t_Y + g_Y for random Y", ok_weak)
R.check("B(Phi) from both sides agrees to 1e-6, and a second engine (supergradient ascent) agrees; B = capacity for balanced channels (generic qubit channels of Kraus "
        "rank 2, a covariant channel), B > capacity for generic qutrit channels of Kraus rank 2, and B = capacity for a "
        "gate, which is unbalanced (its Kraus products span only I)", ok2,
        "; ".join(rows[::2]))
had = cases[-1][1]
R.check("for a unitary every input leaves the environment unchanged and B = capacity = lambda_max(D) = E/sqrt2",
        abs(batch_cost_smooth(had)[0] - E / math.sqrt(2)) < 1e-6)

# 3. additivity on partial X-dephasing (unbalanced) and subadditivity of the entropy decrease
p = 0.2
pd = Channel([math.sqrt(1 - p) * np.eye(2), math.sqrt(p) * X], Hq, beta=1.0)
lo1, up1, _, _ = batch_cost_smooth(pd)
K2 = [np.kron(a, b) for a in pd.K for b in pd.K]
H2 = np.kron(Hq, np.eye(2)) + np.kron(np.eye(2), Hq)
pd2 = Channel(K2, H2, beta=1.0)
lo2, up2, _, _ = batch_cost_smooth(pd2)
R.check("B(Phi x Phi) = 2 B(Phi) for partial X-dephasing (p = 0.2, entangled inputs allowed)",
        lo2 <= 2 * up1 + 1e-6 and up2 >= 2 * lo1 - 1e-6 and up2 - lo2 < 1e-6,
        f"B(Phi) in [{lo1:.6f}, {up1:.6f}], B(Phi x Phi) in [{lo2:.6f}, {up2:.6f}]")
ok3 = True
for trial in range(300):
    ch = Channel(random_channel(2, int(rng.integers(1, 4)), rng), Hq)
    sig = random_density(4, rng)
    K2 = [np.kron(a, b) for a in ch.K for b in ch.K]
    out = sum(k @ sig @ dag(k) for k in K2)
    s1 = np.einsum("aibj->ab", sig.reshape(2, 2, 2, 2).transpose(0, 1, 2, 3)) if False else np.trace(sig.reshape(2, 2, 2, 2), axis1=1, axis2=3)
    s2 = np.trace(sig.reshape(2, 2, 2, 2), axis1=0, axis2=2)
    ok3 &= S(sig) - S(out) <= ch.h(s1) + ch.h(s2) + 1e-10
R.check("S(sigma_12) - S(Phi x Phi sigma_12) <= sum_i [S(sigma_i) - S(Phi sigma_i)] (300 random two-qubit inputs)", ok3)

# ---------------------------------------------------------------------------------------------------------------------
# 4. Gibbs-preserving channels
ok4, kern_cases = True, 0
for trial in range(25):
    beta = rng.uniform(0.3, 2.5)
    K, gam = random_gp_channel(2, Hq, beta, rng)
    ch = Channel(K, Hq, beta)
    ok4 &= opnorm(ch.phi(gam) - gam) < 1e-6 and (ch.balance_residual() < 1e-5 or opnorm(ch.D) < 1e-6)
    ker = [x for x in ch.psi_kernel_hermitian(tol=1e-7) if abs(np.trace(x)) < 1e-8]
    if ker:
        kern_cases += 1
        ok4 &= opnorm(ch.phi(np.eye(2)) - np.eye(2)) < 1e-5                       # unital
        for t in (0.3, 1.1, 2.0):
            Ut = np.diag([1, np.exp(-1j * E * t)])
            rr = random_density(2, rng)
            ok4 &= opnorm(ch.phi(Ut @ rr @ dag(Ut)) - Ut @ ch.phi(rr) @ dag(Ut)) < 1e-5   # phase covariant
# diagonal unitaries and their mixtures (dephasing) are Gibbs-preserving and have a traceless kernel of Psi
for trial in range(10):
    ks = int(rng.integers(1, 4))
    pk = rng.dirichlet(np.ones(ks))
    ch = Channel([math.sqrt(pk[j]) * np.diag(np.exp(1j * rng.uniform(0, 6, 2))) for j in range(ks)], Hq, 1.0)
    ker = [x for x in ch.psi_kernel_hermitian() if abs(np.trace(x)) < 1e-8]
    kern_cases += bool(ker)
    ok4 &= bool(ker) and opnorm(ch.phi(np.eye(2)) - np.eye(2)) < 1e-12
R.check("every Gibbs-preserving qubit channel is balanced (25 extreme points of the Gibbs-preserving set); when Psi "
        "kills a traceless X the channel is unital and phase-covariant", ok4, f"{kern_cases} channels with such a kernel")
# the qutrit channel N of Proposition "arrow" is Gibbs-preserving and unbalanced: rho = gamma +- tX gives B > 0
a_, b_ = math.log(1.5), math.log(3.0)
H_N = np.diag([0, a_, b_]).astype(complex)
pl, mi, tw = np.array([1, 1, 0]) / math.sqrt(2), np.array([1, -1, 0]) / math.sqrt(2), np.array([0, 0, 1.0])
KN = [amp * np.outer(np.eye(3)[i], v) for i, v, amp in
      [(0, pl, 1.0), (0, tw, math.sqrt(.5)), (1, mi, math.sqrt(.8)), (2, mi, math.sqrt(.2)), (2, tw, math.sqrt(.5))]]
chN = Channel(KN, H_N, 1.0)
gN = np.diag([0.5, 1 / 3, 1 / 6]).astype(complex)
Xk = [x for x in chN.psi_kernel_hermitian() if abs(np.trace(x @ chN.D)) > 1e-6][0]
tmax = 1 / (2 * opnorm(Xk) / np.min(np.linalg.eigvalsh(gN)))
best = max(np.real(np.trace((gN + sg * tmax * Xk) @ chN.D)) for sg in (1, -1))
R.check("unbalanced and Gibbs-preserving: some X in ker Psi has Tr XD != 0, and rho = gamma +- tX, sigma = gamma give "
        "B > 0 (qutrit N)", best > 1e-3 and opnorm(chN.psi(Xk)) < 1e-10, f"objective {best:.4f}")

# proof of Theorem "balanced": with V^*(H + K)V = H the environment carries D(omega_OF||gamma_F x omega_O) = ln Z_F + q(rho)
ok4c = True
for trial in range(20):
    ch = Channel(random_channel(2, 2, rng), Hq, beta=rng.uniform(0.3, 2))
    from qtools import hermitian_basis
    hb = hermitian_basis(ch.r)
    target = herm(ch.H - ch.phistar(ch.H))
    A = np.array([np.concatenate([np.real(ch.psistar(B)).ravel(), np.imag(ch.psistar(B)).ravel()]) for B in hb]).T
    coef, *_ = np.linalg.lstsq(A, np.concatenate([np.real(target).ravel(), np.imag(target).ravel()]), rcond=None)
    K = herm(sum(c * B for c, B in zip(coef, hb)))
    ok4c &= opnorm(dag(ch.V) @ (np.kron(ch.H, np.eye(ch.r)) + np.kron(np.eye(2), K)) @ ch.V - ch.H) < 1e-10
    wK, vK = np.linalg.eigh(K)
    ZF = np.sum(np.exp(-ch.beta * wK))
    gF = (vK * (np.exp(-ch.beta * wK) / ZF)) @ dag(vK)
    for _ in range(5):
        rho = random_density(2, rng)
        om = ch.V @ rho @ dag(ch.V)
        # D(omega || Phi(rho) x gamma_F) with the logarithm of the product taken factor by factor,
        # ln gamma_F = -beta K - ln Z_F, which avoids the loss of precision of a matrix logarithm of a near-singular product
        log_prod = np.kron(logm_h(ch.phi(rho)), np.eye(ch.r)) + np.kron(np.eye(2), -ch.beta * K - math.log(ZF) * np.eye(ch.r))
        lhs = -S(om) - float(np.real(np.trace(om @ log_prod)))
        Fr = lambda m: np.real(np.trace(m @ ch.H)) - S(m) / ch.beta
        q = ch.beta * (Fr(rho) - Fr(ch.phi(rho)))
        ok4c &= abs(lhs - (math.log(ZF) + q)) < 1e-8
R.check("proof of Theorem 'balanced': with V^*(H + K)V = H the environment carries D(omega_OF || omega_O x gamma_F) = "
        "ln Z_F + beta[F(rho) - F(Phi rho)] on every input", ok4c)

# ---------------------------------------------------------------------------------------------------------------------
# 5. continuity lemma and the converse constants
xs_ = sp.symbols("x", positive=True)
r0 = (1 + xs_) * sp.log(1 + xs_) - xs_ * sp.log(xs_)
h_ = lambda p_: -p_ * sp.log(p_) - (1 - p_) * sp.log(1 - p_)
R.check("(1+x) h(x/(1+x)) = r0(x) = (1+x)ln(1+x) - x ln x", sp.simplify(sp.expand_log((1 + xs_) * h_(xs_ / (1 + xs_)) - r0, force=True)) == 0)
r0f = lambda x: 0.0 if x <= 0 else (1 + x) * math.log(1 + x) - x * math.log(x)
ok5, near5c, near5u = True, 0, 0
for trial in range(1500):
    dA, dF = int(rng.integers(2, 4)), int(rng.integers(1, 4))
    rho = random_density(dA * dF, rng, rank=int(rng.integers(1, dA * dF + 1)))
    if trial % 3 == 0:     # near the extremal configuration: mix a pure state with a little noise
        sigma = (1 - 10 ** rng.uniform(-3, -0.3)) * dm(np.eye(dA * dF)[0]) + 10 ** rng.uniform(-3, -0.3) * random_density(dA * dF, rng)
        sigma /= np.trace(sigma)
        rho = dm(np.eye(dA * dF)[0])
    else:
        lam = 10 ** rng.uniform(-4, 0)
        sigma = (1 - lam) * rho + lam * random_density(dA * dF, rng)
    x = trace_norm(rho - sigma) / 2
    if x > 1:
        continue
    cond = lambda m: S(m) - S(np.trace(m.reshape(dA, dF, dA, dF), axis1=0, axis2=2))
    margA = lambda m: np.trace(m.reshape(dA, dF, dA, dF), axis1=1, axis2=3)
    lc = abs(cond(rho) - cond(sigma))
    lu = abs(S(margA(rho)) - S(margA(sigma)))
    xa = trace_norm(margA(rho) - margA(sigma)) / 2
    ok5 &= lc <= 2 * x * math.log(dA) + r0f(x) + 1e-10 and lu <= xa * math.log(dA) + r0f(xa) + 1e-10
    near5u += lu > 0.6 * (xa * math.log(dA) + r0f(xa))
R.check("|S(A|F)_rho - S(A|F)_sigma| <= 2x ln d_A + r0(x) and |S(A)_rho - S(A)_sigma| <= x ln d_A + r0(x)",
        ok5 and near5u >= 30, f"{near5u} cases above 60% of the unconditional bound")
ok5b = True
for trial in range(400):
    d = int(rng.integers(2, 5))
    r1, r2 = random_density(d, rng), random_density(d, rng)
    lam = 10 ** rng.uniform(-4, 0)
    r2 = (1 - lam) * r1 + lam * r2
    T = trace_norm(r1 - r2) / 2
    F = fidelity(r1, r2)
    ok5b &= math.sqrt(max(0.0, 1 - F * F)) <= math.sqrt(2 * T) + 1e-10
eps = np.logspace(-12, 0, 2000)
ok5b &= bool(np.all(2 * (2 * eps) ** 0.25 <= 4 * eps ** 0.25))
R.check("purifications can be aligned within sqrt(1 - F^2) <= sqrt(2T), so IF marginals within 2a, a = sqrt(2 eps), "
        "give 2 sqrt(a) = 2(2 eps)^{1/4} <= 4 eps^{1/4} = t", ok5b)

# ---------------------------------------------------------------------------------------------------------------------
# 6. faithful auxiliary balance (beta = 1)
ok6, rows6, resid6 = True, [], 0.0
for trial in range(4):
    d, r = 3, 2
    base = Channel(random_channel(d, r, rng), H3, beta=1.0)
    Yr = herm(rng.standard_normal((r, r)) + 1j * rng.standard_normal((r, r)))
    for n in (1, 3, 10):
        eta = (n + 1) ** -6
        Kn = [math.sqrt(1 - eta) * k for k in base.K] + \
             [math.sqrt(eta / d) * np.outer(np.eye(d)[a], np.eye(d)[b]) for a in range(d) for b in range(d)]
        chn = Channel(Kn, H3, 1.0)
        rp = chn.r
        Yn = np.zeros((rp, rp), dtype=complex)
        Yn[:r, :r] = Yr / (1 - eta)
        Xop = chn.psistar(Yn)
        ok6 &= opnorm(Xop - base.psistar(Yr)) < 1e-12
        pval = float(np.max(np.linalg.eigvalsh(Yn)))
        HE = pval * np.eye(rp) - Yn
        glo, gup, sig = gmax(chn, Xop, iters=200000, tol=1e-16)
        om = chn.phi(sig)
        stat = -logm_h(sig) + chn.phistar(logm_h(om)) + Xop
        ok6 &= opnorm(stat - glo * np.eye(d)) < 1e-5
        resid6 = max(resid6, opnorm(stat - glo * np.eye(d)))
        Hin, HO = -logm_h(sig), -logm_h(om)
        a_val = pval - glo
        lhs = dag(chn.V) @ (np.kron(HO, np.eye(rp)) + np.kron(np.eye(d), HE)) @ chn.V
        ok6 &= opnorm(lhs - Hin - a_val * np.eye(d)) < 1e-5
        Rm = (np.kron(HO, np.eye(rp)) + np.kron(np.eye(d), HE)) @ chn.V - chn.V @ (Hin + a_val * np.eye(d))
        ok6 &= opnorm(dag(chn.V) @ Rm) < 1e-5
        ok6 &= opnorm(logm_h(om)) <= math.log(d / eta) + 1e-9
        ok6 &= opnorm(logm_h(sig)) <= math.log(d / eta) + 2 * opnorm(Xop) + math.log(d) + 1e-9
        CY = 20 * (1 + math.log(d) + opnorm(Yr))
        ok6 &= opnorm(Rm) <= CY * math.log(n + 2)
        # a = Tr H_E Psi_n(sigma_n) - S(E|O), and c = ln Z_E + beta a >= 0
        ok6 &= abs(a_val - (np.real(np.trace(HE @ chn.psi(sig))) - chn.h(sig))) < 1e-6
        ok6 &= math.log(np.sum(np.exp(-np.linalg.eigvalsh(HE)))) + a_val >= -1e-9
        rows6.append(opnorm(Rm) / (CY * math.log(n + 2)))
        if n == 1:
            # tensor residual: R^(2)*R^(2) = sum_i (R*R)_i and the conditional free energy on entangled inputs
            V2 = np.kron(chn.V, chn.V)
            h1 = np.kron(HO, np.eye(rp)) + np.kron(np.eye(d), HE)
            W2 = np.kron(h1, np.eye(d * rp)) + np.kron(np.eye(d * rp), h1)
            Hi2 = np.kron(Hin + a_val * np.eye(d), np.eye(d)) + np.kron(np.eye(d), Hin + a_val * np.eye(d))
            R2 = W2 @ V2 - V2 @ Hi2
            RR = dag(Rm) @ Rm
            ok6 &= opnorm(dag(R2) @ R2 - np.kron(RR, np.eye(d)) - np.kron(np.eye(d), RR)) < 1e-6
            ok6 &= opnorm(R2) <= math.sqrt(2) * opnorm(Rm) + 1e-9
            K2 = [np.kron(k1, k2) for k1 in chn.K for k2 in chn.K]
            ch2 = Channel(K2, np.kron(H3, np.eye(d)) + np.kron(np.eye(d), H3), 1.0)
            HE2 = np.kron(HE, np.eye(rp)) + np.kron(np.eye(rp), HE)
            for _ in range(30):
                v = rng.standard_normal(d * d) + 1j * rng.standard_normal(d * d)
                rho2 = dm(v / np.linalg.norm(v))
                ok6 &= np.real(np.trace(ch2.psi(rho2) @ HE2)) - ch2.h(rho2) >= 2 * a_val - 1e-8
            for _ in range(30):
                rho1 = random_density(d, rng)
                ok6 &= np.real(np.trace(chn.psi(rho1) @ HE)) - chn.h(rho1) >= a_val - 1e-8
R.check("faithful auxiliary balance (eta = (n+1)^-6, n = 1, 3, 10): X = Psi_n^*(Y_n) = Psi^*(Y); stationarity "
        "-ln sigma_n + Phi_n^*(ln omega_n) + beta X = beta g_n I; V_n^*(H_O' + H_E)V_n = H_in' + aI; V_n^*R = 0; "
        "the bounds on ln omega_n, ln sigma_n and ||R|| <= C_Y ln(n+2); a = Tr H_E Psi_n(sigma_n) - S(E|O)/beta and "
        "ln Z_E + beta a >= 0; R^(2)*R^(2) = sum_i (R*R)_i; conditional free energy >= a per use on entangled inputs",
        ok6, f"largest ||R||/(C_Y ln(n+2)) = {max(rows6):.3f}, stationarity residual <= {resid6:.1e}")

# ---------------------------------------------------------------------------------------------------------------------
# 7. the kernel and the uniform test
import mpmath as mp
mp.mp.dps = 30
k_fun = lambda s_: mp.mpf(3) / (8 * mp.pi) * (mp.sinc(s_ / 4)) ** 4
mp.mp.dps = 20
norm = 2 * mp.quad(k_fun, mp.linspace(0, 8000, 2001)) + 2 * mp.quad(k_fun, [8000, mp.inf])
first = 2 * mp.quad(lambda s_: s_ * k_fun(s_), mp.linspace(0, 8000, 2001)) + 2 * mp.quad(lambda s_: s_ * k_fun(s_), [8000, mp.inf])


def IH4(x):
    if x <= 0 or x >= 4:
        return 0.0
    return sum((-1) ** k * comb(4, k) * (x - k) ** 3 for k in range(int(np.floor(x)) + 1)) / 6.0


def khat(nu, w=1.0):
    return IH4(2 * nu / w + 2) / IH4(2.0)


num_hat = [float(mp.quad(lambda s_: k_fun(s_) * mp.cos(nu * s_), mp.linspace(0, 400, 201))) * 2 for nu in (0.0, 0.3, 0.7, 0.95)]
R.check("k(s) = (3/(8 pi)) [sin(s/4)/(s/4)]^4: int k = 1, int |s| k = 12 ln2/pi, and its Fourier transform is the "
        "Irwin-Hall profile supported in [-1, 1]",
        abs(norm - 1) < 1e-9 and abs(first - 12 * mp.log(2) / mp.pi) < 1e-6
        and all(abs(a - khat(nu)) < 2e-4 for a, nu in zip(num_hat, (0.0, 0.3, 0.7, 0.95)))
        and khat(1.0) == 0 and khat(1.5) == 0, f"int k - 1 = {mp.nstr(norm - 1, 3)}, int|s|k = {mp.nstr(first, 12)}")


def kron_all(ops):
    out = np.array([[1.0 + 0j]])
    for o in ops:
        out = np.kron(out, o)
    return out


def groups(evals, U, tol=1e-8):
    order = np.argsort(evals)
    ev, Us = evals[order], U[:, order]
    out, start = [], 0
    for i in range(1, len(ev) + 1):
        if i == len(ev) or ev[i] - ev[i - 1] > tol:
            out.append(Us[:, start:i])
            start = i
    return out


def pinch(M, gs):
    return sum(B @ dag(B) @ M @ B @ dag(B) for B in gs)


def wtrace_E(Mm, N, dO, dE, Gam):
    GN = kron_all([Gam] * N)
    T = Mm.reshape([dO, dE] * N + [dO, dE] * N)
    perm = [2 * i for i in range(N)] + [2 * i + 1 for i in range(N)]
    perm = perm + [2 * N + q for q in perm]
    T = T.transpose(perm).reshape(dO ** N, dE ** N, dO ** N, dE ** N)
    return np.einsum("aibj,ji->ab", T, GN)


ok7, rows7 = True, []
chT = Channel(random_channel(3, 2, rng), H3, beta=1.0)
_, _, _, Ysad = batch_cost(chT, iters=100)
for (N, w, alpha, theta, Yc) in [(1, 1.0, 1e-3, 1e-3, Ysad), (2, 1.0, 1e-3, 1e-3, Ysad), (2, 3.0, 1e-4, 1e-4, Ysad),
                                  (2, 1.5, 1e-3, 1e-3, np.array([[0.3, 0.2 - 0.1j], [0.2 + 0.1j, -0.4]]))]:
    d, r = chT.d, chT.r
    glo, gup, sig = gmax(chT, chT.psistar(Yc), iters=200000, tol=1e-16)
    lam = float(np.max(np.linalg.eigvalsh(Yc)))
    HE = lam * np.eye(r) - Yc
    a_val = lam - glo
    Hin, HO = -logm_h(sig), -logm_h(chT.phi(sig))
    V = chT.V
    hout = np.kron(HO, np.eye(r)) + np.kron(np.eye(d), HE)
    Rm = hout @ V - V @ (Hin + a_val * np.eye(d))
    Vb = kron_all([V] * N)
    Hout = sum(kron_all([hout if j == i else np.eye(d * r) for j in range(N)]) for i in range(N))
    Hint = sum(kron_all([Hin if j == i else np.eye(d) for j in range(N)]) for i in range(N))
    Rb = Hout @ Vb - Vb @ (Hint + N * a_val * np.eye(d ** N))
    ok7 &= opnorm(Rb) <= math.sqrt(N) * opnorm(Rm) + 1e-9
    bo, Uo = np.linalg.eigh(Hout)
    bi, Ui = np.linalg.eigh(Hint)
    Kmat = np.array([[khat(bo[x] - bi[y] - N * a_val, w) for y in range(len(bi))] for x in range(len(bo))])
    A = Uo @ (Kmat * (dag(Uo) @ Vb @ Ui)) @ dag(Ui)
    deltaA = opnorm(A - Vb)
    ok7 &= opnorm(A) <= 1 + 1e-9 and deltaA <= 12 * math.sqrt(N) * opnorm(Rm) / (math.pi * w) + 1e-9
    gm = groups(bo, Uo)
    nu_m = len(gm)
    PA = herm(pinch(A @ dag(A), gm))
    ok7 &= np.min(np.linalg.eigvalsh(nu_m * PA - A @ dag(A))) > -1e-9            # pinching inequality
    ev, U = np.linalg.eigh(PA)
    Q = U[:, ev >= alpha] @ dag(U[:, ev >= alpha])
    I = np.eye(Q.shape[0])
    ok7 &= opnorm((I - Q) @ A) <= math.sqrt(nu_m * alpha) + 1e-9
    wE, UE = np.linalg.eigh(HE)
    Gam = UE @ np.diag(np.exp(-wE)) @ dag(UE)
    LQ = float(np.max(np.linalg.eigvalsh(herm(wtrace_E(Q, N, d, r, Gam)))))
    b8 = math.exp(-(N * a_val - w)) / alpha
    ok7 &= LQ <= b8 * (1 + 1e-9)
    hphys = np.kron(chT.H, np.eye(r)) + np.kron(np.eye(d), HE)
    Hphys = sum(kron_all([hphys if j == i else np.eye(d * r) for j in range(N)]) for i in range(N))
    bp_, Up_ = np.linalg.eigh(Hphys)
    gp = groups(bp_, Up_)
    Zp = herm(pinch(Q, gp))
    ev2, U2 = np.linalg.eigh(Zp)
    P = U2[:, ev2 >= theta] @ dag(U2[:, ev2 >= theta])
    ok7 &= opnorm(P @ Hphys - Hphys @ P) < 1e-8
    ok7 &= opnorm((I - P) @ Q) ** 2 <= len(gp) * theta + 1e-9
    LP = float(np.max(np.linalg.eigvalsh(herm(wtrace_E(P, N, d, r, Gam)))))
    ok7 &= LP <= b8 / theta * (1 + 1e-9)
    kap = (deltaA + math.sqrt(nu_m * alpha) + math.sqrt(len(gp) * theta)) ** 2
    acc = min(np.real(np.trace(P @ Vb @ dm(v / np.linalg.norm(v)) @ dag(Vb)))
              for v in [rng.standard_normal(d ** N) + 1j * rng.standard_normal(d ** N) for _ in range(30)])
    ok7 &= acc >= 1 - kap - 1e-9
    rows7.append(f"N={N}: delta_A {deltaA:.3f}, Tr_E[Gamma P]/bound {LP / (b8 / theta):.2e}, acceptance {acc:.3f} >= {1 - kap:.3f}")
R.check("uniform test at small N: ||A|| <= 1, ||A - V^(x)N|| <= 12 sqrt(N)||R||/(pi w), AA* <= nu' P'(AA*), "
        "||(I-Q)A|| <= sqrt(nu' alpha), Tr_E[e^{-beta H_E} Q] <= alpha^{-1} e^{-beta(Na - w)} I, [P, H_phys] = 0, "
        "||(I-P)Q||^2 <= nu theta, the (alpha theta)^{-1} certificate, and acceptance >= 1 - kappa", ok7, "; ".join(rows7))

# shell counts and the entropy of a nearly pure block
ok7b = True
import itertools
for K_ in (2, 3, 4):
    for n in (1, 2, 3, 5):
        en = rng.standard_normal(K_)
        sums = {round(sum(c), 9) for c in itertools.combinations_with_replacement(en, n)}
        ok7b &= len(sums) <= (n + 1) ** K_
for trial in range(500):
    D_ = int(rng.integers(2, 8))
    psi_ = np.eye(D_)[0]
    lam = 10 ** rng.uniform(-4, 0)
    rho = (1 - lam) * dm(psi_) + lam * random_density(D_, rng)
    pC = 1 - np.real(rho[0, 0])
    hC = 0 if pC <= 0 else -pC * math.log(pC) - (1 - pC) * math.log(1 - pC)
    ok7b &= S(rho) <= hC + pC * math.log(D_ - 1) + 1e-12
R.check("at most (n+1)^K energy shells for n-fold sums of K levels, and a state with weight 1 - p on a pure vector has "
        "entropy <= h(p) + p ln(dim - 1) (the whole-controller entropy budget)", ok7b)

# ---------------------------------------------------------------------------------------------------------------------
# 8. the decoder
ok8, near8 = True, 0
for trial in range(2000):
    d = int(rng.integers(2, 6))
    A = random_density(d, rng, rank=int(rng.integers(1, d + 1)))
    A = A / np.max(np.linalg.eigvalsh(A)) * rng.uniform(0.2, 1)
    Bm = random_density(d, rng) * 10 ** rng.uniform(-3, 1)
    Ssum = A + Bm
    isq = powm_h(Ssum, -0.5)
    lhs = np.eye(d) - isq @ A @ isq
    rhs = 2 * (np.eye(d) - A) + 4 * Bm
    m = np.min(np.linalg.eigvalsh(herm(rhs - lhs)))
    ok8 &= m > -1e-9
    # how close the inequality comes to equality: the largest ratio <v, lhs v>/<v, rhs v>
    wr, vr = np.linalg.eigh(herm(rhs))
    if wr.min() > 1e-9:
        isr = (vr * wr ** -0.5) @ dag(vr)
        near8 += np.max(np.linalg.eigvalsh(herm(isr @ lhs @ isr))) > 0.2
R.check("Hayashi-Nagaoka: I - (A+B)^{-1/2} A (A+B)^{-1/2} <= 2(I - A) + 4B for 0 <= A <= I, B >= 0",
        ok8 and near8 >= 100, f"{near8} cases where the left side reaches 20% of the right side in some direction")
ok8b = True
for trial in range(200):
    d, q = int(rng.integers(2, 4)), int(rng.integers(2, 5))
    Om = [random_density(d, rng) for _ in range(q)]
    tot = sum(Om)
    sc = powm_h(tot, -0.5) / math.sqrt(rng.uniform(1, 2))
    Om = [sc @ o @ sc for o in Om]                                     # sum Omega_j <= I
    Sh = np.roll(np.eye(q), 1, axis=0)
    Ddec = sum(np.kron(o, np.linalg.matrix_power(Sh, -j % q)) for j, o in enumerate(Om))
    ok8b &= opnorm(Ddec) <= 1 + 1e-10
    # Halmos square of a contraction commuting with a Hamiltonian
    hdiag = rng.integers(0, 3, 2 * d).astype(float)
    T = np.zeros((2 * d, 2 * d), dtype=complex)
    for val in np.unique(hdiag):
        idx = np.where(hdiag == val)[0]
        blk = rng.standard_normal((len(idx), len(idx))) + 1j * rng.standard_normal((len(idx), len(idx)))
        T[np.ix_(idx, idx)] = blk / (opnorm(blk) * rng.uniform(1, 1.5))
    UT = np.block([[T, powm_h(np.eye(2 * d) - T @ dag(T), 0.5)], [powm_h(np.eye(2 * d) - dag(T) @ T, 0.5), -dag(T)]])
    ok8b &= opnorm(dag(UT) @ UT - np.eye(4 * d)) < 1e-9
    ok8b &= opnorm(T @ powm_h(np.eye(2 * d) - dag(T) @ T, 0.5) - powm_h(np.eye(2 * d) - T @ dag(T), 0.5) @ T) < 1e-9
    Hd = np.kron(np.eye(2), np.diag(hdiag))
    ok8b &= opnorm(UT @ Hd - Hd @ UT) < 1e-9
    b = rng.uniform(0, 0.5)
    ov = rng.uniform(1 - b, 1)
    ok8b &= math.sqrt(1 - ov ** 2) <= math.sqrt(2 * b) and 1 - ov ** 2 <= 2 * b
R.check("D_dec = sum_j Omega_j (x) S(-j) is a contraction; the Halmos square of an energy-commuting contraction is an "
        "energy-commuting unitary with T sqrt(I - T*T) = sqrt(I - TT*) T; overlap 1 - b gives error sqrt(2b) and "
        "probability 2b", ok8b)

# ---------------------------------------------------------------------------------------------------------------------
# 9. the mechanical factory
ok9 = True
for trial in range(300):
    beta = rng.uniform(0.3, 2)
    s = int(rng.integers(1, 3))
    omega = np.concatenate([[1 / beta], rng.integers(1, 3, s - 1) / beta]) if s > 1 else np.array([1 / beta])
    n = int(rng.integers(1, 3))
    Ct = float(rng.integers(1, 6))
    Tt = int(rng.integers(6, 12))
    # environment eigenvectors of E^n: coordinate charges in {0..n}^s (energy omega.v)
    charges = [np.array(v) for v in np.ndindex(*([n + 1] * s))]
    mult = rng.integers(1, 3, len(charges))                     # multiplicities of each charge
    ZEn = float(sum(m_ * math.exp(-beta * omega @ v) for m_, v in zip(mult, charges)))
    dt = lambda t: math.ceil(Ct * math.exp(beta * omega @ np.array(t)))
    tiles = list(np.ndindex(*([Tt] * s)))
    ZF = sum(dt(t) * math.exp(-beta * omega @ np.array(t)) for t in tiles)
    ok9 &= Ct * Tt ** s <= ZF * (1 + 1e-12) and ZF <= (Ct + 1) * Tt ** s * (1 + 1e-12)
    for u in tiles:
        u = np.array(u)
        src = sum(m_ * dt(u - v) for m_, v in zip(mult, charges) if np.all(u - v >= 0))
        ok9 &= src <= (1 + 1 / Ct) * Ct * math.exp(beta * omega @ u) * ZEn * (1 + 1e-12)
    q = int(rng.integers(2, 50))
    k = math.floor(math.log(q) - math.log(ZEn) - math.log(1 + 1 / Ct))
    for u in tiles:
        u = np.array(u)
        tgt_tile = u - k * np.eye(s)[0]
        if np.all(tgt_tile >= 0) and np.all(tgt_tile < Tt):
            src = sum(m_ * dt(u - v) for m_, v in zip(mult, charges) if np.all(u - v >= 0))
            ok9 &= q * dt(tuple(tgt_tile)) >= src
    # bad-tile probability of the Gibbs stock
    marg = n + abs(k) + 1
    bad = sum(dt(t) * math.exp(-beta * omega @ np.array(t)) for t in tiles
              if any(x < marg or x >= Tt - marg for x in t)) / ZF
    ok9 &= bad <= 2 * s * (1 + 1 / Ct) * marg / Tt + 1e-12
    # energies of the extraction battery and pair conservation
    Ei, Ef = max(0, -k / beta), max(0, k / beta)
    ok9 &= abs((Ef - Ei) - k / beta) < 1e-12
    for v in charges:
        u = v + np.array([abs(k) + 1] + [0] * (s - 1))
        ok9 &= abs((omega @ v + Ei + omega @ (u - v)) - (0 + Ef + omega @ (u - k * np.eye(s)[0]))) < 1e-9
R.check("factory: C T^s <= Z_F <= (C+1) T^s; sum_l d_{u-v_l} <= (1 + 1/C) C e^{beta omega.u} Z_E^n <= q d_{u - k e_1}; "
        "bad tiles have probability <= 2s(1 + 1/C)(n+|k|+1)/T; E_f - E_i = k/beta; every pair conserves energy", ok9)
ok9b = True
for trial in range(2000):
    n = int(rng.integers(1, 1000))
    beta = rng.uniform(0.2, 5)
    lnZE = rng.uniform(0, 3)
    w = rng.uniform(0, 50)
    lnc = -rng.uniform(1, 60)                                   # ln(eps' alpha theta)
    Ct = rng.uniform(1, 100)
    p_, tn, gn = rng.uniform(-2, 2), rng.uniform(-1, 1), rng.uniform(-1, 1)
    a_v = p_ - gn
    lnL = lnc + n * lnZE + beta * (n * a_v - w)
    if lnL < math.log(2) or lnL > 600:
        continue
    q = math.floor(math.exp(lnL))
    k = math.floor(math.log(q) - n * lnZE - math.log(1 + 1 / Ct))
    w0 = p_ + tn
    W = n * w0 - k / beta
    ok9b &= W <= n * (tn + gn) + w + (-lnc + math.log(2) + math.log(1 + 1 / Ct) + 1) / beta + 1e-9
R.check("rounding: W_nom = n w_0 - k/beta <= n(t_n + g_n) + w + beta^{-1}[-ln(eps' alpha theta) + ln 2 + "
        "ln(1 + 1/C) + 1]", ok9b)

# ---------------------------------------------------------------------------------------------------------------------
# 10. the rare excitation
ok10, ratio10 = True, 0.0
for trial in range(30):
    d, r = 3, 2
    ch = Channel(random_channel(d, r, rng), H3, beta=1.0)
    Yr = herm(rng.standard_normal((r, r)) + 1j * rng.standard_normal((r, r)))
    Xop = ch.psistar(Yr)
    pval = float(np.max(np.linalg.eigvalsh(Yr)))
    HE = pval * np.eye(r) - Yr
    tn = float(np.max(np.linalg.eigvalsh(herm(ch.D - Xop))))
    Bh = herm(tn * np.eye(d) - (ch.D - Xop))
    w0 = pval + tn
    ok10 &= w0 >= -1e-12
    M = 10 ** rng.uniform(1, 3) * (1 + opnorm(Bh))
    z = math.exp(-M) / (1 + math.exp(-M))
    C0, F0 = powm_h(np.eye(d) - Bh / M, 0.5), powm_h(Bh / M, 0.5)
    J = np.block([[C0, -F0], [F0, C0]])                         # G outermost, basis (g, e)
    Q0 = herm(ch.phistar(ch.H) + ch.psistar(HE))
    En = C0 @ Q0 @ C0 + F0 @ Q0 @ F0 - Q0 - 2 * z * Bh
    chi = 3 * np.ptp(np.linalg.eigvalsh(Q0)) * opnorm(Bh) / M + 2 * z * opnorm(Bh)
    ok10 &= opnorm(En) <= chi + 1e-12
    ratio10 = max(ratio10, opnorm(En) / chi)
    Hfull = np.kron(ch.H, np.eye(r)) + np.kron(np.eye(d), HE)
    for _ in range(3):
        rho = random_density(d, rng)
        gain = 0.0
        for gstate, pg in ((0, 1 - z), (1, z)):
            G0 = np.zeros((2, 2))
            G0[gstate, gstate] = 1
            st = J @ np.kron(G0, rho) @ dag(J)
            eG = M * np.real(np.trace(st[d:, d:]))
            sS = st[:d, :d] + st[d:, d:]
            eOE = np.real(np.trace(ch.V @ sS @ dag(ch.V) @ Hfull))   # environment starts in its zero-energy ground state
            gain += pg * (eG + eOE - np.real(np.trace(rho @ ch.H)) - M * gstate)
        ok10 &= abs(gain - np.real(np.trace(rho @ (w0 * np.eye(d) + En)))) < 1e-9
R.check("rare excitation: the external gain is exactly w_0 I + E_n with E_n = C0 Q0 C0 + F0 Q0 F0 - Q0 - 2z B_hot, "
        "||E_n|| <= 3 osc(Q0)||B_hot||/M + 2z||B_hot||, and w_0 = p + t_n >= 0", ok10, f"largest ||E_n||/chi_n {ratio10:.3f}")

# ---------------------------------------------------------------------------------------------------------------------
# 11. the bank
ok11 = True
for trial in range(50):
    d = 3
    charges = rng.integers(0, 3, (d, 2))                       # two bank coordinates
    side = 13
    box = list(np.ndindex(side, side))
    idx = {b: i for i, b in enumerate(box)}
    def lift(U):
        Lm = np.zeros((d * len(box), d * len(box)), dtype=complex)
        for x in range(d):
            for y in range(d):
                shift = charges[y] - charges[x]
                for b in box:
                    nb = (b[0] + shift[0], b[1] + shift[1])
                    if nb in idx:
                        Lm[x * len(box) + idx[nb], y * len(box) + idx[b]] += U[x, y]
        return Lm
    U1, U2 = random_unitary(d, rng), random_unitary(d, rng)
    interior = [x * len(box) + idx[b] for x in range(d) for b in box if 4 <= b[0] <= 8 and 4 <= b[1] <= 8]
    L1, L2, L12 = lift(U1), lift(U2), lift(U1 @ U2)
    ok11 &= np.allclose((L1 @ L2)[:, interior], L12[:, interior])
    ok11 &= np.allclose(lift(dag(U1)), dag(L1))
    ok11 &= np.allclose(lift(np.eye(d)), np.eye(d * len(box)))
    ev = np.array([charges[x] @ np.array([1.0, math.sqrt(2)]) + np.array(b) @ np.array([1.0, math.sqrt(2)])
                   for x in range(d) for b in box])
    ok11 &= np.allclose(L1 @ np.diag(ev) - np.diag(ev) @ L1, 0)
R.check("bank lift L(U) = sum U_xy |x><y| (x) T_{a_y - a_x}: multiplicative, *-preserving, unital, energy-conserving "
        "(two coordinates, incommensurate frequencies)", ok11)
ok11b, worst11 = True, 0.0
for Lp in list(range(1, 200)) + [500, 1000, 2000]:
    u = np.arange(Lp)
    chi = math.sqrt(2 / (Lp + 1)) * np.sin(math.pi * (u + 1) / (Lp + 1))
    ok11b &= abs(chi @ chi - 1) < 1e-12
    c = np.concatenate([[0], chi, [0]])
    ok11b &= abs(np.sum(np.diff(c) ** 2) - 4 * math.sin(math.pi / (2 * (Lp + 1))) ** 2) < 1e-12
    k = np.subtract.outer(u, u)
    with np.errstate(divide="ignore", invalid="ignore"):
        cmat = np.where(k == 0, math.pi ** 2 / 3, 2.0 * (-1.0) ** k / np.where(k == 0, 1, k) ** 2)
    m2 = chi @ cmat @ chi                                        # E theta^2 of the phase law, exactly
    worst11 = max(worst11, m2 / (math.pi ** 4 / (4 * (Lp + 1) ** 2)))
    ok11b &= m2 <= math.pi ** 4 / (4 * (Lp + 1) ** 2) * (1 + 1e-12)
R.check("sine packet on L levels: normalized, sum |chi_{u+1} - chi_u|^2 = 4 sin^2(pi/(2(L+1))), and "
        "E theta^2 <= pi^4/(4(L+1)^2) (exact Fourier sums, L <= 2000)", ok11b, f"largest ratio {worst11:.4f}")
R.check("k_front: 7n sqrt(l) pi^2/(2(L+1)) <= 10 pi^2 sqrt(l) (n+1)/(L+1) (six per contact plus one for the pump)",
        all(7 * n * math.pi ** 2 / 2 <= 10 * math.pi ** 2 * (n + 1) for n in range(1, 10000)))
R.close()
