"""The noise horizon (Proposition "Noise horizon", Proposition "The asymmetry is not generic" for fixed noise, and
Appendix "Physical construction for the batch law and the noise horizon": uniform noise construction, finite horizons,
padding, envelopes).

Checks:
  1. B(Phi_delta) = 0 for every fixed delta > 0 while B(Phi) = c > 0 (the qutrit N): B is not continuous;
  2. the noise dilation: Psi_delta^* H_E = B_delta, V^*(H + H_E)V = H + p_delta I, V^* H_E^2 V = B_delta^2/delta, residual
     <= 5h/sqrt(delta) and its n-copy form, p_delta in [0, h], ||B_delta|| <= 2h, beta e_delta <= ln R, r <= Z_E <= R;
  3. the rates of Theorem "Diverging noise horizon": delta_A = O(t_n^{-1/4}) with the stated w, and q >= 2 eventually;
  4. the free replacement module: a Gibbs flag controlling a swap with a Gibbs payload is an energy-conserving unitary that
     implements (1-delta) id + delta gamma Tr at zero work;
  5. padding: the all-unreplaced branch gives (1/2)||Phi_delta^m - Phi^m||_diamond <= 1 - (1-delta)^m <= m delta; the
     choice of x_* gives f_0(x_*) <= c/2; the envelope bound theta B/2;
  6. envelopes: appending replacement (delta_2 - delta_1)/(1 - delta_1) maps Phi_{delta_1} to Phi_{delta_2}; product
     targets differ by at most N|delta - delta'|; every m occurs as floor(theta N); the scaling monotonicity.
"""
import math

import numpy as np
import sympy as sp

from qtools import (Channel, Report, batch_cost_smooth, capacity, choi_of, dag, diamond_half, dm, herm, kraus_from_choi,
                    opnorm, random_density, span_residual)

R = Report("The noise horizon")
rng = np.random.default_rng(20261018)

af, bf = math.log(1.5), math.log(3.0)
Hn = np.diag([0, af, bf]).astype(complex)
gn = np.diag([0.5, 1 / 3, 1 / 6]).astype(complex)
pl, mi, tw = np.array([1, 1, 0]) / math.sqrt(2), np.array([1, -1, 0]) / math.sqrt(2), np.array([0, 0, 1.0])
KN = [amp * np.outer(np.eye(3)[i], v) for i, v, amp in
      [(0, pl, 1.0), (0, tw, math.sqrt(.5)), (1, mi, math.sqrt(.8)), (2, mi, math.sqrt(.2)), (2, tw, math.sqrt(.5))]]


def noisy(K, delta, g):
    d = K[0].shape[0]
    return [math.sqrt(1 - delta) * k for k in K] + \
        [math.sqrt(delta * g[a, a].real) * np.outer(np.eye(d)[a], np.eye(d)[b]) for a in range(d) for b in range(d)]


# 1. B(Phi_delta) = 0 for fixed delta > 0, and the jump at delta = 0
rows1, ok1 = [], True
lo0, up0, _, _ = batch_cost_smooth(Channel(KN, Hn, 1.0))
ok1 &= abs(lo0 - 0.15471030022) < 1e-6
for delta in (0.3, 0.05, 0.01):
    ch = Channel(noisy(KN, delta, gn), Hn, 1.0)
    lo, up, _, _ = batch_cost_smooth(ch)
    ok1 &= ch.balance_residual() < 1e-10 and abs(lo) < 1e-6 and abs(up) < 1e-6 and opnorm(ch.phi(gn) - gn) < 1e-12
    rows1.append(f"delta = {delta}: B in [{lo:.1e}, {up:.1e}]")
R.check("Phi_delta = (1-delta)N + delta gamma Tr is balanced and costs nothing for every fixed delta > 0, while "
        "B(N) = 0.1547: B is not continuous at delta = 0", ok1, f"B(N) = {lo0:.8f}; " + "; ".join(rows1))

# 2. the noise dilation
ok2, worst_res, worst_eg = True, 0.0, 0.0
chans = [("N", KN)]


def random_gp_qutrit(rng):
    import cvxpy as cp
    J = cp.Variable((9, 9), hermitian=True)
    Rm = herm(rng.standard_normal((9, 9)) + 1j * rng.standard_normal((9, 9)))
    cons = [J >> 0, cp.partial_trace(J, [3, 3], axis=1) == np.eye(3),
            cp.partial_trace(cp.kron(gn.T, np.eye(3)) @ J, [3, 3], axis=0) == gn]
    cp.Problem(cp.Maximize(cp.real(cp.trace(Rm @ J))), cons).solve(solver="CLARABEL")
    K = kraus_from_choi(np.asarray(J.value), 3, 3, tol=1e-7)
    s_ = sum(dag(k) @ k for k in K)
    w, v = np.linalg.eigh(s_)
    return [k @ (v * w ** -0.5) @ dag(v) for k in K]


for i in range(3):
    chans.append((f"random GP qutrit {i}", random_gp_qutrit(rng)))
h = float(np.ptp(np.linalg.eigvalsh(Hn)))
beta = 1.0
for name, K0 in chans:
    r = len(K0)
    d = 3
    ok2 &= r >= 2
    for delta in (0.5, 0.1, 1e-2, 1e-4):
        K = noisy(K0, delta, gn)
        ch = Channel(K, Hn, beta)
        Rdim = r + d * d
        Dd = ch.D
        p = float(np.max(np.linalg.eigvalsh(Dd)))
        Bd = herm(p * np.eye(d) - Dd)
        ok2 &= -1e-12 <= p <= h + 1e-12 and opnorm(Bd) <= 2 * h + 1e-12
        HE = np.zeros((Rdim, Rdim), dtype=complex)
        HE[r:, r:] = np.kron(np.eye(d), Bd / delta)                # replacement labels (a, b): I_a (x) B_delta/delta
        ok2 &= opnorm(ch.psistar(HE) - Bd) < 1e-9 * (1 + opnorm(Bd))
        Wtot = np.kron(Hn, np.eye(Rdim)) + np.kron(np.eye(d), HE)
        ok2 &= opnorm(dag(ch.V) @ Wtot @ ch.V - Hn - p * np.eye(d)) < 1e-9
        ok2 &= opnorm(dag(ch.V) @ np.kron(np.eye(d), HE @ HE) @ ch.V - Bd @ Bd / delta) < 1e-7 * (1 + opnorm(Bd) ** 2 / delta)
        Rm = Wtot @ ch.V - ch.V @ (Hn + p * np.eye(d))
        worst_res = max(worst_res, opnorm(Rm) / (5 * h / math.sqrt(delta)))
        V2 = np.kron(ch.V, ch.V)
        W2 = np.kron(Wtot, np.eye(d * Rdim)) + np.kron(np.eye(d * Rdim), Wtot)
        H2 = np.kron(Hn + p * np.eye(d), np.eye(d)) + np.kron(np.eye(d), Hn + p * np.eye(d))
        R2 = W2 @ V2 - V2 @ H2
        ok2 &= opnorm(R2) <= 5 * h * math.sqrt(2 / delta) * (1 + 1e-9)
        eHE = np.linalg.eigvalsh(HE)
        ok2 &= np.min(eHE) > -1e-9
        gE = np.exp(-beta * (eHE - 0))
        ZE = gE.sum()
        eg = float(eHE @ gE / ZE)
        worst_eg = max(worst_eg, beta * eg / math.log(Rdim))
        ok2 &= r - 1e-9 <= ZE <= Rdim + 1e-9
R.check("noise dilation (old labels at energy 0, replacement labels I_a (x) B_delta/delta): Psi_delta^* H_E = B_delta, "
        "V^*(H + H_E)V = H + p_delta I, V^* H_E^2 V = B_delta^2/delta, ||R|| <= 5h/sqrt(delta), two copies <= "
        "5h sqrt(2/delta), p_delta in [0, h], ||B_delta|| <= 2h, r >= 2 and r <= Z_E <= R",
        ok2 and worst_res <= 1, f"largest ||R||/(5h/sqrt delta) = {worst_res:.3f}")
R.check("the Gibbs mean of H_E satisfies beta e_delta <= ln R although ||H_E|| = O(1/delta)", worst_eg <= 1,
        f"largest beta e_delta/ln R = {worst_eg:.3f}")
# a Gibbs-preserving unitary commutes with H and has B = 0, so r >= 2 when B > 0
okr = True
for trial in range(50):
    U = np.diag(np.exp(1j * rng.uniform(0, 6, 3)))
    ch = Channel([U], Hn)
    okr &= opnorm(ch.phi(gn) - gn) < 1e-12 and opnorm(U @ Hn - Hn @ U) < 1e-12 and opnorm(ch.D) < 1e-12
R.check("Gibbs-preserving unitaries (non-degenerate H) commute with H and have D = 0, B = 0", okr)

# 3. the rates of the diverging noise horizon
ok3 = True
for bh in (0.1, 1.0, 10.0):
    for tn in (10.0, 1e3, 1e6):
        for n in (100, 10 ** 4, 10 ** 8):
            hh = bh                                                  # beta = 1
            delta = tn / n
            if delta >= 1:
                continue
            w = 100 * (1 + bh) * n / tn ** 0.25
            dA = 12 * math.sqrt(n) * 5 * hh * math.sqrt(n / tn) / (math.pi * w)
            ok3 &= dA * tn ** 0.25 <= 60 * hh / (100 * math.pi * (1 + bh)) * (1 + 1e-12) and dA * tn ** 0.25 < 0.2
# q = floor(eps' alpha Z_E^n e^{beta(n p - w)}) >= 2 eventually: Z_E >= 2, p >= 0, ln(eps' alpha) = -O(ln n), w = o(n)
dR = 3 * 14
for bh in (0.1, 1.0):
    for n in (10 ** 12, 10 ** 15):
        tn = n / 10
        w_beta = 100 * (1 + bh) * n / tn ** 0.25
        lnq = -4 * math.log(n + 1) - (dR + 6) * math.log(n + 1) + n * math.log(2) - w_beta
        ok3 &= lnq > math.log(2)
R.check("Theorem 'Diverging noise horizon': with w = 100 beta^{-1}(1 + beta h) n/t_n^{1/4}, delta_A <= "
        "12 sqrt(n) ||R^(n)||/(pi w sqrt n) <= 0.6 t_n^{-1/4}/pi = O(t_n^{-1/4}), and q >= 2 once n ln Z_E dominates beta w "
        "and the logarithms (n = 1e12, 1e15)", ok3)

# 4. the free replacement module
ok4 = True
for delta in (0.5, 0.2, 1e-3):
    eF = math.log((1 - delta) / delta) / beta                        # a genuine Gibbs flag with populations (1-delta, delta)
    HF = np.diag([0.0, eF])
    flag = np.diag(np.exp(-beta * np.diag(HF)))
    flag /= np.trace(flag)
    ok4 &= abs(flag[1, 1] - delta) < 1e-12
    d = 3
    SW = np.zeros((d * d, d * d))
    for i in range(d):
        for j in range(d):
            SW[j * d + i, i * d + j] = 1
    U = np.kron(dm([1, 0]), np.eye(d * d)) + np.kron(dm([0, 1]), SW)      # flag (x) system (x) payload
    Htot = np.kron(HF, np.eye(d * d)) + np.kron(np.eye(2), np.kron(Hn, np.eye(d)) + np.kron(np.eye(d), Hn))
    ok4 &= opnorm(U @ Htot - Htot @ U) < 1e-12 and opnorm(dag(U) @ U - np.eye(2 * d * d)) < 1e-12
    for _ in range(5):
        rho = random_density(d, rng)
        st = U @ np.kron(flag, np.kron(rho, gn)) @ dag(U)
        t = st.reshape(2, d, d, 2, d, d)
        out = np.einsum("aibajb->ij", t)
        fl = np.einsum("aibcib->ac", t)
        ok4 &= opnorm(out - ((1 - delta) * rho + delta * gn)) < 1e-12 and opnorm(fl - flag) < 1e-12
        ok4 &= abs(np.real(np.trace(Htot @ st)) - np.real(np.trace(Htot @ np.kron(flag, np.kron(rho, gn))))) < 1e-12
R.check("free replacement: a Gibbs flag with populations (1-delta, delta) controlling a swap with a Gibbs payload is an "
        "energy-conserving unitary implementing (1-delta) id + delta gamma Tr, with the flag unchanged and no work", ok4)

# 5. padding, x_*, and the envelope bound
Hq = np.diag([0.0, 1.0]).astype(complex)
gq = np.diag([1 / (1 + math.exp(-1)), math.exp(-1) / (1 + math.exp(-1))])
ok5 = True
gp_qubit = [np.array([[1, 0], [0, math.sqrt(1 - 0.3)]]), np.array([[0, math.sqrt(0.3)], [0, 0]])]
for m in (1, 2):
    for delta in (0.05, 0.3):
        K = gp_qubit
        if m == 2:
            K = [np.kron(a, b) for a in gp_qubit for b in gp_qubit]
            g = np.kron(gq, gq)
        else:
            g = gq
        dd = K[0].shape[0]
        phi = lambda x, K=K: sum(k @ x @ dag(k) for k in K)
        rep = lambda x, g=g: g * np.trace(x)
        if m == 1:
            phid = lambda x: (1 - delta) * phi(x) + delta * rep(x)
        else:
            K1 = noisy(gp_qubit, delta, gq)
            phid = lambda x: sum(np.kron(a, b) @ x @ dag(np.kron(a, b)) for a in K1 for b in K1)
        dist = diamond_half(choi_of(phid, dd), choi_of(phi, dd), dd, dd)
        ok5 &= dist <= 1 - (1 - delta) ** m + 1e-7 and 1 - (1 - delta) ** m <= m * delta + 1e-15
R.check("padding: (1/2)||Phi_delta^(x)m - Phi^(x)m||_diamond <= 1 - (1-delta)^m <= m delta (SDP, m = 1, 2)", ok5)
ok5b = True
for trial in range(20000):
    c = rng.uniform(1e-6, 5)
    d = int(rng.integers(2, 20))
    bh = rng.uniform(0, 50)
    t = lambda x: min(1.0, 4 * x ** 0.25)
    f0 = lambda x: (2 * bh + math.log(d)) * x + 4 * t(x) * math.log(d)
    xs = min(0.5, (c / (64 * math.log(d))) ** 4, c / (4 * (2 * bh + math.log(d))))
    ok5b &= xs > 0 and f0(xs) <= c / 2 * (1 + 1e-12)
    x2 = xs * rng.uniform(0, 1)
    ok5b &= f0(x2) <= f0(xs) + 1e-15
    lam = rng.uniform(0.01, 20)
    theta = min(1.0, -math.log(1 - xs) / lam) * rng.uniform(0.5, 1)
    B = c / 1.0
    ok5b &= theta * (B - f0(1 - math.exp(-theta * lam))) >= theta * B / 2 - 1e-12
R.check("x_* = min{1/2, (c/(64 ln d))^4, c/(4(2 beta h + ln d))} gives f_0(x_*) <= c/2, f_0 is nondecreasing, and "
        "1 - e^{-theta lambda} <= x_* gives the envelope bound theta[B - f_0/beta] >= theta B/2", ok5b)

# 6. envelopes
d1, d2 = sp.symbols("delta1 delta2", positive=True)
app = (d2 - d1) / (1 - d1)
ok6 = sp.simplify((1 - app) * (1 - d1) - (1 - d2)) == 0 and sp.simplify((1 - app) * d1 + app - d2) == 0
for (x1, x2) in ((0.1, 0.3), (0.01, 0.02)):
    K1 = noisy(KN, x1, gn)
    K2 = noisy(KN, x2, gn)
    a_ = (x2 - x1) / (1 - x1)
    for _ in range(5):
        rho = random_density(3, rng)
        o1 = sum(k @ rho @ dag(k) for k in K1)
        ok6 &= opnorm((1 - a_) * o1 + a_ * gn - sum(k @ rho @ dag(k) for k in K2)) < 1e-12
    dist = diamond_half(choi_of(lambda x: sum(k @ x @ dag(k) for k in K1), 3),
                        choi_of(lambda x: sum(k @ x @ dag(k) for k in K2), 3), 3, 3)
    ok6 &= dist <= abs(x2 - x1) + 1e-7
for theta in (0.3, 0.5, 0.77, 1.0):
    seen = {math.floor(theta * N) for N in range(1, 5000)}
    ok6 &= all(m in seen for m in range(1, int(theta * 4999)))
lam_, mu_, U_ = sp.symbols("lambda mu U", positive=True)
th_ = mu_ / lam_
ok6 &= sp.simplify(mu_ * (U_ / th_) - lam_ * U_) == 0
R.check("appending replacement (delta_2 - delta_1)/(1 - delta_1) maps Phi_{delta_1} to Phi_{delta_2} exactly; one "
        "copy moves by at most |delta - delta'| (SDP); every m occurs as floor(theta N); U(mu) <= U(lambda)/theta with "
        "mu = theta lambda is mu U(mu) <= lambda U(lambda)", bool(ok6))
R.close()
