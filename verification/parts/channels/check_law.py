"""The real-time work law: bookkeeping, accumulation and the construction (Sections 2-3, Appendices "The construction"
and "The fixed-error converse").

Checks:
  1. Definition 1: on real-time rounds (random device states purified by F, random rounds on S D) Q and F stay a
     product, S(QO|F) >= S(Q) - S(O) (equality reached for unitary rounds), and S(D_{t+1}) - S(D_t) = S(Q_t O_t|F_t)
     exactly (Lemma "Causal accumulation");
  2. for every dilation, S(B') - S(tau) = S(rho) - S(Phi(rho)) + I(O:B') (random dilations, mixed baths);
  3. Lemma "Accounting identity" on random exactly energy-conserving two-round implementations with a controller, a
     battery and a Gibbs reservoir: w = A + beta/ln2 dE_sys + D(R_fin||gamma_R) + I(C:B:R)_fin, and the reservoir
     identity S(R_fin) - S(gamma_R) = beta dE_R/ln2 - D(R_fin||gamma_R);
  4. |Tr H X| <= eps span(H) for traceless X with 1/2||X||_1 <= eps (equality on the extreme eigenvectors);
     Fannes-Audenaert |S(rho) - S(sigma)| <= eps log2(D - 1) + h(eps) behind the batch remark;
  5. Lemma "Minimax": a flagged direct sum of dilations realizes the convex combination of their objectives exactly,
     F_Dil is concave, and |f_Dil(rho) - S(rho)| <= log d (equality for the swap dilation of full depolarization);
  6. A(t) of Appendix A: A(0) = I, A(t) >= 0 and A'(0) = ln2 Gamma^*(L_B) + beta(Phi^*(H) - H) (finite differences);
     the similarity Q(t) L(U) Q(t)^{-1} = L(U_t) for the energy register;
  7. forming the baths: reservoir levels j W_f with degeneracies m_C^j K^{L_f - j} have equal Gibbs weights, the swapped
     subspaces have equal energy and dimension, and the explicit permutation succeeds with probability 1 - 1/(L_f + 1);
  8. the converter: (1 - theta) e^{beta s} > 1 for theta <= (1 - e^{-beta s})/2, and the ratio display; the net work
     W_f - w_n of Appendix A, symbolically, and its per-use overhead O(n^{-1/4});
  9. Appendix B: the frame {e_i} u {e_i + e_k} u {e_i + i e_k} gives m^2 rank-one effects that are informationally
     complete, L = sum m_j^2 <= d^4 for H_Y = -H^T x I + I x H, and the test instrument is trace preserving and commutes
     with H_Y; sum_{k <= 2 gamma n} C(n,k) L^k <= 2^{n theta_gamma} (exact integers); the battery remark
     b_beta <= beta W/ln2 + log2 R_B;
 10. Lemma "cap" at s = 1/2: the constant 4 and the rejected trace (1 - s)/2;
     Lemma "postproj" constants: squared purified distance <= 4 delta/r <= 1/16; the assembly: 1 - 2 log2(delta p_G)
     <= 13 + 4 log2(1/p) and, with a = min{delta'/16, delta'^2/(256 C_f^2)}, the right side exceeds n(T - delta')
     for large n.
"""
from fractions import Fraction
import itertools
import math

import numpy as np
import sympy as sp

from qtools import (Report, conserving_unitary, cond_entropy, dm, entropy, gibbs, h2, herm, kraus_apply, mfun,
                    mutual_info, ptrace, random_density, random_herm, random_unitary, relent, trace_norm)

R = Report("The real-time work law")
rng = np.random.default_rng(20261018)
LN2 = math.log(2)


def purify(rho, rng=None):
    w, v = np.linalg.eigh(herm(rho))
    w = np.clip(w, 0, None)
    d = len(w)
    return sum(math.sqrt(w[i]) * np.kron(v[:, i], np.eye(d)[i]) for i in range(d))


# ---------------------------------------------------------------------------------------------------- 1. rounds
ok_prod, ok_acc, ok_bound = True, True, True
near = 0
for trial in range(400):
    d, dD = 2, int(rng.integers(2, 5))
    rho = random_density(d, rng)
    psi = purify(rho)                                  # S (x) Q, then reorder to Q S
    psi = psi.reshape(d, d).T.reshape(-1)              # Q (x) S
    rD = random_density(dD, rng, rank=int(rng.integers(1, dD + 1)))
    phiD = purify(rD)                                  # D (x) F
    unitary_round = trial % 4 == 0
    if unitary_round:                                  # a unitary channel on S, device untouched
        U = np.kron(random_unitary(d, rng), np.eye(dD))
    else:
        U = random_unitary(d * dD, rng)
    vec = np.kron(psi, phiD).reshape(d, d * dD, dD)    # Q, (S D), F
    vec = np.einsum("ab,qbf->qaf", U, vec).reshape(-1)
    full = np.outer(vec, vec.conj())
    dims = [d, d, dD, dD]                              # Q, O, D', F
    sQF = ptrace(full, dims, [0, 3])
    ok_prod &= np.allclose(sQF, np.kron(ptrace(full, dims, [0]), ptrace(full, dims, [3])), atol=1e-12)
    sQOF = ptrace(full, dims, [0, 1, 3])
    S_cond = cond_entropy(sQOF, [d, d, dD], [0, 1])
    rise = entropy(ptrace(full, dims, [2])) - entropy(rD)
    ok_acc &= abs(rise - S_cond) < 1e-10
    lower = entropy(ptrace(full, dims, [0])) - entropy(ptrace(full, dims, [1]))
    ok_bound &= S_cond >= lower - 1e-10
    near += abs(S_cond - lower) < 1e-9
R.check("Q and F stay a product through a real-time round (400 random rounds)", bool(ok_prod))
R.check("Lemma \"Causal accumulation\": S(D_{t+1}) - S(D_t) = S(Q_t O_t|F_t) exactly", bool(ok_acc))
R.check("S(QO|F) >= S(Q) - S(O) whenever QF is a product, with equality on unitary rounds", ok_bound and near >= 80,
        f"{near} rounds at equality")

# ---------------------------------------------------------------------------------------------------- 2. dilations
worst = 0.0
for _ in range(300):
    d, dB = int(rng.integers(2, 4)), int(rng.integers(2, 4))
    U = random_unitary(d * dB, rng)
    tau = random_density(dB, rng, rank=int(rng.integers(1, dB + 1)))
    rho = random_density(d, rng)
    out = U @ np.kron(rho, tau) @ U.conj().T
    O = ptrace(out, [d, dB], [0])
    Bp = ptrace(out, [d, dB], [1])
    lhs = entropy(Bp) - entropy(tau)
    rhs = entropy(rho) - entropy(O) + mutual_info(out, [d, dB], [0], [1])
    worst = max(worst, abs(lhs - rhs))
R.check("S(B') - S(tau) = S(rho) - S(Phi(rho)) + I(O:B') for every dilation (300 random dilations)", worst < 1e-10,
        f"max deviation {worst:.1e}")

# ---------------------------------------------------------------------------------------------------- 3. accounting
def accounting_trial(rng, beta):
    # systems: S1, S2 (inputs, energies 0/1), C (0/1), B (0,1,2), R (two qubits, 0/1 each, Gibbs)
    dims = [2, 2, 2, 3, 2, 2]
    Hs = [np.diag([0.0, 1.0]), np.diag([0.0, 1.0]), np.diag([0.0, 1.0]), np.diag([0.0, 1.0, 2.0]),
          np.diag([0.0, 1.0]), np.diag([0.0, 1.0])]
    from qtools import embed
    Htot = sum(embed(Hs[i], [i], dims) for i in range(len(dims)))
    # inputs: entangled with nothing (product), possibly coherent
    s1, s2 = random_density(2, rng), random_density(2, rng)
    alpha = random_density(2, rng)                      # controller, any state
    zeta = dm(np.eye(3)[1]) if rng.random() < 0.5 else random_density(3, rng)   # battery
    gR = np.kron(gibbs(Hs[4], beta), gibbs(Hs[5], beta))
    rho0 = np.kron(np.kron(np.kron(np.kron(s1, s2), alpha), zeta), gR)
    # round 1 acts on S1 C B R, round 2 on S2 C B R; both conserve the total energy of what they touch
    # make U1 trivial on S2 and U2 trivial on S1: build them on the sub-systems and embed
    sub1 = [0, 2, 3, 4, 5]
    sub2 = [1, 2, 3, 4, 5]
    Hsub = lambda sub: sum(embed(Hs[i], [k], [dims[j] for j in sub]) for k, i in enumerate(sub))
    U1 = embed(conserving_unitary(Hsub(sub1), rng), sub1, dims)
    U2 = embed(conserving_unitary(Hsub(sub2), rng), sub2, dims)
    rho1 = U2 @ U1 @ rho0 @ U1.conj().T @ U2.conj().T
    m = lambda r, keep: ptrace(r, dims, keep)
    E = lambda H, r: float(np.trace(H @ r).real)
    dEsys = E(Hs[0], m(rho1, [0])) - E(Hs[0], m(rho0, [0])) + E(Hs[1], m(rho1, [1])) - E(Hs[1], m(rho0, [1]))
    F = lambda H, r: E(H, r) - entropy(r) * LN2 / beta
    w = (F(Hs[3], m(rho0, [3])) - F(Hs[3], m(rho1, [3])) + F(Hs[2], m(rho0, [2])) - F(Hs[2], m(rho1, [2]))) * beta / LN2
    A = entropy(m(rho1, [2, 3, 4, 5])) - entropy(m(rho0, [2, 3, 4, 5]))
    Rf = m(rho1, [4, 5])
    DR = relent(Rf, gR)
    Itot = entropy(m(rho1, [2])) + entropy(m(rho1, [3])) + entropy(Rf) - entropy(m(rho1, [2, 3, 4, 5]))
    dER = E(np.kron(Hs[4], np.eye(2)) + np.kron(np.eye(2), Hs[5]), Rf) - E(np.kron(Hs[4], np.eye(2)) + np.kron(np.eye(2), Hs[5]), gR)
    res_id = (entropy(Rf) - entropy(gR)) - (beta * dER / LN2 - DR)
    cons = np.abs(U1 @ Htot - Htot @ U1).max() + np.abs(U2 @ Htot - Htot @ U2).max()
    return w - (A + beta / LN2 * dEsys + DR + Itot), res_id, cons, w - (A + beta / LN2 * dEsys)


worst_id = worst_res = worst_cons = 0.0
ineq = True
for trial in range(40):
    beta = rng.uniform(0.2, 3)
    d1, d2, c, slack = accounting_trial(rng, beta)
    worst_id, worst_res, worst_cons = max(worst_id, abs(d1)), max(worst_res, abs(d2)), max(worst_cons, c)
    ineq &= slack >= -1e-10
R.check("Lemma \"Accounting identity\": w = A + beta/ln2 dE_sys + D(R_fin||gamma_R) + I(C:B:R)_fin (40 random energy-conserving "
        "two-round implementations), and w >= A + beta dE_sys/ln2",
        worst_id < 1e-9 and worst_cons < 1e-9 and ineq, f"max deviation {worst_id:.1e}")
R.check("reservoir: S(R_fin) - S(gamma_R) = beta dE_R/ln2 - D(R_fin||gamma_R)", worst_res < 1e-9)

# ---------------------------------------------------------------------------------------------------- 4. continuity
ok, near = True, 0
for _ in range(2000):
    d = int(rng.integers(2, 5))
    H = random_herm(d, rng)
    span = np.ptp(np.linalg.eigvalsh(H))
    if rng.random() < 0.3:
        w, v = np.linalg.eigh(H)
        eps = rng.uniform(0, 1)
        X = eps * (dm(v[:, -1]) - dm(v[:, 0]))
        if rng.random() < 0.5:
            X = X + 1e-3 * eps * (random_density(d, rng) - random_density(d, rng))
    else:
        X = random_density(d, rng) - random_density(d, rng)
    eps = 0.5 * trace_norm(X)
    val = abs(np.trace(H @ X).real)
    ok &= val <= eps * span + 1e-12
    near += val >= 0.99 * eps * span
R.check("|Tr H X| <= eps span(H) for traceless X with 1/2||X||_1 <= eps", ok and near >= 300, f"{near} within 1%")
ok, near = True, 0
for _ in range(2000):
    D = int(rng.integers(2, 6))
    r = random_density(D, rng)
    u = rng.uniform(0, 1)
    s = (1 - u) * r + u * random_density(D, rng) if rng.random() < 0.5 else random_density(D, rng)
    if rng.random() < 0.3:                              # near-extremal pair: pure state against a flat tail
        e = rng.uniform(0, 1 - 1 / D)
        r = dm(np.eye(D)[0])
        s = np.diag([1 - e] + [e / (D - 1)] * (D - 1))
    t = 0.5 * trace_norm(r - s)
    val = abs(entropy(r) - entropy(s))
    ok &= val <= t * math.log2(D) + h2(t) + 1e-10                    # the form used in the batch remark, any t
    if t <= 1 - 1 / D:                                               # Audenaert's sharp form
        bnd = t * math.log2(D - 1) + h2(t)
        ok &= val <= bnd + 1e-10
        near += val >= bnd - 1e-9
R.check("continuity: |S(rho) - S(sigma)| <= eps log2 D + h(eps) for every eps (the batch remark), and Audenaert's "
        "eps log2(D - 1) + h(eps) for eps <= 1 - 1/D", ok and near >= 300, f"{near} at equality")

# ---------------------------------------------------------------------------------------------------- 5. minimax
def f_dil(U, tau, rho, d, dB):
    out = U @ np.kron(rho, tau) @ U.conj().T
    return entropy(ptrace(out, [d, dB], [1])) - entropy(tau)


ok_flag, ok_conc, ok_logd = True, True, True
for trial in range(100):
    d = 2
    J = int(rng.integers(2, 4))
    dils = []
    for _ in range(J):
        dB = int(rng.integers(2, 4))
        dils.append((random_unitary(d * dB, rng), random_density(dB, rng), dB))
    p = rng.dirichlet(np.ones(J))
    rho = random_density(d, rng)
    # flagged direct sum: bath = flag (x) padded bath of the largest dimension
    dBm = max(x[2] for x in dils)
    dBt = J * dBm
    taut = np.zeros((dBt, dBt), dtype=complex)
    for j, (U, tau, dB) in enumerate(dils):
        taup = np.zeros((dBm, dBm), dtype=complex)
        taup[:dB, :dB] = tau
        Pj = np.zeros((J, J))
        Pj[j, j] = 1
        taut += p[j] * np.kron(Pj, taup)
    # controlled unitary sum_j |j><j| (x) U_j acting on (system, bath_j)
    Ut = np.zeros((d * dBt, d * dBt), dtype=complex)
    for j, (U, tau, dB) in enumerate(dils):
        Up = np.eye(d * dBm, dtype=complex)
        idx = [a * dBm + b for a in range(d) for b in range(dB)]
        Up[np.ix_(idx, idx)] = U
        Pj = np.zeros((J, J))
        Pj[j, j] = 1
        T4 = Up.reshape(d, dBm, d, dBm)
        blk = np.einsum("abce,fg->afbcge", T4, Pj).reshape(d * J * dBm, d * J * dBm)
        Ut += blk
    ok_flag &= np.allclose(Ut.conj().T @ Ut, np.eye(d * dBt), atol=1e-12)
    lhs = f_dil(Ut, taut, rho, d, dBt)
    rhs = sum(p[j] * f_dil(U, tau, rho, d, dB) for j, (U, tau, dB) in enumerate(dils))
    ok_flag &= abs(lhs - rhs) < 1e-10
    U, tau, dB = dils[0]
    r1, r2 = random_density(d, rng), random_density(d, rng)
    H = np.diag([0.0, rng.uniform(0, 2)])
    PhiU = lambda r: ptrace(U @ np.kron(r, tau) @ U.conj().T, [d, dB], [0])
    Fd = lambda r: f_dil(U, tau, r, d, dB) + np.trace(H @ (PhiU(r) - r)).real
    ok_conc &= Fd((r1 + r2) / 2) >= (Fd(r1) + Fd(r2)) / 2 - 1e-12
    ok_logd &= abs(f_dil(U, tau, rho, d, dB) - entropy(rho)) <= math.log2(d) + 1e-12
# equality case: swap the input into a maximally mixed bath of the same size (full depolarization)
SW = np.zeros((4, 4))
for a in range(2):
    for b in range(2):
        SW[2 * b + a, 2 * a + b] = 1
eq = f_dil(SW, np.eye(2) / 2, dm([1, 0]), 2, 2) - entropy(dm([1, 0]))
R.check("a flagged direct sum realizes sum_j p_j f_j exactly (the flag's entropy cancels; 100 random families)", bool(ok_flag))
R.check("F_Dil = f_Dil + e_H is concave (midpoints), and |f_Dil(rho) - S(rho)| <= log d with equality for the swap "
        "into a flat bath", bool(ok_conc and ok_logd) and abs(abs(eq) - 1) < 1e-12)

# ---------------------------------------------------------------------------------------------------- 6. A(t)
ok_A0 = ok_pos = ok_der = True
for trial in range(30):
    d, dB = 2, int(rng.integers(2, 4))
    U = random_unitary(d * dB, rng)
    tau = random_density(dB, rng)
    beta = rng.uniform(0.3, 2)
    H = np.diag([0.0, rng.uniform(0.2, 2)])
    zeta = random_density(dB, rng)
    LB = mfun(zeta, lambda w: -np.log2(w))
    sq = np.kron(np.eye(d), mfun(tau, np.sqrt))

    def Aop(t):
        E = mfun(beta * H, lambda w: np.exp(t * w / 2))
        Ei = mfun(beta * H, lambda w: np.exp(-t * w / 2))
        Ut = np.kron(E, np.eye(dB)) @ U @ np.kron(Ei, np.eye(dB))
        mid = sq @ Ut.conj().T @ np.kron(np.eye(d), mfun(LB, lambda w: 2.0 ** (t * w))) @ Ut @ sq
        return np.einsum("aibi->ab", mid.reshape(d, dB, d, dB))
    Gam = lambda X: ptrace(U @ np.kron(X, tau) @ U.conj().T, [d, dB], [1])
    GamStar = lambda Y: np.array([[np.trace(Y @ Gam(np.outer(np.eye(d)[i], np.eye(d)[j]))) for j in range(d)]
                                  for i in range(d)]).T
    Phi = lambda X: ptrace(U @ np.kron(X, tau) @ U.conj().T, [d, dB], [0])
    PhiStar = lambda Y: np.array([[np.trace(Y @ Phi(np.outer(np.eye(d)[i], np.eye(d)[j]))) for j in range(d)]
                                  for i in range(d)]).T
    ok_A0 &= np.allclose(Aop(0.0), np.eye(d), atol=1e-12)
    ok_pos &= all(np.linalg.eigvalsh(herm(Aop(t))).min() > -1e-12 for t in (0.1, 0.5, 2.0))
    h = 1e-5
    deriv = (Aop(h) - Aop(-h)) / (2 * h)
    ok_der &= np.allclose(deriv, LN2 * GamStar(LB) + beta * (PhiStar(H) - H), atol=1e-6)
R.check("A(0) = I, A(t) >= 0, A'(0) = ln2 Gamma^*(L_B) + beta(Phi^*(H) - H) (30 random dilations)",
        bool(ok_A0 and ok_pos and ok_der))
# similarity Q(t) L(U) Q(t)^{-1} = L(U_t): coefficient of T_u is multiplied by e^{-t beta u.omega/2}
omega = np.array([1.0, math.sqrt(3)])
labels = [(0, 0), (1, 0), (0, 1)]
Hd = np.array([np.dot(l, omega) for l in labels])
ok = True
for _ in range(20):
    U = random_unitary(3, rng)
    t, beta = rng.uniform(0, 2), rng.uniform(0.2, 2)
    Ut = np.diag(np.exp(t * beta * Hd / 2)) @ U @ np.diag(np.exp(-t * beta * Hd / 2))
    for e, f in itertools.product(range(3), repeat=2):
        u = np.subtract(labels[f], labels[e])
        ok &= abs(U[e, f] * math.exp(-t * beta * np.dot(u, omega) / 2) - Ut[e, f]) < 1e-12
R.check("energy register: Q(t) L(U) Q(t)^{-1} = L(U_t), entry by entry", bool(ok))

# ---------------------------------------------------------------------------------------------------- 7. formation
ok = True
for mC, K, Lf in [(4, 2, 3), (6, 3, 2), (8, 2, 4), (9, 3, 3)]:
    deg = [mC ** j * K ** (Lf - j) for j in range(Lf + 1)]
    wts = [Fraction(deg[j]) * Fraction(K, mC) ** j for j in range(Lf + 1)]       # e^{-beta j W_f} = (K/m_C)^j
    ok &= len(set(wts)) == 1
    # swap C (x) |1> (x) R_j  <->  ran(Pi) (x) |0> (x) R_{j+1}, j < L_f: equal energy (j+1) W_f, equal dimension
    for j in range(Lf):
        ok &= mC * deg[j] == K * deg[j + 1]
    # explicit permutation on labels: source (c, 1, j, r) with c < m_C, r < deg[j]; target (k, 0, j+1, r') with k < K
    src = {}
    for j in range(Lf):
        idx = 0
        for c in range(mC):
            for r in range(deg[j]):
                kk, rr = divmod(idx, deg[j + 1])
                src[(c, 1, j, r)] = (kk, 0, j + 1, rr)
                idx += 1
    ok &= len(set(src.values())) == len(src) and all(t[2] == s[2] + 1 for s, t in src.items())
    # success probability: flat C, qubit excited, reservoir Gibbs (uniform over levels)
    p_level = Fraction(1, Lf + 1)
    p_succ = sum(p_level for j in range(Lf))
    ok &= p_succ == 1 - Fraction(1, Lf + 1)
R.check("formation: equal Gibbs weight per reservoir level, equal-energy equal-dimension swaps, an injective "
        "energy-raising-by-one-level map, success probability 1 - 1/(L_f + 1)", bool(ok))

# ---------------------------------------------------------------------------------------------------- 8. converter
bs, th = sp.symbols("bs theta", positive=True)
expr = (1 - (1 - sp.exp(-bs)) / 2) * sp.exp(bs) - 1
R.check("converter: with theta = (1 - e^{-beta s})/2, (1 - theta) e^{beta s} - 1 = (e^{beta s} - 1)/2 > 0",
        sp.simplify(expr - (sp.exp(bs) - 1) / 2) == 0)
N_, u_, w_, pa, qc = sp.symbols("N u w P Q", positive=True)
ratio = (N_ * sp.exp(u_ - w_) * qc) / (N_ * sp.exp(u_) * pa)
R.check("converter ratio: N e^{beta(u.omega - w)} Z_Q / (N e^{beta u.omega} Z_P) = e^{beta s} when beta w = ln(Z_Q/Z_P) - beta s",
        sp.simplify(ratio.subs(w_, sp.log(qc / pa) - bs) - sp.exp(bs)) == 0)
n_, v_, sig_, g_, DL, mC_, rn = sp.symbols("n v sigma g D_L m_C r_n", positive=True)
K_ = sp.Symbol("K", positive=True)
Wf = sp.log(mC_ / K_)                                       # beta W_f
wn = sp.log(mC_ / ((n_ + 1) * 2 ** rn * DL * 2 ** (n_ * (v_ + sp.Symbol("gam")))))      # beta w_n without slack
diff = sp.simplify((Wf - wn) / sp.log(2) - (n_ * (v_ + sp.Symbol("gam")) - sp.log(K_, 2) + rn + sp.log(n_ + 1, 2) + sp.log(DL, 2)))
R.check("net work: beta(W_f - w_n)/ln2 = n(v + gamma) - log2 K + r_n + log2(n+1) + log2 D_L (symbolic)",
        sp.simplify(sp.expand_log(diff, force=True)) == 0)
ok = True
over = []
for n in (10 ** 4, 10 ** 6, 10 ** 8, 10 ** 12):
    gam = n ** -0.25
    v, sig = 1.3, 0.8
    gval = v - sig
    r_n = math.ceil(3 * n * gam) + 4
    D_L = (4 * (n + 1) + 1) ** 2                            # register box polynomial in n (r = 2, A_max = 1)
    per = (n * (v + gam) - math.ceil(n * (sig + 2 * gam)) + r_n + math.log2(n + 1) + math.log2(D_L)) / n
    over.append((per - gval) / gam)
ok = all(1.5 < o < 3.5 for o in over)
R.check("the per-use overhead of the net work is O(n^{-1/4}) (about 2 gamma_n)", ok, ", ".join(f"{o:.3f}" for o in over))

# ---------------------------------------------------------------------------------------------------- 9. Appendix B
def frame(m):
    vecs = [np.eye(m)[i].astype(complex) for i in range(m)]
    for i in range(m):
        for k in range(i + 1, m):
            vecs.append(np.eye(m)[i] + np.eye(m)[k])
            vecs.append(np.eye(m)[i] + 1j * np.eye(m)[k])
    vecs = [v / np.linalg.norm(v) for v in vecs]
    S = sum(np.outer(v, v.conj()) for v in vecs)
    Sih = mfun(S, lambda w: 1 / np.sqrt(w))
    return [Sih @ v for v in vecs]


ok = True
for m in range(1, 6):
    eff = frame(m)
    ok &= len(eff) == m * m
    ok &= np.allclose(sum(np.outer(v, v.conj()) for v in eff), np.eye(m), atol=1e-12)
    span = np.array([np.outer(v, v.conj()).reshape(-1) for v in eff])
    ok &= np.linalg.matrix_rank(span, tol=1e-10) == m * m
R.check("the normalized frame gives m^2 rank-one effects summing to I that span all m x m matrices (m <= 5)", bool(ok))
ok = True
for d in (2, 3):
    for _ in range(10):
        H = np.diag(np.round(rng.uniform(0, 3, d), 1))
        HY = -np.kron(H.T, np.eye(d)) + np.kron(np.eye(d), H)
        ev = np.round(np.diag(HY), 9)
        ms = [int(np.sum(ev == e)) for e in np.unique(ev)]
        ok &= sum(x * x for x in ms) <= d ** 4 and sum(ms) == d * d
        # instrument: sqrt(1 - g) I and sqrt(g)|u_j><v_x| inside each eigenspace, u_j fixed per eigenspace
        gam = 0.2
        K = [math.sqrt(1 - gam) * np.eye(d * d)]
        for e in np.unique(ev):
            idx = np.where(ev == e)[0]
            u = np.zeros(d * d, dtype=complex)
            u[idx[0]] = 1
            for v in frame(len(idx)):
                vv = np.zeros(d * d, dtype=complex)
                vv[idx] = v
                K.append(math.sqrt(gam) * np.outer(u, vv.conj()))
        ok &= np.allclose(sum(k.conj().T @ k for k in K), np.eye(d * d), atol=1e-12)
        ok &= all(np.allclose(k @ HY, HY @ k, atol=1e-12) for k in K)
R.check("L = sum_j m_j^2 <= d^4 for H_Y, and the test instrument is trace preserving with every Kraus operator "
        "commuting with H_Y", bool(ok))
ok, closeness = True, []
for n in (20, 50, 100, 200, 400, 800):
    for gamma in (0.01, 0.05, 0.1, 0.2, 0.24):
        for L in (1, 4, 16, 81):
            lhs = sum(math.comb(n, k) * L ** k for k in range(0, math.floor(2 * gamma * n) + 1))
            theta = h2(2 * gamma) + 2 * gamma * math.log2(L)
            ok &= math.log2(lhs) <= n * theta + 1e-9
            if n == 800:
                closeness.append(math.log2(lhs) / (n * theta))
R.check("sum_{k <= 2 gamma n} C(n,k) L^k <= 2^{n theta_gamma}, theta_gamma = h(2 gamma) + 2 gamma log2 L (exact sums)",
        ok and max(closeness) > 0.98, f"at n = 800 the exponents agree to {max(closeness):.4f}")
ok = True
for _ in range(500):
    EB = np.sort(rng.uniform(0, 5, 6))
    beta = rng.uniform(0.1, 3)
    Ei = EB[rng.integers(0, 6)]
    sel = rng.random(6) < 0.5
    if not sel.any():
        continue
    W = Ei - EB[sel].min()
    bb = math.log2(np.sum(np.exp(-beta * EB[sel])) / math.exp(-beta * Ei))
    ok &= bb <= beta * W / LN2 + math.log2(sel.sum()) + 1e-12
R.check("battery remark: a projector of rank R_B at energies >= E_i - W has b_beta <= beta W/ln2 + log2 R_B", bool(ok))

# ---------------------------------------------------------------------------------------------------- 10. constants
ok, worst = True, 0.0
for r in np.geomspace(1e-6, 1, 400):
    for frac in np.linspace(1e-6, 1, 50):
        dl = r / 64 * frac
        F = (math.sqrt(r) - math.sqrt(2) * dl) / math.sqrt(r + dl)
        P2 = 1 - F * F
        ok &= P2 <= 4 * dl / r + 1e-15 and 4 * dl / r <= 1 / 16 + 1e-15
        worst = max(worst, P2 / (4 * dl / r))
R.check("Lemma postproj: squared purified distance 1 - F^2 <= 4 delta/r <= 1/16 for delta <= r/64", ok and worst > 0.25,
        f"largest ratio {worst:.3f}")
ok = True
for _ in range(100):
    dk = rng.integers(1, 6, int(rng.integers(1, 6)))
    ks = rng.uniform(0, 4, len(dk))
    beta, s_ = rng.uniform(0.1, 3), rng.uniform(0, 1)
    ZK = float(np.sum(dk * np.exp(-beta * ks)))
    a0 = (1 - s_) / (2 * ZK)
    ok &= abs(a0 * ZK - (1 - s_) / 2) < 1e-15
R.check("Lemma cap at s = 1/2: the smoothing term 2 log2(2/(1 - s)) is the constant 4 of eq. (cap); the rejected trace "
        "a_0 sum_k d_k e^{-beta k} with a_0 = (1 - s)/(2 Z_K) is (1 - s)/2",
        sp.simplify(2 * sp.log(2 / (1 - sp.Rational(1, 2)), 2) - 4) == 0 and ok)
p_ = sp.symbols("p", positive=True)
expr = 1 - 2 * sp.log((p_ / 64) * p_, 2) - (13 + 4 * sp.log(1 / p_, 2))
R.check("assembly: with delta = p/64 and p_G = p, 1 - 2 log2(delta p_G) = 13 + 4 log2(1/p)",
        sp.simplify(sp.expand_log(expr, force=True)) == 0)
ok = True
for _ in range(2000):
    dprime = rng.uniform(1e-3, 1)
    Cf = 10 ** rng.uniform(-1, 2)
    a = min(dprime / 16, dprime ** 2 / (256 * Cf ** 2))
    N0 = (8 * Cf * math.sqrt(13) / dprime + 1) ** 2 + 32 / dprime
    for n in (N0, 2 * N0, 10 * N0):
        lp = a * n                                          # log2(1/p) at its largest allowed value
        rhs = n * (-dprime / 2) - Cf * math.sqrt(n * (13 + 4 * lp)) - 2 * lp - 4
        ok &= rhs > n * (-dprime)                           # T_rt cancels on both sides
R.check("assembly: with a = min{delta'/16, delta'^2/(256 C_f^2)} the right side exceeds n(T - delta') once "
        "n >= (8 C_f sqrt13/delta' + 1)^2 + 32/delta' (2000 random delta', C_f)", bool(ok))
R.close()
