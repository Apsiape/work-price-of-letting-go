"""What the clock costs and the lottery (Sections "Setting", "The dichotomy", "What the clock costs", "The clock's
energy is a lottery"; Appendices "The range of the baths", "The clock's energy", "What the clock costs").

Checks:
  1. g > 0: the identity sum_ij |U_ji|^2 (h_j - h_i)^2 = -2 sum_i h_i d_i, Tr D = 0, and g > 0 exactly when [U, H] != 0;
  2. the Hadamard gate: D = (E/2)(Z - X), lambda_max(D) = E/sqrt2 (work n E/sqrt2), g = E; the witness of Theorem
     "dichotomy" (a) vanishes exactly for time-covariant channels;
  3. the rare-excitation primitive: the rotation by sqrt(B/M) takes up the energy B on average and disturbs the payload
     channel by at most 3||B||/(2M) in half diamond distance;
  4. the capital lemma: A*A <= I, [H_C, A] = -qA, Tr gamma A*A = e^{-beta q} Tr gamma AA*, and
     D(alpha||gamma) >= beta q |Tr alpha A|^2 - ln 2, with A = Lambda^*(L) for a covariant Lambda;
  5. the Hadamard tester: L = Z^{(x)K} (x) |q1><q0| lowers energy by KE, has expectation 1/2 on the ideal output, the
     tester is stationary, and the constant chain m = floor(1/(8(eps+eta))), K = mn gives n E/(256(eps+eta));
  6. the baths: decoupling T(sigma_a, sigma_b) <= 2 sqrt(2 eps) on near-unitary dilations, |Tr H(sigma_a - sigma_b)| <=
     span(H) T, the exponential moments E e^{+-Q/(2 q0)} <= e^{2(sqrt e - 1) A} for bounded-span interactions, and the
     step from these two facts to the displayed bound on A_n;
  7. the lottery: the Hoeffding exponent, the two-window lemma, the Hellinger step for the standard deviation;
  8. the cheaper clock: emission counts, and the block of k = ceil(M/(E tanh(beta E/2))) qubits of gap E.
"""
from fractions import Fraction
import math

import numpy as np
from scipy.linalg import expm

from qtools import (HAD, X, Z, Report, choi_of, dag, diamond_half, dm, herm, kron, ket, opnorm, powm_h, ptrace,
                    random_density, random_unitary, relent, trace_norm)

R = Report("What the clock costs, and the lottery")
rng = np.random.default_rng(20261012)

# ---------------------------------------------------------------------------------------------------------------------
# 1. g > 0
worst_id, worst_tr, ok_pos, near = 0.0, 0.0, True, 0
for trial in range(600):
    d = int(rng.integers(2, 5))
    h = rng.integers(0, 3, d).astype(float) if trial % 3 == 0 else rng.uniform(0, 2, d)
    H = np.diag(h).astype(complex)
    kind = trial % 4
    if kind == 0:
        U = random_unitary(d, rng)
    elif kind == 1:                      # near the identity: barely non-commuting
        K = herm(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)))
        U = expm(1j * 10 ** rng.uniform(-4, -1) * K)
    elif kind == 2:                      # commuting with H: block diagonal in the eigenspaces of H
        U = np.zeros((d, d), dtype=complex)
        for val in np.unique(h):
            idx = np.where(h == val)[0]
            U[np.ix_(idx, idx)] = random_unitary(len(idx), rng)
    else:
        U = random_unitary(d, rng) @ np.diag(np.exp(1j * rng.uniform(0, 6, d)))
    D = dag(U) @ H @ U - H
    dd = np.real(np.diag(D))
    lhs = sum(abs(U[j, i]) ** 2 * (h[j] - h[i]) ** 2 for i in range(d) for j in range(d))
    worst_id = max(worst_id, abs(lhs + 2 * np.dot(h, dd)))
    worst_tr = max(worst_tr, abs(np.trace(D)))
    comm = opnorm(U @ H - H @ U)
    g = dd.max() - dd.min()
    if comm > 1e-6:
        ok_pos &= g > 0
        near += comm < 1e-2
    else:
        ok_pos &= g < 1e-9
R.check("sum_ij |U_ji|^2 (h_j - h_i)^2 = -2 sum_i h_i d_i and Tr D = 0 (600 random U, H)",
        worst_id < 1e-10 and worst_tr < 1e-10, f"{worst_id:.1e}, {worst_tr:.1e}")
R.check("g > 0 exactly when U does not commute with H, including barely non-commuting U",
        ok_pos and near >= 50, f"{near} instances with ||[U,H]|| < 1e-2")

# 2. Hadamard
E = 1.7
Hq = np.diag([0, E]).astype(complex)
Dh = dag(HAD) @ Hq @ HAD - Hq
ev = np.linalg.eigvalsh(Dh)
R.check("Hadamard: D = (E/2)(Z - X), lambda_max(D) = E/sqrt2, lambda_max - lambda_min = sqrt2 E, g = E",
        np.allclose(Dh, E / 2 * (Z - X)) and abs(ev[-1] - E / math.sqrt(2)) < 1e-12
        and abs(ev[-1] - ev[0] - math.sqrt(2) * E) < 1e-12 and abs(np.real(Dh[0, 0] - Dh[1, 1]) - E) < 1e-12)

# Theorem "dichotomy" (a): the witness (1/4) sup_t ||J - e^{-itG} J e^{itG}||_1, G = H_O - H_I^T, vanishes exactly for
# time-covariant channels (random channels, and their exact twirls over integer spectra)
ok_dich, cnt_dich = True, 0
for trial in range(60):
    d = int(rng.integers(2, 4))
    h = rng.integers(0, 3, d).astype(float)
    Hd = np.diag(h)
    kr = [rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)) for _ in range(2)]
    sm = sum(dag(k) @ k for k in kr)
    w_, v_ = np.linalg.eigh(sm)
    kr = [k @ (v_ * w_ ** -0.5) @ dag(v_) for k in kr]
    T = 11                                   # exceeds the largest frequency difference 4, so the twirl is exact
    def chan(r, twirl):
        if not twirl:
            return sum(k @ r @ dag(k) for k in kr)
        out = 0
        for t in 2 * math.pi * np.arange(T) / T:
            Ut = np.diag(np.exp(-1j * h * t))
            out = out + Ut @ sum(k @ (dag(Ut) @ r @ Ut) @ dag(k) for k in kr) @ dag(Ut) / T
        return out
    for twirl in (False, True):
        J = choi_of(lambda r: chan(r, twirl), d)
        G = np.kron(np.eye(d), Hd) - np.kron(Hd.T, np.eye(d))
        wit = max(trace_norm(J - expm(-1j * t * G) @ J @ expm(1j * t * G)) / 4 for t in np.linspace(0.1, 6.2, 40))
        Ut = np.diag(np.exp(-1j * h * 0.77))
        rr = random_density(d, rng)
        cov = opnorm(chan(Ut @ rr @ dag(Ut), twirl) - Ut @ chan(rr, twirl) @ dag(Ut))
        ok_dich &= (wit < 1e-10) == (cov < 1e-10) and (wit < 1e-10 or not twirl)
        cnt_dich += wit > 1e-3
R.check("Theorem 'dichotomy' (a): the witness (1/4) sup_t ||J - e^{-itG} J e^{itG}||_1 vanishes exactly for the "
        "time-covariant channels (random channels and their exact twirls)", ok_dich and cnt_dich >= 30,
        f"{cnt_dich} non-covariant channels with a positive witness")

# 3. rare-excitation primitive
worst_e, ratio_dist, cnt = 0.0, 0.0, 0
for trial in range(40):
    d = int(rng.integers(2, 4))
    Bm = random_density(d, rng) * rng.uniform(0.2, 3)
    M = 10 ** rng.uniform(0.7, 2.5) * opnorm(Bm)
    C0 = powm_h(np.eye(d) - Bm / M, 0.5)
    F0 = powm_h(Bm / M, 0.5)
    J = np.block([[C0, -F0], [F0, C0]])            # G basis (g, e) outermost
    unit = opnorm(dag(J) @ J - np.eye(2 * d)) < 1e-12
    rho = random_density(d, rng)
    out = J @ np.kron(dm(ket((0,))), rho) @ dag(J)
    pe = np.real(np.trace(out[d:, d:]))
    worst_e = max(worst_e, abs(M * pe - np.real(np.trace(rho @ Bm))), 0 if unit else 1)
    lam = lambda r: C0 @ r @ C0 + F0 @ r @ F0
    dist = diamond_half(choi_of(lam, d), choi_of(lambda r: r, d), d, d)
    ratio_dist = max(ratio_dist, dist / (3 * opnorm(Bm) / (2 * M)))
    cnt += 1
R.check("the rotation with blocks sqrt(I - B/M), sqrt(B/M) is unitary and takes up the energy Tr rho B on average",
        worst_e < 1e-12, f"{worst_e:.1e}")
R.check("its payload channel C0 rho C0 + F0 rho F0 is within 3||B||/(2M) of the identity (half diamond, SDP)",
        ratio_dist <= 1 + 1e-6 and ratio_dist > 0.1, f"largest ratio to the bound {ratio_dist:.3f} over {cnt} instances")

# ---------------------------------------------------------------------------------------------------------------------
# 4. the capital lemma
ok_struct, worst_slack, informative = True, np.inf, 0
for trial in range(400):
    dC = int(rng.integers(3, 7))
    eC = np.sort(rng.integers(0, 4, dC)).astype(float)
    q = float(rng.integers(1, 3))
    beta = rng.uniform(0.2, 12)
    HC = np.diag(eC)
    gam = np.diag(np.exp(-beta * eC))
    gam /= np.trace(gam)
    if trial % 2 == 0:
        # A = Lambda^*(L) for a covariant channel Lambda from C to a qubit pair Y, by an exact twirl
        eY = np.array([0.0, q, q, 2 * q])
        dY = 4
        kr = [rng.standard_normal((dY, dC)) + 1j * rng.standard_normal((dY, dC)) for _ in range(3)]
        s = sum(dag(k) @ k for k in kr)
        w, v = np.linalg.eigh(s)
        isq = (v * w ** -0.5) @ dag(v)
        kr = [k @ isq for k in kr]
        T = int(2 * (eC.max() + eY.max())) + 3
        ts = 2 * math.pi * np.arange(T) / T
        L = np.zeros((dY, dY), dtype=complex)
        for x in range(dY):
            for y in range(dY):
                if abs(eY[x] - (eY[y] - q)) < 1e-12:
                    L[x, y] = rng.standard_normal() + 1j * rng.standard_normal()
        L /= opnorm(L)
        A = np.zeros((dC, dC), dtype=complex)
        for t in ts:
            UC, UY = np.diag(np.exp(-1j * eC * t)), np.diag(np.exp(-1j * eY * t))
            Lt = dag(UY) @ L @ UY                      # e^{i H_Y t} L e^{-i H_Y t}
            A += UC @ sum(dag(k) @ Lt @ k for k in kr) @ dag(UC) / T
    else:
        A = np.zeros((dC, dC), dtype=complex)
        for x in range(dC):
            for y in range(dC):
                if abs(eC[x] - (eC[y] - q)) < 1e-12:
                    A[x, y] = rng.standard_normal() + 1j * rng.standard_normal()
        if opnorm(A) < 1e-12:
            continue
        A *= rng.uniform(0.3, 1) / opnorm(A)
    ok_struct &= np.max(np.linalg.eigvalsh(dag(A) @ A)) <= 1 + 1e-10
    ok_struct &= opnorm(HC @ A - A @ HC + q * A) < 1e-9
    lhs = np.real(np.trace(gam @ dag(A) @ A))
    ok_struct &= abs(lhs - math.exp(-beta * q) * np.real(np.trace(gam @ A @ dag(A)))) < 1e-12 and lhs <= math.exp(-beta * q) + 1e-12
    for _ in range(4):
        if rng.random() < 0.5:
            # pure states that make |Tr alpha A| large: top eigenvector of the Hermitian part of a random phase of A
            ph = np.exp(1j * rng.uniform(0, 2 * math.pi))
            w, v = np.linalg.eigh(herm(ph * A))
            alpha = dm(v[:, -1])
        else:
            alpha = random_density(dC, rng, rank=int(rng.integers(1, dC + 1)))
        alpha = (1 - 1e-13) * alpha + 1e-13 * np.eye(dC) / dC
        rhs = beta * q * abs(np.trace(alpha @ A)) ** 2 - math.log(2)
        D_ag = relent(alpha, gam)
        worst_slack = min(worst_slack, D_ag - rhs)
        informative += rhs > 0.5
R.check("A = Lambda^*(L): A*A <= I, [H_C, A] = -qA, Tr gamma A*A = e^{-beta q} Tr gamma A A* <= e^{-beta q}", ok_struct)
R.check("D(alpha||gamma_C) >= beta q |Tr alpha A|^2 - ln 2 (pure and mixed alpha)",
        worst_slack > -1e-9 and informative >= 100, f"{informative} instances with right side > 0.5, least slack {worst_slack:.3f}")

# 5. the Hadamard tester
ok_t = True
for K in range(1, 5):
    nq = K + 1
    dims = [2] * nq
    # tester: (|0^K>|q0> + |1^K>|q1>)/sqrt2, kept qubit with energies 0 (q0) and -KE (q1)
    Hout = sum(np.kron(np.kron(np.eye(2 ** i), Hq), np.eye(2 ** (K - 1 - i))) for i in range(K))
    Hkeep = np.diag([0, -K * E])
    HY = np.kron(Hout, np.eye(2)) + np.kron(np.eye(2 ** K), Hkeep)
    tester = (ket((0,) * K + (0,)) + ket((1,) * K + (1,))) / math.sqrt(2)
    ok_t &= np.allclose(HY @ tester, 0 * tester)
    plus, minus = np.array([1, 1]) / math.sqrt(2), np.array([1, -1]) / math.sqrt(2)
    ideal = (kron(*([plus] * K + [np.array([1, 0])])) + kron(*([minus] * K + [np.array([0, 1])]))) / math.sqrt(2)
    UK = kron(*([HAD] * K + [np.eye(2)]))
    ok_t &= np.allclose(UK @ tester, ideal)
    L = np.kron(kron(*([Z] * K)), np.outer([0, 1], [1, 0]))
    ok_t &= np.allclose(HY @ L - L @ HY, -K * E * L) and abs(opnorm(L) - 1) < 1e-12
    ok_t &= abs(np.vdot(ideal, L @ ideal) - 0.5) < 1e-12
    for _ in range(50):
        lam = 10 ** rng.uniform(-4, -0.5)
        rho = (1 - lam) * dm(ideal) + lam * random_density(2 ** nq, rng)
        delta = trace_norm(rho - dm(ideal)) / 2
        ok_t &= abs(np.trace(rho @ L)) >= 0.5 - 2 * delta - 1e-12
R.check("tester stationary, ideal output (|+>^K|q0> + |->^K|q1>)/sqrt2, L lowers energy by KE, <L> = 1/2, and "
        "|Tr rho L| >= 1/2 - 2 delta (K = 1..4)", ok_t)

ok_c, worst_ratio = True, np.inf
grid = sorted({Fraction(1, 16) * Fraction(i, 400) for i in range(1, 401)} |
              {Fraction(1, 8) / (Fraction(2) - Fraction(1, 10 ** k)) for k in range(1, 7)})
for zeta in grid:
    for share in (Fraction(0), Fraction(1, 3), Fraction(1, 2), Fraction(1)):
        eps, eta = zeta * share, zeta * (1 - share)
        m = math.floor(1 / (8 * zeta))
        delta = m * eps + (m - 1) * eta
        ok_c &= m >= 1 and delta <= Fraction(1, 8) and (Fraction(1, 2) - 2 * delta) ** 2 >= Fraction(1, 16)
        bound = Fraction(m, 16)                         # K E (1/2 - 2 delta)^2 / (nE) with K = mn
        ok_c &= bound >= 1 / (256 * zeta)
        worst_ratio = min(worst_ratio, float(bound * 256 * zeta))
R.check("eps + eta <= 1/16, m = floor(1/(8(eps+eta))): m eps + (m-1) eta <= 1/8 and m n E/16 >= n E/(256(eps+eta)) "
        "(exact rationals)", ok_c and worst_ratio < 1.001, f"least ratio {worst_ratio:.5f}")

# ---------------------------------------------------------------------------------------------------------------------
# 6. the baths
worst_dec, cnt_dec, worst_rng = 0.0, 0, 0.0
for trial in range(60):
    d = int(rng.integers(2, 4))
    dE = int(rng.integers(2, 4))
    U = random_unitary(d, rng)
    e0 = np.zeros((dE, 1))
    e0[0] = 1
    W = np.kron(U, e0) + 10 ** rng.uniform(-3, -0.7) * (rng.standard_normal((d * dE, d)) + 1j * rng.standard_normal((d * dE, d)))
    w, v = np.linalg.eigh(dag(W) @ W)
    W = W @ (v * w ** -0.5) @ dag(v)
    kr = [W.reshape(d, dE, d)[:, k, :] for k in range(dE)]
    chan = lambda r: sum(k @ r @ dag(k) for k in kr)
    eps = diamond_half(choi_of(chan, d), choi_of(lambda r: U @ r @ dag(U), d), d, d)
    Vq = random_unitary(d, rng)
    a, b = Vq[:, 0], Vq[:, 1]
    env = lambda x: ptrace(W @ dm(x) @ dag(W), [d, dE], [1])
    T = trace_norm(env(a) - env(b)) / 2
    worst_dec = max(worst_dec, T / (2 * math.sqrt(2 * eps)))
    cnt_dec += 1
    Henv = herm(rng.standard_normal((dE, dE)) + 1j * rng.standard_normal((dE, dE)))
    span = np.ptp(np.linalg.eigvalsh(Henv))
    worst_rng = max(worst_rng, abs(np.trace(Henv @ (env(a) - env(b)))) / (span * T))
R.check("decoupling: the environment states of two orthogonal inputs are within 2 sqrt(2 eps) (half trace distance)",
        worst_dec <= 1 + 1e-6, f"largest ratio {worst_dec:.3f} over {cnt_dec} near-unitary dilations")
R.check("|Tr H (sigma_a - sigma_b)| <= span(H) T(sigma_a, sigma_b), so R >= L_n/(2 sqrt(2 eps))",
        worst_rng <= 1 + 1e-9, f"largest ratio {worst_rng:.3f}")

# exponential moments of the heat for interactions on cells of energy span at most q0
worst_mom, inf_mom = 0.0, 0
for trial in range(300):
    q0 = rng.uniform(0.3, 2)
    ncell, dc = 2, 3
    cells = [np.sort(rng.uniform(0, q0, dc)) for _ in range(ncell)]
    cells = [c - c[0] for c in cells]
    HS = np.diag([0, rng.uniform(0, 3)])
    hb = np.array([sum(cells[c][idx[c]] for c in range(ncell)) for idx in np.ndindex(*[dc] * ncell)])
    HB = np.kron(np.eye(2), np.diag(hb))
    H0 = np.kron(HS, np.eye(dc ** ncell)) + HB
    beta = rng.uniform(0.1, 3)
    U = np.eye(2 * dc ** ncell, dtype=complex)
    A = 0.0
    for l in range(int(rng.integers(1, 6))):
        c = int(rng.integers(ncell))
        hm = herm(rng.standard_normal((2 * dc, 2 * dc)) + 1j * rng.standard_normal((2 * dc, 2 * dc)))
        hm *= rng.uniform(0.05, 2.5) / opnorm(hm)
        hr = hm.reshape(2, dc, 2, dc)
        if c == 0:
            hfull = np.einsum("aibj,kl->aikbjl", hr, np.eye(dc)).reshape(2 * dc * dc, 2 * dc * dc)
        else:
            hfull = np.einsum("aibj,kl->akibl j".replace(" ", ""), hr, np.eye(dc)).reshape(2 * dc * dc, 2 * dc * dc)
        tau = rng.uniform(0.1, 1.5)
        U = expm(-1j * (H0 + hfull) * tau) @ U
        A += opnorm(hm) * tau
    rhoS = random_density(2, rng)
    g = np.exp(-beta * hb)
    rho0 = np.kron(rhoS, np.diag(g / g.sum()))
    for lam in (1 / (2 * q0), -1 / (2 * q0)):
        mom = np.real(np.trace(expm(lam * HB) @ U @ expm(-lam * HB) @ rho0 @ dag(U)))
        worst_mom = max(worst_mom, math.log(mom) / (2 * (math.sqrt(math.e) - 1) * A))
        inf_mom += math.log(mom) > 0.02
R.check("E e^{+-Q/(2 q0)} <= e^{2(sqrt e - 1) A} for interactions on cells of energy span <= q0 (two-point heat law)",
        worst_mom <= 1 and inf_mom >= 100, f"{inf_mom} moments above e^0.02, largest log-ratio {worst_mom:.3f}")


# From the two ingredients to a bound on A_n. Two laws P, P' of Q at total variation delta whose exponential moments
# E e^{+-Q/s} are at most M (s = 2 q0) have |E_P Q - E_P' Q| <= 2 s delta ln(M/delta); a two-point pair attains this
# asymptotically. A weaker display, |E_P Q - E_P' Q| <= s delta (ln(M/delta) + 2), is not enough; the check below shows it.
def worst_pair(s_, d_, M_):
    a_ = s_ * math.log((M_ - 1 + d_) / d_)
    return 2 * d_ * a_                                   # mean difference of the two-point pair


ok_corr, tight = True, 0.0
for trial in range(4000):
    n_at = int(rng.integers(2, 8))
    xs = rng.uniform(-6, 6, n_at)
    p = rng.dirichlet(np.ones(n_at) * rng.uniform(0.2, 2))
    pp = rng.dirichlet(np.ones(n_at) * rng.uniform(0.2, 2))
    s_ = 1.0
    delta = 0.5 * np.abs(p - pp).sum()
    M_ = max(p @ np.exp(xs / s_), p @ np.exp(-xs / s_), pp @ np.exp(xs / s_), pp @ np.exp(-xs / s_))
    if delta < 1e-9:
        continue
    ok_corr &= abs(p @ xs - pp @ xs) <= 2 * s_ * delta * math.log(M_ / delta) + 1e-12
for M_ in (10.0, 1e2, 1e4, 1e8):
    for d_ in (1e-1, 1e-2, 1e-4):
        tight = max(tight, worst_pair(1.0, d_, M_) / (2 * d_ * math.log(M_ / d_)))
R.check("ingredients => |E_P Q - E_P' Q| <= 2 s delta ln(M/delta), so A_n >= [L_n/(8 q0 sqrt(2 eps)) - "
        "ln(1/(2 sqrt(2 eps)))]/(2(sqrt e - 1)); the two-point pair is tight", ok_corr and tight > 0.99,
        f"two-point pairs reach {tight:.4f} of the bound")
viol = [(M_, d_, worst_pair(1.0, d_, M_) / (d_ * (math.log(M_ / d_) + 2)))
        for M_ in (100.0, 1e4) for d_ in (1e-2, 1e-4)]
R.check("the corrected constant is needed: two-point laws exceed the weaker form s delta (ln(M/delta) + 2)",
        all(v[2] > 1 for v in viol), "factors " + ", ".join(f"{v[2]:.2f}" for v in viol))
eps_max = 1 / (8 * math.e ** 2)
mono = all((x + 1e-6) * math.log(M_ / (x + 1e-6)) >= x * math.log(M_ / x)
           for M_ in (1.0, 2.0, 50.0) for x in np.linspace(1e-6, 1 / math.e - 2e-6, 400))
R.check("for eps <= 1/(8e^2), delta = 2 sqrt(2 eps) <= 1/e <= M/e, where x ln(M/x) increases (M >= 1)",
        abs(2 * math.sqrt(2 * eps_max) - 1 / math.e) < 1e-15 and mono)

# ---------------------------------------------------------------------------------------------------------------------
# 7. the lottery
import sympy as sp
n_, g_, a_, sH = sp.symbols("n g a s", positive=True)
t_ = n_ * (g_ - 2 * a_) / 2
R.check("Hoeffding: deviation n(g - 2a)/2 of a sum of n terms in a range span(H) has exponent n(g-2a)^2/(2 span^2)",
        sp.simplify(2 * t_ ** 2 / (n_ * sH ** 2) - n_ * (g_ - 2 * a_) ** 2 / (2 * sH ** 2)) == 0)
ok_w = True
for trial in range(3000):
    k = int(rng.integers(3, 12))
    p, pp = rng.dirichlet(np.ones(k)), rng.dirichlet(np.ones(k))
    cut = int(rng.integers(1, k))
    W1, W2 = np.arange(k) < cut, np.arange(k) >= cut
    x1, x2 = 1 - p[W1].sum(), 1 - pp[W2].sum()
    ok_w &= x1 + x2 >= 1 - 0.5 * np.abs(p - pp).sum() - 1e-12
R.check("two laws at total variation delta that concentrate on disjoint windows, up to x1 and x2, have "
        "x1 + x2 >= 1 - delta (3000 random pairs)", ok_w)

worst_h, near_h = np.inf, 0
xs = np.linspace(-5, 5, 41)
for trial in range(6000):
    kind = trial % 3
    if kind == 0:
        p, q = rng.dirichlet(np.ones(41) * rng.uniform(0.05, 3)), rng.dirichlet(np.ones(41) * rng.uniform(0.05, 3))
    elif kind == 1:                                     # discretized Gaussians of equal width: the near-equality case
        sd = rng.uniform(0.4, 1.5)
        mu = rng.uniform(1e-3, 0.6) * sd
        p = np.exp(-(xs + mu / 2) ** 2 / (2 * sd ** 2))
        q = np.exp(-(xs - mu / 2) ** 2 / (2 * sd ** 2))
        p, q = p / p.sum(), q / q.sum()
    else:
        p = rng.dirichlet(np.ones(41))
        q = 0.7 * p + 0.3 * rng.dirichlet(np.ones(41) * 0.2)
    mp, mq = p @ xs, q @ xs
    sp_, sq_ = math.sqrt(p @ (xs - mp) ** 2), math.sqrt(q @ (xs - mq) ** 2)
    bc = float(np.sum(np.sqrt(p * q)))
    if bc >= 1 - 1e-13 or abs(mp - mq) < 1e-12:
        continue
    ratio = (sp_ + sq_) / (abs(mp - mq) * bc / math.sqrt(1 - bc ** 2))
    worst_h = min(worst_h, ratio)
    near_h += ratio < 1.01
R.check("Hellinger step: sigma_P + sigma_Q >= |mu_P - mu_Q| BC/sqrt(1 - BC^2), so with BC >= sqrt(1 - 16 eps) one "
        "standard deviation is at least |mu_P - mu_Q| sqrt(1 - 16 eps)/(8 sqrt eps)",
        worst_h >= 1 - 1e-9 and near_h >= 100, f"least ratio {worst_h:.5f}, {near_h} cases within 1%")
eps_s = sp.symbols("epsilon", positive=True)
y = sp.sqrt(1 - 16 * eps_s)
R.check("sqrt(1-16 eps)/(2 sqrt(1 - (1 - 16 eps))) = sqrt(1-16 eps)/(8 sqrt eps)",
        sp.simplify(y / (2 * sp.sqrt(1 - y ** 2)) - y / (8 * sp.sqrt(eps_s))) == 0)

# ---------------------------------------------------------------------------------------------------------------------
# 8. the cheaper clock
ok_j, near_j = True, 0
for trial in range(300):
    n = int(rng.integers(3, 25))
    pmax = 10 ** rng.uniform(-3, -0.5)
    # emission probability given the past may depend on the number of earlier emissions, but is at most pmax
    probs = rng.uniform(0.3, 1, (n, n + 1)) * pmax if trial % 2 else np.full((n, n + 1), pmax)
    dist = np.zeros(n + 1)
    dist[0] = 1
    for t in range(n):
        new = np.zeros(n + 1)
        for j in range(t + 1):
            new[j] += dist[j] * (1 - probs[t, j])
            new[j + 1] += dist[j] * probs[t, j]
        dist = new
    js = np.arange(n + 1)
    lam = n * pmax
    ok_j &= dist @ js ** 2 <= lam + lam ** 2 + 1e-12
    for Kc in range(0, 6):
        tail = dist[Kc + 1:].sum()
        ok_j &= tail <= lam ** (Kc + 1) / math.factorial(Kc + 1) + 1e-15
    near_j += (trial % 2 == 0) and dist @ js ** 2 > 0.95 * (lam + lam ** 2)
R.check("emissions with probability at most b/M given the past: E J^2 <= nb/M + (nb/M)^2 and "
        "Pr(J > K_c) <= (nb/M)^{K_c+1}/(K_c+1)! (exact laws, adaptive probabilities)", ok_j and near_j >= 50,
        f"{near_j} cases within 5% of the second-moment bound")
bE = sp.symbols("bE", positive=True)
pe = 1 / (1 + sp.exp(bE))
R.check("flipping a Gibbs qubit of gap E raises its mean energy by E tanh(beta E/2), so k = ceil(M/(E tanh(beta E/2))) "
        "qubits flipped together take up at least M",
        sp.simplify(((1 - 2 * pe) - sp.tanh(bE / 2)).rewrite(sp.exp)) == 0)
R.close()
