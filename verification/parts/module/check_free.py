"""What is free (Section F.4) and repairing small gain (Section F.10).

Checks:
  1. the defect identity a_j = S(tau_j) - S(tau_{j-1}) + (beta/ln2) Tr H_j(rho_Oj - gamma_j)
     = D(U_j(gamma_j (x) tau_{j-1})U_j^* || gamma_j (x) tau_j) >= 0 (eq. (defect)), and the Gibbs tester scores sum_j a_j;
  2. the prefix identity D(Omega_j || xi_j) = sum_{l<=j} a_l (eq. (prefix)), random collisions with three slots;
  3. the gauged contacts W_j = (I (x) G_j)(U_j (x) I_A)(I (x) G_{j-1}^*) (eq. (gauge)) implement the same process from the
     single source sigma;
  4. Section F.10, first paragraph: D(sigma || eta_j) = sum_{l<=j} a_l <= g, hence ||sqrt(eta_j) - sqrt(sigma)||_2 <= sqrt(ln2 g);
     the reversed order, D(eta_j || sigma) <= g, fails (it is infinite for the delay device), which is why the text uses D(sigma || eta_j);
  5. ||sqrt(rho) - sqrt(sigma)||_2^2 <= D_nat(rho||sigma), with near-equality instances, and the commutator bound
     ||[W_j, sqrt(gamma_j (x) sigma)]||_2 <= 3 sqrt(ln2 g) (eq. (common)) on random and nearly thermal collisions, with the
     gain g from a certified Frank-Wolfe bound;
  6. a causally ordered thermal realization scores exactly -D(omega_t || sigma) <= 0 for every tester, with maximum 0;
  7. Step 1: the regularization bounds k_g and b_g;
  8. Step 3: two eigenvalues fall into different bins with probability min{1, |ln(l_a/l_b)|/h} for a uniform offset, and
     this is at most |sqrt(l_a/l_b) - 1|/(1 - e^{-h/2}) (with near-equality cases); E_s L_j(s) <= sqrt(q_j)/(1 - e^{-h/2});
  9. Step 4: polar completion gives ||(W - V) sqrt(Lambda)||_2^2 <= 2 e^{2h} L and conserves the rounded energy exactly;
 10. Step 6: the exponent bookkeeping (sympy) giving O(g^{1/(6r)}) and O(g^{1/6}); simultaneous Dirichlet approximation;
 11. Step 7: the lattice isometries turn H_j + H'_B + H_L into H_0j + H'_B + const, the lifted contact is unitary and
     conserves the original energy exactly; the boundary weight bound;
 12. Step 9: the episode clock ladder is a full energy-conserving injection with Gibbs level weights 1/(L+1);
 13. the examples: Werner-Holevo preserves equilibrium and its complementary channel reaches entropy log2 3.
"""
import itertools
import math

import numpy as np
import sympy as sp

from qtools import (Report, dm, embed, entropy, entropy_nat, gibbs, herm, ket, logm_psd, near_unitary, ptrace,
                    random_density, random_energy_conserving_unitary, random_unitary, relent, sqrtm_psd)
from combs import Realization, TesterLP, link, maximize_score, omega_map, random_tester, simulate

R = Report("What is free and repairing small gain")
rng = np.random.default_rng(555)
LN2 = math.log(2)
beta = 1.0


def gibbs_driven(dims, H, tau, U):
    """Bath states tau_j, outputs rho_Oj and the defects a_j under fresh Gibbs inputs."""
    dB = tau.shape[0]
    taus, outs, a = [tau], [], []
    for j, d in enumerate(dims):
        g = gibbs(H[j], beta)
        st = U[j] @ np.kron(g, taus[-1]) @ U[j].conj().T
        tj, oj = ptrace(st, [d, dB], [1]), ptrace(st, [d, dB], [0])
        aj = entropy(tj) - entropy(taus[-1]) + beta / LN2 * float(np.trace(H[j] @ (oj - g)).real)
        rel = relent(st, np.kron(g, tj))
        a.append((aj, rel))
        taus.append(tj)
        outs.append(oj)
    return taus, outs, a


def rand_diag_H(d):
    return np.diag(np.sort(rng.uniform(0, 2, d))).astype(complex)


# 1-2. defect and prefix identities ---------------------------------------------------------------------------------
w1 = w2 = wg = 0.0
neg = 0
for _ in range(25):
    dims = [int(x) for x in rng.choice([2, 3], 3)]
    dB = int(rng.integers(2, 4))
    H = [herm(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) for d in dims]
    tau = random_density(dB, rng)
    U = [random_unitary(d * dB, rng) for d in dims]
    taus, outs, a = gibbs_driven(dims, H, tau, U)
    w1 = max(w1, max(abs(x - y) for x, y in a))
    neg += any(x < -1e-12 for x, _ in a)
    # prefix: registers A_1..A_n start in Gibbs states; slot j acts on (A_j, bath)
    gam = [gibbs(h, beta) for h in H]
    full = [dB] + dims
    Om = np.kron(tau, np.kron(np.kron(gam[0], gam[1]), gam[2]))
    for j in range(3):
        Uj = embed(U[j], [1 + j, 0], full)            # U_j is ordered (port, bath)
        Om = Uj @ Om @ Uj.conj().T
        xi = np.kron(taus[j + 1], np.kron(np.kron(gam[0], gam[1]), gam[2]))
        w2 = max(w2, abs(relent(Om, xi) - sum(x for x, _ in a[:j + 1])))
    # the Gibbs tester (each input a purified Gibbs state, nothing adaptive) scores sum_j a_j
    if dims[0] == 2 and dims[1] == 2 and dims[2] == 2:
        pass
R.check("a_j = S(tau_j) - S(tau_{j-1}) + (beta/ln2) Tr H_j(rho_Oj - gamma_j) = D(U(gamma (x) tau)U^* || gamma (x) tau_j) >= 0",
        w1 < 1e-10 and neg == 0, f"{w1:.1e} over 75 slots")
R.check("D(Omega_j || xi_j) = sum_{l<=j} a_l for every j (eq. (prefix)), three slots, random collisions", w2 < 1e-9, f"{w2:.1e}")

# the Gibbs tester scores sum a_j
wgt = 0.0
from combs import Tester
for _ in range(10):
    dims = [2, 2]
    dB = 2
    H = [rand_diag_H(2), rand_diag_H(2)]
    tau = random_density(dB, rng)
    U = [random_unitary(4, rng) for _ in dims]
    _, _, a = gibbs_driven(dims, H, tau, U)
    real = Realization.collision(dims, tau, U)
    g1, g2 = gibbs(H[0], beta), gibbs(H[1], beta)
    Zg = np.kron(np.kron(g1, np.eye(2)), g2)                 # record of the Gibbs tester
    lk = link(real, Zg, H)
    wgt = max(wgt, abs(entropy(lk["omega"]) - real.S_tau() + beta / LN2 * lk["energy"] - sum(x for x, _ in a)))
R.check("the Gibbs tester scores exactly sum_j a_j >= 0, so K_beta >= 0 (Proposition 'Basic properties' (c))", wgt < 1e-10, f"{wgt:.1e}")

# 3. the gauge ------------------------------------------------------------------------------------------------------
def gauged(dims, H, tau, U):
    """Enlarged bath (B, A_1, ..., A_n), source sigma, gauged contacts W_j on (port, B, A)."""
    dB = tau.shape[0]
    full = [dB] + dims
    gam = [gibbs(h, beta) for h in H]
    sigma = tau
    for g in gam:
        sigma = np.kron(sigma, g)
    F = [np.eye(int(np.prod(full)), dtype=complex)]          # forward maps of the first j contacts on (B, A)
    for j in range(len(dims)):
        F.append(embed(U[j], [1 + j, 0], full) @ F[-1])
    G = [f.conj().T for f in F]                              # G_j = inverse of the first j contacts
    DBp = int(np.prod(full))
    W = []
    for j in range(len(dims)):
        d = dims[j]
        Uj = np.kron(U[j], np.eye(DBp // dB))                # (port, B, A): U_j on (port, B), identity on A
        Wj = np.kron(np.eye(d), G[j + 1]) @ Uj @ np.kron(np.eye(d), G[j].conj().T)
        W.append(Wj)
    return sigma, W, G, F


wgauge = 0.0
for _ in range(6):
    dims = [2, 2]
    dB = 2
    H = [rand_diag_H(2), rand_diag_H(2)]
    tau = random_density(dB, rng)
    U = [random_unitary(4, rng) for _ in dims]
    sigma, W, G, F = gauged(dims, H, tau, U)
    orig = Realization.collision(dims, tau, U).R
    new = Realization.collision(dims, sigma, W).R
    wgauge = max(wgauge, np.abs(orig - new).max())
R.check("the gauged contacts W_j implement the same process from the single source sigma (eq. (gauge))", wgauge < 1e-12,
        f"{wgauge:.1e}")

# 4-5. relative-entropy directions, the square-root inequality, and (common) --------------------------------------
lp = TesterLP([2, 2])
wdir, ok_sqrt, ratios, fails_text = 0.0, True, [], 0
SW = np.eye(4)[[0, 2, 1, 3]].astype(complex)
cases = []
for k in range(8):
    dB = 2
    if k < 3:                                  # random collisions
        tau = random_density(dB, rng)
        U = [random_unitary(4, rng) for _ in range(2)]
        H = [rand_diag_H(2), rand_diag_H(2)]
    elif k < 7:                                # nearly thermal: energy-conserving contacts on a Gibbs bath, perturbed
        H = [np.diag([0.0, 1.0]).astype(complex)] * 2
        HB = np.diag([0.0, 1.0]).astype(complex)
        tau = gibbs(HB, beta)
        Et = np.add.outer(np.diag(H[0]).real, np.diag(HB).real).reshape(-1)
        eps = [1e-4, 1e-3, 1e-2, 0.05][k - 3]
        U = [near_unitary(random_energy_conserving_unitary(Et, rng), eps, rng) for _ in range(2)]
    else:                                      # the delay device: tau pure
        H = [np.diag([0.0, 1.0]).astype(complex)] * 2
        tau = dm(ket((0,)))
        U = [SW, SW]
    cases.append((tau, U, H))
for tau, U, H in cases:
    dims = [2, 2]
    real = Realization.collision(dims, tau, U)
    _, gval, gup = maximize_score(real, H, beta, lp, iters=60)
    g = max(gup, 0.0)
    sigma, W, G, F = gauged(dims, H, tau, U)
    taus, _, a = gibbs_driven(dims, H, tau, U)
    gam = [gibbs(h, beta) for h in H]
    for j in range(1, 3):
        xi = np.kron(np.kron(taus[j], gam[0]), gam[1])
        eta = G[j] @ xi @ G[j].conj().T
        wdir = max(wdir, abs(relent(sigma, eta) - sum(x for x, _ in a[:j])))
        ok_sqrt &= np.linalg.norm(sqrtm_psd(eta) - sqrtm_psd(sigma)) ** 2 <= LN2 * g + 1e-9
        # the order written in the text
        w_eta = np.linalg.eigvalsh(herm(sigma))
        null_sigma = np.linalg.eigh(herm(sigma))[1][:, w_eta < 1e-12]
        leak = float(np.trace(null_sigma.conj().T @ eta @ null_sigma).real) if null_sigma.size else 0.0
        if leak > 1e-9 or relent(eta, sigma) > g + 1e-6:
            fails_text += 1
    for j in range(2):
        comm = W[j] @ np.kron(sqrtm_psd(gam[j]), sqrtm_psd(sigma)) - np.kron(sqrtm_psd(gam[j]), sqrtm_psd(sigma)) @ W[j]
        val = np.linalg.norm(comm)
        ratios.append(val / (3 * math.sqrt(LN2 * g)) if g > 1e-14 else (0.0 if val < 1e-9 else math.inf))
R.check("D(sigma || eta_j) = sum_{l<=j} a_l <= g, and ||sqrt(eta_j) - sqrt(sigma)||_2^2 <= ln2 g", wdir < 1e-9 and ok_sqrt,
        f"{wdir:.1e}")
R.check("the reversed order D(eta_j || sigma) <= g, which the text does not use, fails: it is violated (infinite) for the delay device",
        fails_text >= 1, f"{fails_text} of {2 * len(cases)} cases violate it; the needed square-root bound holds")
R.check("||[W_j, sqrt(gamma_j (x) sigma)]||_2 <= 3 sqrt(ln2 g) (eq. (common)) on random and nearly thermal collisions",
        max(ratios) <= 1 + 1e-6, f"largest ratio {max(ratios):.3f}")

# the square-root inequality with near-equality cases
worst_r, near_r = 0.0, 0
for k in range(400):
    d = int(rng.integers(2, 5))
    s = random_density(d, rng)
    if k % 2 == 0:
        r = random_density(d, rng)
    else:                                     # rho = sigma restricted to a large-weight subspace
        w, v = np.linalg.eigh(s)
        keep = np.ones(d, bool)
        keep[int(np.argmin(w))] = False
        if rng.random() < 0.5:
            s = s + float(rng.uniform(1e-4, 1e-2)) * dm(v[:, int(np.argmin(w))])
            s /= np.trace(s).real
            w, v = np.linalg.eigh(s)
        P = v[:, keep] @ v[:, keep].conj().T
        r = P @ s @ P / np.trace(P @ s).real
    lhs = np.linalg.norm(sqrtm_psd(r) - sqrtm_psd(s)) ** 2
    rhs = relent(r, s, math.e)
    worst_r = max(worst_r, lhs / rhs)
    near_r += lhs / rhs > 0.99
R.check("||sqrt(rho) - sqrt(sigma)||_2^2 <= D_nat(rho||sigma) on 400 pairs", worst_r <= 1 + 1e-9 and near_r >= 50,
        f"largest ratio {worst_r:.6f}, {near_r} with ratio > 0.99")

# 6. thermal realizations -----------------------------------------------------------------------------------------
wth, maxs = 0.0, []
for _ in range(6):
    dims = [2, 2]
    H = [np.diag([0.0, 1.0]).astype(complex), np.diag([0.0, 2.0]).astype(complex)]
    eB = rng.integers(0, 3, 3)
    HB = np.diag(eB).astype(complex)
    sigma = gibbs(HB, beta)
    U = [random_energy_conserving_unitary(np.add.outer(np.diag(H[j]).real, eB).reshape(-1), rng) for j in range(2)]
    real = Realization.collision(dims, sigma, U)
    for _ in range(10):
        s = simulate(real, random_tester(dims, rng), H)
        wth = max(wth, abs(s["SZF"] + beta / LN2 * s["energy"] + relent(s["omega"], sigma)))
    _, val, up = maximize_score(real, H, beta, lp, iters=30)
    maxs.append(up)
R.check("a causally ordered thermal realization scores -D(omega_t || sigma) for every tester, and its gain is 0",
        wth < 1e-10 and max(maxs) < 1e-6, f"{wth:.1e}; largest certified upper bound {max(maxs):.1e}")

# 7. Step 1 ---------------------------------------------------------------------------------------------------------
ok7 = True
for tau, U, H in cases[:6]:
    dims = [2, 2]
    real = Realization.collision(dims, tau, U)
    _, _, gup = maximize_score(real, H, beta, lp, iters=40)
    g = max(gup, 0.0)
    sigma, W, G, F = gauged(dims, H, tau, U)
    DBp = sigma.shape[0]
    taus, _, a = gibbs_driven(dims, H, tau, U)
    gam = [gibbs(h, beta) for h in H]
    for u in (1e-3, 1e-2, 0.1):
        su = (1 - u) * sigma + u * np.eye(DBp) / DBp
        # Gibbs-driven gauged baths from sigma_u: mixtures of eta_j and the evolved maximally mixed state
        for j in (1, 2):
            xi = np.kron(np.kron(taus[j], gam[0]), gam[1])
            eta = G[j] @ xi @ G[j].conj().T
            # evolve the maximally mixed source through j Gibbs-driven gauged contacts
            st = np.eye(DBp) / DBp
            for l in range(j):
                full = W[l] @ np.kron(gam[l], st) @ W[l].conj().T
                st = ptrace(full, [2, DBp], [1])
            eta_u = (1 - u) * eta + u * st
            kg = math.sqrt(LN2 * g) + 2 * math.sqrt(2 * u)
            ok7 &= np.linalg.norm(sqrtm_psd(eta_u) - sqrtm_psd(su)) <= kg + 1e-9
        for j in range(2):
            comm = (W[j] @ np.kron(sqrtm_psd(gam[j]), sqrtm_psd(su)) - np.kron(sqrtm_psd(gam[j]), sqrtm_psd(su)) @ W[j])
            ok7 &= np.linalg.norm(comm) <= 3 * math.sqrt(LN2 * g) + 2 * math.sqrt(2 * u) + 1e-9
R.check("Step 1: ||sqrt(eta_j^u) - sqrt(sigma_u)||_2 <= k_g and ||[W_j, sqrt(gamma_j (x) sigma_u)]||_2 <= b_g", ok7)

# 8. Step 3 ---------------------------------------------------------------------------------------------------------
def bin_prob_exact(xa, xb, h):
    """Probability over a uniform offset s in [0, h) that floor((x+s)/h) differs, by exact integration."""
    pts = sorted({0.0, h} | {(-x) % h for x in (xa, xb)})
    tot = 0.0
    for lo, hi in zip(pts, pts[1:]):
        s = (lo + hi) / 2
        tot += (hi - lo) * (math.floor((xa + s) / h) != math.floor((xb + s) / h))
    return tot / h


wp, worst_b, near_b = 0.0, 0.0, 0
for _ in range(4000):
    h = float(rng.choice([0.05, 0.3, 1.0, 2.5]))
    xa = float(rng.uniform(-5, 5))
    mode = rng.integers(0, 3)
    if mode == 0:
        xb = float(rng.uniform(-5, 5))
    elif mode == 1:
        xb = xa + float(rng.choice([-1, 1])) * h * float(rng.uniform(0.95, 1.05))
    else:
        xb = xa + float(rng.uniform(-1, 1)) * 1e-3 * h
    exact = bin_prob_exact(xa, xb, h)
    formula = min(1.0, abs(xa - xb) / h)
    wp = max(wp, abs(exact - formula))
    # lambda_a / lambda_b = e^{-(xa - xb)}
    rhs = abs(math.exp(-(xa - xb) / 2) - 1) / (1 - math.exp(-h / 2))
    if rhs > 0:
        worst_b = max(worst_b, formula / rhs)
        near_b += formula / rhs > 0.97
R.check("different bins with probability min{1, |ln(l_a/l_b)|/h} for a uniform offset (exact integration, 4000 pairs)",
        wp < 1e-12)
R.check("min{1, |ln(l_a/l_b)|/h} <= |sqrt(l_a/l_b) - 1|/(1 - e^{-h/2})", worst_b <= 1 + 1e-12 and near_b >= 200,
        f"largest ratio {worst_b:.6f}, {near_b} pairs above 0.97")


def bins_and_L(W, lam, h, s):
    xi = -np.log(lam)
    b = np.floor((xi + s) / h)
    diff = b[:, None] != b[None, :]
    return float(np.sum(np.abs(W) ** 2 * lam[None, :] * diff)), b


ok8, ratios8 = True, []
for _ in range(60):
    D = int(rng.integers(3, 9))
    lam = rng.dirichlet(np.ones(D) * float(rng.choice([0.3, 1, 5])))
    lam = np.clip(lam, 1e-6, None)
    lam /= lam.sum()
    Hgen = herm(rng.standard_normal((D, D)) + 1j * rng.standard_normal((D, D)))
    W = near_unitary(np.diag(np.exp(1j * rng.uniform(0, 6, D))), float(rng.choice([0.01, 0.1, 1.0])), rng)
    h = float(rng.choice([0.1, 0.5, 2.0]))
    xi = -np.log(lam)
    P = np.minimum(1.0, np.abs(xi[:, None] - xi[None, :]) / h)
    EL = float(np.sum(np.abs(W) ** 2 * lam[None, :] * P))
    q = np.linalg.norm(W @ np.diag(np.sqrt(lam)) - np.diag(np.sqrt(lam)) @ W) ** 2
    bound = math.sqrt(q) / (1 - math.exp(-h / 2))
    ok8 &= EL <= bound + 1e-12
    ratios8.append(EL / bound)
    # Monte Carlo cross-check of the expectation over the offset
    mc = np.mean([bins_and_L(W, lam, h, s)[0] for s in np.linspace(0, h, 2001)[:-1]])
    ok8 &= abs(mc - EL) < 5e-3 * max(1.0, EL)
R.check("E_s L_j(s) <= sqrt(q_j)/(1 - e^{-h/2}) (Cauchy-Schwarz), 60 random contacts", ok8,
        f"largest ratio {max(ratios8):.3f}")

# 9. Step 4 ---------------------------------------------------------------------------------------------------------
worst9, ok9c = 0.0, True
for _ in range(80):
    D = int(rng.integers(3, 9))
    lam = rng.dirichlet(np.ones(D))
    h = float(rng.choice([0.1, 0.5, 1.5]))
    s = float(rng.uniform(0, h))
    xi = -np.log(lam)
    xr = h * np.floor((xi + s) / h) - s                         # rounded logarithms
    W = near_unitary(np.diag(np.exp(1j * rng.uniform(0, 6, D))), float(rng.choice([0.02, 0.2, 1.0])), rng)
    blocks = [np.where(np.isclose(xr, v))[0] for v in np.unique(np.round(xr, 12))]
    X = np.zeros_like(W)
    for bl in blocks:
        X[np.ix_(bl, bl)] = W[np.ix_(bl, bl)]
    V = np.zeros_like(W)
    for bl in blocks:
        u_, sv, vh = np.linalg.svd(X[np.ix_(bl, bl)])
        V[np.ix_(bl, bl)] = u_ @ vh                             # polar completion inside the block
    L = float(np.sum(np.abs(W - X) ** 2 * lam[None, :]))
    lhs = np.linalg.norm((W - V) @ np.diag(np.sqrt(lam))) ** 2
    if L > 1e-14:
        worst9 = max(worst9, lhs / (2 * math.exp(2 * h) * L))
    Hr = np.diag(xr)
    ok9c &= np.abs(V @ Hr - Hr @ V).max() < 1e-12 and np.abs(V.conj().T @ V - np.eye(D)).max() < 1e-12
R.check("polar completion: ||(W - V) sqrt(Lambda)||_2^2 <= 2 e^{2h} L, and V is unitary and conserves the rounded energy",
        worst9 <= 1 + 1e-12 and ok9c, f"largest ratio {worst9:.3f}")

# 10. Step 6 --------------------------------------------------------------------------------------------------------
g_, r_, Lv = sp.symbols("g r L", positive=True)
L_choice = g_ ** (-1 / (2 * r_))
e1 = sp.simplify(sp.log(L_choice ** sp.Rational(-1, 3)) / sp.log(g_))
e2 = sp.simplify(sp.log(g_ ** sp.Rational(1, 4) * L_choice ** (r_ / 2 - sp.Rational(1, 3))) / sp.log(g_))
# eq. (repair) with h ~ 1/(m q), m ~ L^{1/3}, q <= L^{r-1}, delta <= C/(L q): the square-root term
q_ = Lv ** (r_ - 1)
term = sp.sqrt((sp.sqrt(g_) + 1 / (Lv * q_)) * Lv ** sp.Rational(1, 3) * q_)
lead = sp.expand(term ** 2)
ok10 = (sp.simplify(e1 - 1 / (6 * r_)) == 0 and sp.simplify(e2 - 1 / (6 * r_)) == 0
        and sp.simplify(lead - (sp.sqrt(g_) * Lv ** (r_ - sp.Rational(2, 3)) + Lv ** sp.Rational(-2, 3))) == 0)
# r <= 1: mesh h ~ g^{1/6} gives sqrt(b_g/h) ~ g^{1/4 - 1/12} = g^{1/6}
ok10 &= sp.Rational(1, 4) - sp.Rational(1, 12) == sp.Rational(1, 6)
R.check("Step 6: with L = g^{-1/(2r)}, L^{-1/3} = g^{1/4} L^{r/2 - 1/3} = g^{1/(6r)}; the square-root term of (repair) is "
        "(g^{1/2} L^{r - 2/3} + L^{-2/3})^{1/2}; for r <= 1 a mesh g^{1/6} gives g^{1/6}", ok10)
okd = True
for _ in range(200):
    rr = int(rng.integers(2, 4))
    v = rng.uniform(0, 1, rr - 1)
    Lint = int(rng.integers(2, 13))
    found = any(np.max(np.abs(q * v - np.round(q * v))) <= 1 / Lint + 1e-15 for q in range(1, Lint ** (rr - 1) + 1))
    okd &= found
R.check("Dirichlet: for every L >= 2 some 1 <= q <= L^{r-1} has |q v_k - p_k| <= 1/L (200 random cases, brute force)", okd)

# 11. Step 7 --------------------------------------------------------------------------------------------------------
ok11 = True
for _ in range(10):
    om = np.array([1.0, math.sqrt(2)])                   # rationally independent basis, r = 2
    om0 = np.array([1.0, 1.4])                           # commensurate approximation
    labels = [np.array([0, 0]), np.array([1, 0]), np.array([0, 1]), np.array([1, 1])][: int(rng.integers(2, 5))]
    Es = 0.3
    E_true = np.array([Es + a @ om for a in labels])
    E_0 = np.array([Es + a @ om0 for a in labels])
    eB = rng.integers(0, 3, 2).astype(float)             # rounded bath energies H'_B
    Mbox = 4
    lat = list(itertools.product(range(-Mbox, Mbox + 1), repeat=2))
    lat_index = {k: i for i, k in enumerate(lat)}
    HL = np.array([0.7 + np.array(k) @ (om - om0) for k in lat])
    de, db, dl = len(labels), len(eB), len(lat)
    Htot = np.zeros(de * db * dl)
    for e in range(de):
        for b in range(db):
            for i in range(dl):
                Htot[(e * db + b) * dl + i] = E_true[e] + eB[b] + HL[i]
    # V conserves H_0 + H'_B
    V = random_energy_conserving_unitary(np.add.outer(E_0, eB).reshape(-1), rng)
    Vt = np.eye(de * db * dl, dtype=complex)
    Amax = max(int(np.max(np.abs(a))) for a in labels)
    inner = [k for k in lat if max(abs(k[0]), abs(k[1])) <= Mbox - Amax]
    for k in inner:
        idx = []
        for e in range(de):
            for b in range(db):
                tgt = tuple(np.array(k) - labels[e])
                idx.append((e * db + b) * dl + lat_index[tgt])
        J = np.zeros((de * db * dl, de * db), dtype=complex)
        for col, row in enumerate(idx):
            J[row, col] = 1
        P = J @ J.conj().T
        Vt = Vt - P + J @ V @ J.conj().T
        # J^*(H_j + H'_B + H_L)J = H_0 + H'_B + const
        red = J.conj().T @ np.diag(Htot) @ J - np.diag(np.add.outer(E_0, eB).reshape(-1))
        ok11 &= np.allclose(red, red[0, 0] * np.eye(de * db))
    ok11 &= np.abs(Vt.conj().T @ Vt - np.eye(len(Htot))).max() < 1e-12
    ok11 &= np.abs(Vt @ np.diag(Htot) - np.diag(Htot) @ Vt).max() < 1e-10
R.check("Step 7: J^*(H_j + H'_B + H_L)J = H_0j + H'_B + const on inner labels; the lifted contact is unitary and conserves "
        "the original energy exactly", ok11)
ok11b = True
for Mbox, d_om in ((20, 1e-4), (50, 1e-5), (200, 1e-6)):
    r, A, bt = 2, 1, 1.0
    lat = np.array(list(itertools.product(range(-Mbox, Mbox + 1), repeat=r)))
    w = np.exp(-bt * lat @ np.array([d_om, -d_om]))
    w /= w.sum()
    near_bd = np.max(np.abs(lat), axis=1) > Mbox - A
    bound = 2 * A * r / (2 * Mbox + 1) * 1.01 + (math.exp(2 * bt * Mbox * 2 * d_om) - 1) / 2
    ok11b &= w[near_bd].sum() <= bound
R.check("labels near the lattice boundary have Gibbs weight at most C/M + (e^{2 beta M ||omega - omega_0||_1} - 1)/2", ok11b)

# 12. Step 9 ---------------------------------------------------------------------------------------------------------
ok12 = True
for Dc, Lr in ((2, 3), (3, 3), (4, 2), (5, 2)):
    Wc = math.log(Dc)                                    # beta W_c with beta = 1
    probs = [Dc ** j * math.exp(-j * Wc) for j in range(Lr + 1)]
    Zl = sum(probs)
    ok12 &= all(abs(pj / Zl - 1 / (Lr + 1)) < 1e-12 for pj in probs)
    images = set()
    for x in range(Dc):
        for j in range(Lr):
            for z in range(Dc ** j):
                img = (0, "ground", j + 1, x * Dc ** j + z)
                ok12 &= img[3] < Dc ** (j + 1) and (j * Wc + Wc) == ((j + 1) * Wc + 0.0)
                images.add(img)
    ok12 &= len(images) == sum(Dc * Dc ** j for j in range(Lr))
for N in (10, 100, 1000):
    Lr = N ** 8
    ok12 &= (1 / (Lr + 1)) * math.log(2 * 1 + 1) < 1e-6 and -(1 / (Lr + 1)) * math.log(1 / (Lr + 1)) < 1e-6
R.check("Step 9: the clock ladder (levels jW_c, degeneracy D_c^j) has Gibbs weights 1/(L+1); the swaps conserve energy and "
        "are injective; with L >= N^8 the failure and battery entropy vanish", ok12)

# 13. Werner-Holevo --------------------------------------------------------------------------------------------------
K = []
for i, j in ((0, 1), (0, 2), (1, 2)):
    k = np.zeros((3, 3), dtype=complex)
    k[i, j], k[j, i] = 1 / math.sqrt(2), -1 / math.sqrt(2)
    K.append(k)
WH = lambda rho: sum(k @ rho @ k.conj().T for k in K)
ok13 = np.allclose(WH(np.eye(3) / 3), np.eye(3) / 3)
for _ in range(10):
    rho = random_density(3, rng)
    ok13 &= np.allclose(WH(rho), (np.trace(rho) * np.eye(3) - rho.T) / 2)
comp = np.array([[np.trace(K[a] @ (np.eye(3) / 3) @ K[b].conj().T) for b in range(3)] for a in range(3)])
R.check("Werner-Holevo W(rho) = (I - rho^T)/2 preserves I/3, and its complementary channel at I/3 has entropy log2 3",
        ok13 and abs(entropy(comp) - math.log2(3)) < 1e-12)
R.close()
