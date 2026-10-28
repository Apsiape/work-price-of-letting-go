"""A strong converse with a reusable controller (Proposition "Strong converse with a reusable controller", its proof in
Appendix "A strong converse with a reusable controller", and the flat bank of Section "The clock's energy is a
lottery").

Checks:
  1. the log-likelihood law of (X, Gamma): its characteristic function is Xi(X; Gamma, t) = Tr X^{1+it} Gamma^{-it},
     its mean is D(X||Gamma), and Xi factorizes over tensor products and is invariant under unitaries that commute
     with Gamma;
  2. the spread s_n: s_n <= D(alpha||gamma) + 2/e, s_n = 0 for an energy eigenstate, s_n = beta x (mean absolute
     deviation of the energy from a median) for a pure controller, |Xi(alpha; gamma, t)| >= 1 - |t| s_n, and weight
     3/4 on one value gives |Xi| >= 1/2;
  3. acceptance: Tr AX <= e^x Tr A Gamma + Pr(L >= x) for projections A commuting with Gamma;
  4. continuity: |Xi(A) - Xi(B)| <= 2 sqrt(1+t^2) ||A-B||_1^{1/2}, with its two steps, and, for A and B that commute
     with Gamma, |Xi(A) - Xi(B)| <= sqrt(1+t^2) ||A - B||_1;
  5. the Taylor step |Xi(rho; gamma, t)^n - e^{itnD}| <= n v t^2/2;
  6. the reuse lemma: m runs of a controller that returns within eta stay within m eta of independent copies;
  7. the tail lemma 1 - sinc y >= min{y^2, 1}/8 and the bound Pr(|L - c| >= g/2) <= 8 max{1, 16B^2/g^2}
     E[1 - sinc(h(L - c))], on random laws;
  8. the constants: b = 3 beta Delta/4 in (a), 51 and 16nv/(3g^2) in (b), 2^17, 1/12, 12/11 and 2 tau/m in (c), and 36
     in the commuting case;
  9. a maximizer that commutes with H exists for covariant channels (pinching never lowers the objective);
 10. the flat bank, in exact rationals: branch weights, a fair branch independent of the bank, return distance
     6/((L+1)(L+2)), equal means and entropies, the variance A^2 given up, error exactly 1/2, and the spread.
"""
from fractions import Fraction
import math

import numpy as np
from scipy.linalg import expm

from qtools import (Report, choi_of, dag, diamond_half, dm, herm, logm_h, opnorm, powm_h, random_density,
                    random_unitary, relent, trace_norm)

R = Report("Strong converse with a reusable controller")
rng = np.random.default_rng(20261013)


def law(Xm, G):
    """Atoms (values, weights) of the log-likelihood law of (X, Gamma)."""
    x, a = np.linalg.eigh(herm(Xm))
    g, b = np.linalg.eigh(herm(G))
    ov = np.abs(dag(a) @ b) ** 2
    vals, wts = [], []
    for i in range(len(x)):
        if x[i] <= 1e-14:
            continue
        for j in range(len(g)):
            if ov[i, j] > 1e-15:
                vals.append(math.log(x[i] / g[j]))
                wts.append(x[i] * ov[i, j])
    return np.array(vals), np.array(wts)


def Xi(Xm, G, t):
    x, a = np.linalg.eigh(herm(Xm))
    xp = np.array([xx ** (1 + 1j * t) if xx > 1e-14 else 0 for xx in x])
    g, b = np.linalg.eigh(herm(G))
    return complex(np.trace((a * xp) @ dag(a) @ (b * g ** (-1j * t)) @ dag(b)))


def spread(vals, wts):
    order = np.argsort(vals)
    v, w = vals[order], wts[order]
    c = v[np.searchsorted(np.cumsum(w), 0.5 * w.sum())]
    return float(np.sum(w * np.abs(v - c))), c


def rand_gibbs(d, rng, beta=None):
    e = rng.uniform(0, 3, d)
    beta = rng.uniform(0.2, 3) if beta is None else beta
    u = random_unitary(d, rng)
    g = np.exp(-beta * e)
    return (u * (g / g.sum())) @ dag(u), u, e, beta


# 1. the law and its characteristic function
ok1 = True
for trial in range(300):
    d = int(rng.integers(2, 5))
    Xm = random_density(d, rng, rank=int(rng.integers(1, d + 1)))
    G, *_ = rand_gibbs(d, rng)
    vals, wts = law(Xm, G)
    ok1 &= abs(wts.sum() - 1) < 1e-12 and abs(wts @ vals - relent((1 - 1e-15) * Xm + 1e-15 * np.eye(d) / d, G)) < 1e-6
    for t in rng.uniform(-5, 5, 3):
        ok1 &= abs(Xi(Xm, G, t) - np.sum(wts * np.exp(1j * t * vals))) < 1e-10
    # tensor products and conserving unitaries
    d2 = 2
    X2 = random_density(d2, rng)
    G2, *_ = rand_gibbs(d2, rng)
    t = rng.uniform(-3, 3)
    ok1 &= abs(Xi(np.kron(Xm, X2), np.kron(G, G2), t) - Xi(Xm, G, t) * Xi(X2, G2, t)) < 1e-10
    w, v = np.linalg.eigh(G)
    Uc = v @ np.diag(np.exp(1j * rng.uniform(0, 6, d))) @ dag(v)
    ok1 &= abs(Xi(Uc @ Xm @ dag(Uc), G, t) - Xi(Xm, G, t)) < 1e-10
    ok1 &= abs(Xi(G / np.trace(G), G / np.trace(G), t) - 1) < 1e-10
R.check("Xi(X; Gamma, t) = Tr X^{1+it} Gamma^{-it} is the characteristic function of the law, with mean D(X||Gamma); "
        "it factorizes, is invariant under unitaries commuting with Gamma, and Xi(gamma; gamma, t) = 1", ok1)

# 2. the spread
ok2, near2 = True, 0
for trial in range(400):
    d = int(rng.integers(2, 6))
    G, u, e, beta = rand_gibbs(d, rng)
    if trial % 4 == 0:
        alpha = dm(u[:, int(rng.integers(d))])          # energy eigenstate
        vals, wts = law(alpha, G)
        ok2 &= spread(vals, wts)[0] < 1e-10
        continue
    if trial % 4 == 1:
        psi = rng.standard_normal(d) + 1j * rng.standard_normal(d)
        psi /= np.linalg.norm(psi)
        alpha = dm(psi)
        vals, wts = law(alpha, G)
        s, _ = spread(vals, wts)
        pE = np.abs(dag(u) @ psi) ** 2                  # energy law of the pure controller
        order = np.argsort(e)
        med = e[order][np.searchsorted(np.cumsum(pE[order]), 0.5)]
        ok2 &= abs(s - beta * float(pE @ np.abs(e - med))) < 1e-9
    else:
        alpha = random_density(d, rng, rank=int(rng.integers(1, d + 1)))
        vals, wts = law(alpha, G)
        s, _ = spread(vals, wts)
    Dag = float(wts @ vals)
    neg = float(np.sum(wts * np.maximum(-vals, 0)))
    ok2 &= s <= Dag + 2 / math.e + 1e-10 and neg <= 1 / math.e + 1e-12
    near2 += neg > 0.1
    B = max(1.0, s)
    for t in rng.uniform(-1, 1, 5) / max(s, 1e-9):
        ok2 &= abs(Xi(alpha, G, t)) >= 1 - abs(t) * s - 1e-10
        if abs(t) <= 1 / (2 * B):
            ok2 &= abs(Xi(alpha, G, t)) >= 0.5 - 1e-12
for trial in range(300):
    k = int(rng.integers(2, 8))
    vals = rng.uniform(-20, 20, k)
    w = rng.dirichlet(np.ones(k))
    w = 0.75 * np.eye(k)[0] + 0.25 * w
    t = rng.uniform(-50, 50)
    ok2 &= abs(np.sum(w * np.exp(1j * t * vals))) >= 0.5 - 1e-12
R.check("s_n <= D(alpha||gamma) + 2/e with E(L)_- <= 1/e; s_n = 0 for an energy eigenstate; s_n = beta x mean "
        "absolute deviation of the energy from a median for a pure controller; |Xi| >= 1 - |t| s_n, >= 1/2 for "
        "|t| <= 1/(2B), and >= 1/2 when one value has weight 3/4", ok2 and near2 >= 20, f"{near2} cases with E(L)_- > 0.1")

# 3. acceptance
ok3, near3 = True, 0
for trial in range(3000):
    d = int(rng.integers(2, 6))
    G, u, e, beta = rand_gibbs(d, rng)
    G = G * rng.uniform(0.2, 5)                          # Gamma need not be normalized
    Xm = random_density(d, rng) if trial % 2 else (u @ np.diag(rng.dirichlet(np.ones(d))) @ dag(u))
    sel = rng.random(d) < 0.5
    A = u[:, sel] @ dag(u[:, sel])
    vals, wts = law(Xm, G)
    for x in np.concatenate([vals, rng.uniform(-4, 4, 3)]):
        lhs = np.real(np.trace(A @ Xm))
        rhs = math.exp(x) * np.real(np.trace(A @ G)) + float(np.sum(wts[vals >= x - 1e-12]))
        ok3 &= lhs <= rhs + 1e-10
        near3 += lhs > 0.1 and lhs >= 0.98 * rhs
R.check("acceptance: Tr AX <= e^x Tr A Gamma + Pr(L >= x) for projections A commuting with Gamma",
        ok3 and near3 >= 100, f"{near3} cases within 2%")

# 4. continuity
ok4, worst4, worst_c, near4 = True, 0.0, 0.0, 0
for trial in range(1500):
    d = int(rng.integers(2, 5))
    G, u, e, beta = rand_gibbs(d, rng)
    A = random_density(d, rng, rank=int(rng.integers(1, d + 1)))
    lam = 10 ** rng.uniform(-6, 0)
    B = (1 - lam) * A + lam * random_density(d, rng)
    t = rng.uniform(-6, 6)
    n1 = trace_norm(A - B)
    lhs = abs(Xi(A, G, t) - Xi(B, G, t))
    worst4 = max(worst4, lhs / (2 * math.sqrt(1 + t * t) * math.sqrt(n1)))
    sa, sb = powm_h(A, 0.5), powm_h(B, 0.5)
    ps = np.linalg.norm(sa - sb) ** 2
    ok4 &= ps <= n1 + 1e-12
    za = lambda m: (lambda w, v: (v * np.array([ww ** (1 + 1j * t) if ww > 1e-15 else 0 for ww in w])) @ dag(v))(*np.linalg.eigh(herm(m)))
    ok4 &= np.linalg.norm(za(sa) - za(sb)) ** 2 <= (1 + t * t) * ps + 1e-12
    # commuting case: A, B block diagonal in the eigenbasis of Gamma (energy shells, here non-degenerate)
    Ac = u @ np.diag(rng.dirichlet(np.ones(d))) @ dag(u)
    Bc = u @ np.diag(rng.dirichlet(np.ones(d))) @ dag(u) if trial % 2 else (1 - lam) * Ac + lam * u @ np.diag(rng.dirichlet(np.ones(d))) @ dag(u)
    rc = abs(Xi(Ac, G, t) - Xi(Bc, G, t)) / (math.sqrt(1 + t * t) * trace_norm(Ac - Bc))
    worst_c = max(worst_c, rc)
    near4 += rc > 0.8
R.check("continuity: ||A^z - B^z||_2^2 <= (1+t^2)||sqrt A - sqrt B||_2^2 <= (1+t^2)||A - B||_1 and "
        "|Xi(A) - Xi(B)| <= 2 sqrt(1+t^2) ||A - B||_1^{1/2}", ok4 and worst4 <= 1, f"largest ratio {worst4:.3f}")
R.check("commuting case: |Xi(A) - Xi(B)| <= sqrt(1+t^2) ||A - B||_1 when A, B commute with Gamma",
        worst_c <= 1 + 1e-9 and near4 >= 20, f"largest ratio {worst_c:.3f}, {near4} cases above 0.8")

# 5. Taylor step
ok5, near5 = True, 0
for trial in range(600):
    d = int(rng.integers(2, 4))
    G, *_ = rand_gibbs(d, rng)
    rho = random_density(d, rng)
    vals, wts = law(rho, G)
    mu = wts @ vals
    v = wts @ (vals - mu) ** 2
    n = int(rng.integers(1, 200))
    t = rng.uniform(-1, 1) / math.sqrt(n * v + 1e-12)
    lhs = abs(Xi(rho, G, t) ** n - np.exp(1j * t * n * mu))
    ok5 &= lhs <= n * v * t * t / 2 + 1e-12
    near5 += lhs > 0.5 * n * v * t * t / 2
R.check("|Xi(rho; gamma, t)^n - e^{itnD}| <= n v t^2/2", ok5 and near5 >= 100, f"{near5} cases above half the bound")

# 6. the reuse lemma
worst6, cnt6 = 0.0, 0
for trial in range(60):
    dC, dF = 2, 2
    alpha = random_density(dC, rng)
    fresh = random_density(dF, rng)
    Ugen = herm(rng.standard_normal((4, 4)) + 1j * rng.standard_normal((4, 4)))
    U = expm(1j * 10 ** rng.uniform(-2, 0) * Ugen)        # a run acting on the controller and one fresh block
    out1 = U @ np.kron(alpha, fresh) @ dag(U)
    om_rest = np.einsum("aiaj->ij", out1.reshape(dC, dF, dC, dF))
    eta = trace_norm(out1 - np.kron(alpha, om_rest)) / 2
    state = alpha.copy()
    for m in range(1, 5):
        dims_rest = dF ** (m - 1)
        full = np.kron(state, fresh)                         # (C, old blocks, new block)
        # apply U on C and the new block
        Ufull = np.einsum("aibj,kl->akiblj", U.reshape(dC, dF, dC, dF), np.eye(dims_rest)).reshape(dC * dims_rest * dF, -1)
        state = Ufull @ full @ dag(Ufull)
        comp = alpha
        for _ in range(m):
            comp = np.kron(comp, om_rest)
        dist = trace_norm(state - comp) / 2
        worst6 = max(worst6, dist / (m * eta))
        cnt6 += 1
R.check("reuse: after m runs the state is within m eta of alpha_C (x) Omega_R^{(x)m} (m <= 4, random runs)",
        worst6 <= 1 + 1e-9, f"largest ratio {worst6:.3f} over {cnt6} cases")

# 7. the tail lemma
ys = np.linspace(1e-6, 200, 2000001)
sinc = np.sin(ys) / ys
R.check("1 - sinc y >= min{y^2, 1}/8 on (0, 200] (grid of 2e6 points; proved in Lean on all of R)",
        bool(np.all(1 - sinc >= np.minimum(ys ** 2, 1) / 8 - 1e-15)))
ok7, near7 = True, 0
for trial in range(3000):
    k = int(rng.integers(2, 10))
    vals = rng.normal(0, rng.uniform(0.1, 30), k)
    w = rng.dirichlet(np.ones(k) * rng.uniform(0.1, 2))
    c = rng.normal(0, 5)
    B = rng.uniform(1, 20)
    g = rng.uniform(0.1, 60)
    h = min(1 / (2 * B), 2 / g)
    esinc = float(np.sum(w * (1 - np.sinc(h * (vals - c) / math.pi))))
    tail = float(np.sum(w[np.abs(vals - c) >= g / 2]))
    bound = 8 * max(1, 16 * B * B / (g * g)) * esinc
    ok7 &= tail <= bound + 1e-12
    near7 += tail > 0.05 and tail >= 0.25 * bound
    ts = np.linspace(-h, h, 2001)
    avg = np.trapezoid([1 - np.real(np.sum(w * np.exp(1j * tt * (vals - c)))) for tt in ts], ts) / (2 * h)
    ok7 &= abs(avg - esinc) < 1e-5
R.check("E[1 - sinc(h(L-c))] is the average of 1 - Re E e^{it(L-c)} over |t| <= h, and "
        "Pr(|L - c| >= g/2) <= 8 max{1, 16B^2/g^2} E[1 - sinc(h(L - c))] for h = min{1/(2B), 2/g}",
        ok7 and near7 >= 20, f"{near7} cases above a quarter of the bound")

# 8. constants
bD = __import__("sympy").symbols("bD", positive=True)
import sympy as sp
n_s = sp.symbols("n", positive=True)
kappa = bD / 8
expo = n_s * (-bD) + 2 * kappa * n_s                      # beta W - n(beta T - 2 kappa) <= n(-beta Delta + 2 kappa)
R.check("(a): with kappa = beta Delta/8, r = e^{beta W - n(beta T - 2 kappa)} <= e^{-bn} with b = 3 beta Delta/4",
        sp.simplify(expo + sp.Rational(3, 4) * bD * n_s) == 0)
R.check("(b): 8 x 4 sqrt2 x sqrt(5/4) = 50.60 <= 51, and the commuting case 8 x 4 x sqrt(5/4) = 35.78 <= 36",
        32 * math.sqrt(2) * math.sqrt(1.25) <= 51 and 32 * math.sqrt(1.25) <= 36,
        f"{32 * math.sqrt(2.5):.3f}, {32 * math.sqrt(1.25):.3f}")
ok8 = True
for B in (1.0, 1.5, 3.0, 10.0):
    for g in (0.5, 2.0, 4.0, 7.9, 8.1, 50.0):
        for nv in (0.01, 1.0, 30.0):
            h = min(1 / (2 * B), 2 / g)
            ok8 &= 8 * max(1, 16 * B * B / (g * g)) * nv * h * h / 6 <= 16 * nv / (3 * g * g) * (1 + 1e-12)
R.check("(b): 8 max{1, 16B^2/g^2} n v h^2/6 = 16 n v/(3 g^2) for h = min{1/(2B), 2/g}", ok8)
ok8b = True
for s in (0.0, 0.3, 1.0, 5.0, 100.0):
    for n in range(1, 200):
        for bdel in (0.05, 0.5, 2.0):
            Bv = max(1.0, s)
            g = n * bdel / 2
            if s >= 1 or n >= 8 / bdel:
                ok8b &= max(1, 16 * Bv * Bv / g ** 2) <= max(1, (8 * s / (bdel * n)) ** 2) * (1 + 1e-12)
            if n * bdel >= 4:
                ok8b &= max(1, (4 * Bv / (n * bdel)) ** 2) <= max(1, (8 * s / (n * bdel)) ** 2) * (1 + 1e-12)
R.check("max{1, 16B^2/g^2} <= max{1, (8 s/(beta Delta n))^2} when s >= 1 or n >= 8/(beta Delta) (g >= n beta Delta/2), "
        "and max{1, (4B/(n beta Delta))^2} <= max{1, (8 s/(n beta Delta))^2} when n beta Delta >= 4", ok8b)
ok8c, near8c = True, 0
etas = [Fraction(1, 2 ** 14) / k for k in range(1, 400)] + [Fraction(1, 2 ** 14) * Fraction(k, 400) for k in range(1, 400)]
for eta in etas:
    m = math.floor(1 / (8192 * eta))
    ok8c &= m >= 1 and 2 * m * eta <= Fraction(1, 4096)          # so sqrt(2 m eta) <= 1/64 and tau <= 1/12
    bound = Fraction(16, 3) / m
    ok8c &= bound <= 2 ** 17 * eta
    near8c += bound >= Fraction(2, 5) * 2 ** 17 * eta
R.check("(c): eta <= 2^-14, m = floor(1/(8192 eta)): 2 m eta <= 1/4096 (tau = (16/3) sqrt(2 m eta) <= 1/12) and "
        "16/(3m) <= 2^17 eta (exact rationals)", ok8c and near8c >= 10, f"{near8c} cases within a factor 2.5")
R.check("(c): |phi^m - psi^m| <= 4 sqrt(2 m eta) sqrt(5/4) and |psi^m| >= 15/16 give |r^m - 1| <= (16/3) sqrt(2 m eta)",
        4 * math.sqrt(1.25) * 16 / 15 <= 16 / 3, f"{4 * math.sqrt(1.25) * 16 / 15:.4f} <= 5.3333")
ok8d = True
for trial in range(20000):
    tau = rng.uniform(0, 1 / 12)
    m = int(rng.integers(1, 1000))
    w = 1 + tau * math.sqrt(rng.uniform()) * np.exp(1j * rng.uniform(0, 2 * math.pi))
    L = np.log(w) / m                                         # the continuous log of r, given Log(r^m) = Log w
    ok8d &= abs(np.log(w)) <= 12 * tau / 11 + 1e-15
    psi = np.exp(1j * rng.uniform(0, 6)) * rng.uniform(0, 1)
    ok8d &= abs(psi * np.exp(L) - psi) <= 2 * tau / m + 1e-15
R.check("(c): |w - 1| <= tau <= 1/12 gives |Log w| <= 12 tau/11, hence |phi - psi| = |psi||e^{Log r} - 1| <= 2 tau/m", ok8d)
ok8e = True
for B in (1.0, 2.0, 30.0):
    for a in (1.0, 3.0, 50.0):
        for m in (1, 10, 10 ** 4):
            for nv in (1e-3, 1.0, 1e3):
                tau = 1 / 12
                h = min(0.5, 1 / (2 * B), (8 * m * nv) ** -0.5, 1 / (2 * a))
                lhs = 8 * (nv * h * h / 6 + 2 * tau / m) / (h * a) ** 2
                ok8e &= h * a <= 0.5 + 1e-15 and lhs <= 12 * nv / a ** 2 + 16 / (3 * m) * max(1, B * B / a ** 2) + 1e-12
R.check("(c): with h = min{1/2, 1/(2B), (8mnv)^{-1/2}, 1/(2a)}, 8(n v h^2/6 + 2 tau/m)/(ha)^2 <= 12 n v/a^2 + "
        "(16/(3m)) max{1, B^2/a^2}; with a = n beta Delta/4, 12nv/a^2 = 192 v/(n beta^2 Delta^2)",
        ok8e and sp.simplify(12 / (n_s * bD / 4) ** 2 - 192 / (n_s ** 2 * bD ** 2)) == 0)

# commuting case: Omega commuting with H_C + H_R has Omega_R commuting with H_R
ok8f = True
for trial in range(100):
    dC, dR = 2, 3
    eC, eR = rng.integers(0, 3, dC).astype(float), rng.integers(0, 3, dR).astype(float)
    Htot = np.add.outer(eC, eR).reshape(-1)
    Om = random_density(dC * dR, rng)
    P = np.zeros_like(Om)
    for val in np.unique(Htot):
        idx = np.where(Htot == val)[0]
        P[np.ix_(idx, idx)] = Om[np.ix_(idx, idx)]                 # pinch in total energy
    P /= np.trace(P)
    OR = np.einsum("aiaj->ij", P.reshape(dC, dR, dC, dR))
    ok8f &= opnorm(OR @ np.diag(eR) - np.diag(eR) @ OR) < 1e-12
R.check("commuting case: [Omega, H_C + H_R] = 0 implies [Omega_R, H_R] = 0", ok8f)

# 9. covariant channels have a stationary maximizer: pinching never lowers the objective
ok9, cnt9 = True, 0
for trial in range(200):
    d = 3
    e = np.array([0.0, 1.0, 2.0])
    beta = rng.uniform(0.2, 3)
    gam = np.diag(np.exp(-beta * e))
    gam /= np.trace(gam)
    kr = [rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)) for _ in range(2)]
    s_ = sum(dag(k) @ k for k in kr)
    w, v = np.linalg.eigh(s_)
    kr = [k @ (v * w ** -0.5) @ dag(v) for k in kr]
    T = 9
    ts = 2 * math.pi * np.arange(T) / T

    def cov(r):
        out = 0
        for t in ts:
            Ut = np.diag(np.exp(-1j * e * t))
            out = out + dag(Ut) @ sum(k @ (Ut @ r @ dag(Ut)) @ dag(k) for k in kr) @ Ut / T
        return out

    obj = lambda r: relent(cov(r), gam) - relent(r, gam)
    for _ in range(3):
        rho = (1 - 1e-12) * random_density(d, rng) + 1e-12 * np.eye(d) / d
        ok9 &= obj(np.diag(np.diag(rho))) >= obj(rho) - 1e-9
        cnt9 += 1
R.check("covariant channels: the objective D(Phi rho||gamma) - D(rho||gamma) at rho is at most its value at the "
        "pinched rho", ok9, f"{cnt9} inputs on random covariant qutrit channels")

# ---------------------------------------------------------------------------------------------------------------------
# 10. the flat bank
ok10 = True
ratios = {}
for L in list(range(1, 80)) + [100, 1000, 10000]:
    k = Fraction(L * (L + 1) * (L + 2), 3)
    npj = [Fraction(L)] + [Fraction(2 * j * (L + 1 - j) - 2) for j in range(1, L + 1)] + [Fraction(L)]
    nq = [Fraction(0)] + [Fraction(2 * j * (L + 1 - j)) for j in range(1, L + 1)] + [Fraction(0)]
    ok10 &= sum(npj) == k and sum(nq) == k and all(x >= 0 for x in npj)
    p = [x / k for x in npj]
    q = [x / k for x in nq]
    # branch weights: Pr(bank at j and branch down) = d_j, up = u_j
    dj = [Fraction(0)] + [Fraction((j - 1) * (L + 2 - j)) / k for j in range(1, L + 1)] + [Fraction(L) / k]
    uj = [Fraction(L) / k] + [Fraction((j + 1) * (L - j)) / k for j in range(1, L + 1)] + [Fraction(0)]
    ok10 &= all(dj[j] + uj[j] == p[j] and dj[j] >= 0 and uj[j] >= 0 for j in range(L + 2))
    ok10 &= sum(dj) == Fraction(1, 2) and sum(uj) == Fraction(1, 2)
    # after the step: down moves j -> j-1, up moves j -> j+1; the bank law given each branch is the same, q
    after_down = [2 * (dj[l + 1] if l + 1 <= L + 1 else 0) for l in range(L + 2)]
    after_up = [2 * (uj[l - 1] if l >= 1 else 0) for l in range(L + 2)]
    ok10 &= after_down == q and after_up == q
    tv = sum(abs(a - b) for a, b in zip(p, q)) / 2
    ok10 &= tv == Fraction(6, (L + 1) * (L + 2))
    js = range(L + 2)
    mp_ = sum(j * x for j, x in zip(js, p))
    mq_ = sum(j * x for j, x in zip(js, q))
    vp = sum((j - mp_) ** 2 * x for j, x in zip(js, p))
    vq = sum((j - mq_) ** 2 * x for j, x in zip(js, q))
    ok10 &= mp_ == mq_ == Fraction(L + 1, 2) and vp - vq == 1
    mad = sum(abs(j - Fraction(L + 1, 2)) * x for j, x in zip(js, p))
    ratios[L] = float(mad) * math.log(2) / 2 * math.sqrt((L + 1) * (L + 2) / 6) ** -1 if False else \
        float(mad) * math.log(2) / 2 / math.sqrt((L + 1) * (L + 2) / 6)
R.check("flat bank (L = 1..79, 100, 1000, 10000, exact): ranks sum to k = L(L+1)(L+2)/3 before and after; a fair "
        "branch, the bank law after the step is the same on both branches; return distance 6/((L+1)(L+2)); equal means; "
        "the variance drops by exactly one level squared (A^2); flat on k states before and after (equal entropies)", ok10)
lim = 3 * math.sqrt(6) * math.log(2) / 32
R.check("spread: for even n, s_n/(n eta_n^{-1/2}) = (ln2/2) E_p|j - (L+1)/2| sqrt(6/((L+1)(L+2))) tends to "
        "(3 sqrt6/32) ln2 = 0.1592, and is within 1.5% of that limit for every L >= 10",
        abs(ratios[10000] - lim) < 1e-4 and all(abs(ratios[L] / lim - 1) <= 0.015 for L in ratios if L >= 10),
        f"L=1: {ratios[1]:.3f}, L=2: {ratios[2]:.3f}, L=5: {ratios[5]:.3f}, L=10: {ratios[10]:.4f}, "
        f"L=30: {ratios[30]:.4f}, L=10^4: {ratios[10000]:.5f}")
R.check("for small L the ratio is larger, so 0.159 is the large-L value (L = 1, 2, 3)",
        ratios[1] > ratios[2] > ratios[3] > lim, f"{ratios[1]:.3f}, {ratios[2]:.3f}, {ratios[3]:.3f}")
# error exactly 1/2: (Reset + id)/2 against Reset on one and two zero-Hamiltonian qubits
ok10b = True
for nq_ in (1, 2):
    d = 2 ** nq_
    reset = lambda r: np.trace(r) * dm(np.eye(d)[0])
    half = lambda r: 0.5 * reset(r) + 0.5 * r
    ok10b &= abs(diamond_half(choi_of(half, d), choi_of(reset, d), d, d) - 0.5) < 1e-6
R.check("the bank's channel (Reset + id)/2 is at half diamond distance exactly 1/2 from Reset (n = 1, 2; SDP)", ok10b)
eK = []
for n in (16, 64, 256):
    for Lfun, name in ((lambda n: n, "L = n"), (lambda n: n * n, "L = n^2")):
        L = Lfun(n)
        A_beta = math.ceil(n / 2) * math.log(2)               # beta A
        K = (L + 1) * A_beta + math.log(L * (L + 1) * (L + 2) / 3 + 2 * L) + n * math.log(2)
        eK.append((name, n, 6 / ((L + 1) * (L + 2)) * K))
small = [v for nm, n, v in eK if nm == "L = n^2"]
large = [v for nm, n, v in eK if nm == "L = n"]
R.check("eta_n K tends to zero when L/n -> infinity (here L = n^2): about 3 ln2 n/L",
        small[-1] < small[0] and small[-1] < 0.02, "L = n^2: " + ", ".join(f"{v:.4f}" for v in small))
R.check("the hypothesis L/n -> infinity is needed: with L = n, eta_n K stays near 2.08",
        all(1.9 < v < 2.3 for v in large), "L = n gives eta_n K = " + ", ".join(f"{v:.2f}" for v in large))
R.close()
