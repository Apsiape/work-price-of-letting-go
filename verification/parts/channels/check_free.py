"""What is free (Theorem "What is free in real time", Section 6, Appendix "What is free in real time").

Checks:
  1. S(rho) - S(Phi(rho)) + beta/ln2 Tr H(Phi(rho) - rho) = D(Phi(rho)||gamma) - D(rho||gamma) for every channel
     (the relative-entropy form of T_cap), so T_rt >= D(Phi(gamma)||gamma), and T_cap(Phi) <= 0 when Phi(gamma) = gamma;
  2. thermal operations (random baths with commensurate and incommensurate gaps, random energy-conserving unitaries):
     f_Dil(rho) + e_H(rho) = -D(Gamma(rho)||gamma_B) <= 0 for every input;
  3. the Gibbs defect identity G_Dil = D(Omega||gamma x omega) >= 0 for every dilation (bath states of any rank), with
     G_Dil = 0 for thermal operations;
  4. Nussbaum-Szkola distributions reproduce D(rho||sigma); Tr sqrt(rho) sqrt(sigma) >= e^{-D_nat/2} and
     ||sqrt rho - sqrt sigma||_2^2 <= D_nat(rho||sigma);
  5. the commutator bound ||[W, sqrt(gamma x sigma_D)]||_2 <= 2 sqrt(ln2 G_Dil) for W = U_AB^* U_SB (which implements the
     same channel), on random dilations including near-thermal ones; mixing with I/dim D changes the channel by at most
     t and the commutator by at most 2 sqrt(2t);
  6. |x^{iz} - 1| <= C_z |sqrt x - 1|, C_z = max{2 e^{1/2}|z|, 2/(1 - e^{-1/2})} (dense grid, with near-equality), and
     ||[W, eta^{iz}]||_{2,eta} <= C_z ||[W, sqrt eta]||_2 on random instances;
  7. twirling: time covariance is commutation with every D_theta, the discrete average over Q^r phases equals the full
     twirl when Q exceeds every |a_e - a_f - a_g + a_h|, and the flagged twirl of a dilation has exactly the same
     Gibbs defect;
  8. replacement: the randomly offset rounding gives e^{-h} sigma <= sigma' <= e^h sigma; two logarithms are separated
     with probability min(1, |ln(p_a/p_b)|/h) <= |sqrt(p_a/p_b) - 1|/(1 - e^{-h/2}) (equality at the edge);
     Dirichlet's theorem on random instances; the lattice isometries J_k reduce H + H_L to H_0 + const and the outer
     labels have Gibbs probability <= 4rA/(2N+1) + 2 beta N ||omega - omega_0||_1; the exponents give G^{1/(6r)},
     and G^{1/6} for r <= 1.
"""
import itertools
import math

import numpy as np
import sympy as sp

from qtools import (Report, conserving_unitary, dm, entropy, gibbs, herm, kraus_apply, mfun, msqrt, ptrace,
                    random_density, random_herm, random_unitary, relent, trace_norm)

R = Report("What is free")
rng = np.random.default_rng(20261019)
LN2 = math.log(2)

# ---------------------------------------------------------------------------------------------------- 1. T_cap form
worst = 0.0
for _ in range(300):
    d, dB = int(rng.integers(2, 4)), int(rng.integers(2, 4))
    U = random_unitary(d * dB, rng)
    tau = random_density(dB, rng)
    Phi = lambda r: ptrace(U @ np.kron(r, tau) @ U.conj().T, [d, dB], [0])
    beta = rng.uniform(0.2, 3)
    H = np.diag(np.sort(rng.uniform(0, 2, d)))
    g = gibbs(H, beta)
    rho = random_density(d, rng)
    lhs = entropy(rho) - entropy(Phi(rho)) + beta / LN2 * np.trace(H @ (Phi(rho) - rho)).real
    rhs = relent(Phi(rho), g) - relent(rho, g)
    worst = max(worst, abs(lhs - rhs))
R.check("S(rho) - S(Phi(rho)) + beta/ln2 Tr H(Phi(rho) - rho) = D(Phi(rho)||gamma) - D(rho||gamma) (so at gamma it is "
        "D(Phi(gamma)||gamma), and it is <= 0 when Phi(gamma) = gamma)", worst < 1e-10, f"max deviation {worst:.1e}")


# ---------------------------------------------------------------------------------------------------- 2. thermal ops
def thermal_operation(HS, HB, beta, rng):
    Htot = np.kron(np.diag(HS), np.eye(len(HB))) + np.kron(np.eye(len(HS)), np.diag(HB))
    U = conserving_unitary(Htot, rng)
    return U, gibbs(np.diag(HB), beta)


worst, ok = 0.0, True
for trial in range(300):
    beta = rng.uniform(0.2, 3)
    if trial % 2:
        HS = np.array([0.0, 1.0, 2.0])
        HB = rng.integers(0, 4, int(rng.integers(2, 6))).astype(float)
    else:
        e1, e2 = 1.0, math.sqrt(2)
        HS = np.array([0.0, e1, e2])
        HB = np.array([a * e1 + b * e2 for a, b in itertools.product(range(2), repeat=2)])[: int(rng.integers(2, 5))]
    U, gB = thermal_operation(HS, HB, beta, rng)
    d, dB = len(HS), len(HB)
    rho = random_density(d, rng)
    out = U @ np.kron(rho, gB) @ U.conj().T
    Gam = ptrace(out, [d, dB], [1])
    O = ptrace(out, [d, dB], [0])
    f = entropy(Gam) - entropy(gB)
    e = beta / LN2 * np.trace(np.diag(HS) @ (O - rho)).real
    worst = max(worst, abs(f + e + relent(Gam, gB)))
    ok &= f + e <= 1e-10
R.check("thermal operations: f_Dil(rho) + e_H(rho) = -D(Gamma(rho)||gamma_B) <= 0 for every input (300 random)",
        worst < 1e-9 and ok, f"max deviation {worst:.1e}")


# ---------------------------------------------------------------------------------------------------- 3. defect
def defect_pair(U, tau, H, beta, d, dB):
    g = gibbs(H, beta)
    Om = U @ np.kron(g, tau) @ U.conj().T
    om = ptrace(Om, [d, dB], [1])
    Psig = ptrace(Om, [d, dB], [0])
    G = entropy(om) - entropy(tau) + beta / LN2 * np.trace(H @ (Psig - g)).real
    return G, Om, om, g


worst, ok_pos, ok_th = 0.0, True, True
for trial in range(300):
    d, dB = int(rng.integers(2, 4)), int(rng.integers(2, 5))
    U = random_unitary(d * dB, rng)
    tau = random_density(dB, rng, rank=int(rng.integers(1, dB + 1)))
    H = np.diag(np.sort(rng.uniform(0, 2, d)))
    beta = rng.uniform(0.2, 3)
    G, Om, om, g = defect_pair(U, tau, H, beta, d, dB)
    # D(Omega || g x omega) with supports: omega may be singular; Omega is supported in supp(g x omega)
    w, v = np.linalg.eigh(herm(om))
    keep = w > 1e-13
    P = np.kron(np.eye(d), v[:, keep] @ v[:, keep].conj().T)
    Dval = relent(Om, np.kron(g, om) + 1e-300 * np.eye(d * dB)) if keep.all() else \
        -entropy(Om) - float(np.trace(Om @ (np.kron(mfun(g, np.log2), np.eye(dB)) +
                                            np.kron(np.eye(d), (v[:, keep] * np.log2(w[keep])) @ v[:, keep].conj().T))).real)
    worst = max(worst, abs(G - Dval))
    ok_pos &= G >= -1e-10
for trial in range(100):
    HS = np.array([0.0, 1.0, 2.0])
    HB = rng.integers(0, 4, int(rng.integers(2, 5))).astype(float)
    beta = rng.uniform(0.2, 3)
    U, gB = thermal_operation(HS, HB, beta, rng)
    G, *_ = defect_pair(U, gB, np.diag(HS), beta, 3, len(HB))
    ok_th &= abs(G) < 1e-10
R.check("G_Dil = D(Omega||gamma x omega) >= 0 for every dilation, bath states of any rank (300 random)",
        worst < 1e-9 and ok_pos, f"max deviation {worst:.1e}")
R.check("G_Dil = 0 for thermal operations (100 random)", bool(ok_th))

# ---------------------------------------------------------------------------------------------------- 4. sqrt distance
ok_ns, ok_bc, ok_sq = True, True, True
best = 0.0
for _ in range(2000):
    d = int(rng.integers(2, 5))
    r = random_density(d, rng)
    s = random_density(d, rng)
    if rng.random() < 0.5:
        u = 10 ** rng.uniform(-4, 0)
        s = (1 - u) * r + u * s
    wr, vr = np.linalg.eigh(r)
    ws, vs = np.linalg.eigh(s)
    ov = np.abs(vr.conj().T @ vs) ** 2
    p = wr[:, None] * ov
    q = ws[None, :] * ov
    mask = p > 0
    Dpq = float(np.sum(p[mask] * np.log2(p[mask] / q[mask])))
    Dbits = relent(r, s)
    ok_ns &= abs(Dpq - Dbits) < 1e-8
    Dnat = Dbits * LN2
    bc = np.trace(msqrt(r) @ msqrt(s)).real
    ok_bc &= bc >= math.exp(-Dnat / 2) - 1e-12
    lhs = np.linalg.norm(msqrt(r) - msqrt(s)) ** 2
    ok_sq &= lhs <= Dnat + 1e-12
    best = max(best, lhs / Dnat if Dnat > 1e-12 else 0)
R.check("Nussbaum-Szkola distributions p_ij = r_i |<i|j>|^2, q_ij = s_j |<i|j>|^2 have D(p||q) = D(rho||sigma)", bool(ok_ns))
R.check("Tr sqrt(rho) sqrt(sigma) >= e^{-D_nat/2} and ||sqrt rho - sqrt sigma||_2^2 <= D_nat(rho||sigma) (2000 pairs)",
        ok_bc and ok_sq and best > 0.45, f"largest ratio {best:.3f} (about 1/2 for nearby states)")


# ---------------------------------------------------------------------------------------------------- 5. commutator
def commutator_data(d, dB, U, tau, H, beta):
    """S, A (copy of S), B. W = U_AB^* U_SB on S A B; eta = gamma_S x gamma_A x tau_B."""
    g = gibbs(H, beta)
    from qtools import embed
    dims = [d, d, dB]
    USB = embed(U, [0, 2], dims)
    UAB = embed(U, [1, 2], dims)
    W = UAB.conj().T @ USB
    eta = np.kron(np.kron(g, g), tau)
    comm = W @ msqrt(eta) - msqrt(eta) @ W
    G, *_ = defect_pair(U, tau, H, beta, d, dB)
    return W, eta, np.linalg.norm(comm), G, g


ok_ch, ok_cb, ok_mix = True, True, True
ratios = []
for trial in range(150):
    d, dB = 2, int(rng.integers(2, 4))
    H = np.diag([0.0, rng.uniform(0.3, 2)])
    beta = rng.uniform(0.3, 2)
    if trial % 3 == 0:                                   # near-thermal: thermal operation perturbed slightly
        HB = rng.integers(0, 3, dB).astype(float) * H[1, 1]
        U0, tau = thermal_operation(np.diag(H), HB, beta, rng)
        K = random_herm(d * dB, rng)
        eps = 10 ** rng.uniform(-4, -1)
        U = U0 @ mfun(K, lambda w: np.exp(1j * eps * w))
    else:
        U = random_unitary(d * dB, rng)
        tau = random_density(dB, rng)
    W, eta, c, G, g = commutator_data(d, dB, U, tau, H, beta)
    ok_cb &= c <= 2 * math.sqrt(LN2 * max(G, 0)) + 1e-9
    ratios.append(c / (2 * math.sqrt(LN2 * G)) if G > 1e-14 else 0)
    # W with bath gamma_A x tau_B implements the same channel on S
    rho = random_density(d, rng)
    outW = ptrace(W @ np.kron(np.kron(rho, g), tau) @ W.conj().T, [d, d, dB], [0])
    outU = ptrace(U @ np.kron(rho, tau) @ U.conj().T, [d, dB], [0])
    ok_ch &= np.allclose(outW, outU, atol=1e-12)
    t = rng.uniform(0, 0.3)
    sig_t = (1 - t) * np.kron(g, tau) + t * np.eye(d * dB) / (d * dB)
    eta_t = np.kron(g, sig_t)
    c_t = np.linalg.norm(W @ msqrt(eta_t) - msqrt(eta_t) @ W)
    ok_mix &= abs(c_t - c) <= 2 * math.sqrt(2 * t) + 1e-12
    outt = ptrace(W @ np.kron(rho, sig_t) @ W.conj().T, [d, d, dB], [0])
    ok_mix &= 0.5 * trace_norm(outt - outW) <= t + 1e-12
R.check("W = U_AB^* U_SB with bath gamma_A x tau_B implements the same channel", bool(ok_ch))
R.check("||[W, sqrt(gamma x sigma_D)]||_2 <= 2 sqrt(ln2 G_Dil) (150 dilations, a third near-thermal)", bool(ok_cb),
        f"largest ratio {max(ratios):.3f}")
R.check("mixing sigma_D with I/dim D changes the channel by at most t and the commutator by at most 2 sqrt(2t)",
        bool(ok_mix))

# ---------------------------------------------------------------------------------------------------- 6. C_z
ok, best = True, 0.0
us = np.concatenate([np.linspace(-40, 40, 40001), np.linspace(-1.2, 1.2, 24001)])
for z in np.concatenate([np.linspace(0.01, 5, 200), [10.0, 50.0]]):
    Cz = max(2 * math.exp(0.5) * z, 2 / (1 - math.exp(-0.5)))
    lhs = np.abs(np.exp(1j * z * us) - 1)
    rhs = Cz * np.abs(np.exp(us / 2) - 1)
    mask = np.abs(us) > 1e-12
    ok &= bool(np.all(lhs[mask] <= rhs[mask] + 1e-12))
    best = max(best, float(np.max(lhs[mask] / rhs[mask])))
R.check("|x^{iz} - 1| <= C_z |sqrt x - 1| with C_z = max{2 e^{1/2}|z|, 2/(1 - e^{-1/2})} (x = e^u on a dense grid)",
        ok and best > 0.65, f"largest ratio over the grid {best:.3f}: the constant is valid, not optimal")
ok = True
for _ in range(200):
    dd = int(rng.integers(2, 6))
    eta = random_density(dd, rng)
    Wr = random_unitary(dd, rng)
    z = rng.uniform(-3, 3)
    Cz = max(2 * math.exp(0.5) * abs(z), 2 / (1 - math.exp(-0.5)))
    etaiz = mfun(eta, lambda w: np.exp(1j * z * np.log(w)))
    Xc = Wr @ etaiz - etaiz @ Wr
    lhs = math.sqrt(np.trace(eta @ Xc.conj().T @ Xc).real)          # ||X||_{2,eta}^2 = Tr(eta X^* X)
    rhs = Cz * np.linalg.norm(Wr @ msqrt(eta) - msqrt(eta) @ Wr)
    ok &= lhs <= rhs + 1e-12
R.check("||[W, eta^{iz}]||_{2,eta} <= C_z ||[W, sqrt eta]||_2 (200 random W, eta, z)", bool(ok))

# ---------------------------------------------------------------------------------------------------- 7. twirl
omega = np.array([1.0, math.sqrt(2)])
avec = [np.array([0, 0]), np.array([1, 0]), np.array([0, 1]), np.array([1, 1])]
E = np.array([a @ omega for a in avec])
dS = 4


def full_twirl_choi(J):
    """Keep exactly the Choi entries with E_e - E_f = E_g - E_h (input e,g; output f,h)."""
    out = np.zeros_like(J)
    for e, f, g, h in itertools.product(range(dS), repeat=4):
        if abs((E[e] - E[f]) - (E[g] - E[h])) < 1e-9:
            out[e * dS + f, g * dS + h] = J[e * dS + f, g * dS + h]
    return out


def discrete_twirl_choi(J, Q):
    out = np.zeros_like(J)
    for th in itertools.product(range(Q), repeat=2):
        phase = np.array([np.exp(1j * 2 * math.pi * (a @ np.array(th)) / Q) for a in avec])
        D = np.diag(phase)
        Dk = np.kron(D.conj(), D)               # Choi of D^* . conj applied to input, D on output: covariance twirl
        out += Dk @ J @ Dk.conj().T
    return out / Q ** 2


Kr = [random_unitary(dS, rng) / 2 for _ in range(4)]
from qtools import choi_of_map
J = choi_of_map(lambda X: kraus_apply(Kr, X), dS)
Qmin = 1 + max(int(np.max(np.abs(avec[e] - avec[f] - avec[g] + avec[h]))) for e, f, g, h in itertools.product(range(dS), repeat=4))
ok_tw = np.allclose(discrete_twirl_choi(J, Qmin), full_twirl_choi(J), atol=1e-12)
ok_small = not np.allclose(discrete_twirl_choi(J, 2), full_twirl_choi(J), atol=1e-6)
# commutation with every D_theta <=> covariance
Jc = full_twirl_choi(J)
ok_cov = True
for _ in range(20):
    th = rng.uniform(0, 2 * math.pi, 2)
    D = np.diag(np.exp(1j * np.array([a @ th for a in avec])))
    Dk = np.kron(D.conj(), D)
    ok_cov &= np.allclose(Dk @ Jc @ Dk.conj().T, Jc, atol=1e-12)
    t = rng.uniform(0, 20)
    Dt = np.diag(np.exp(-1j * t * E))
    Dtk = np.kron(Dt.conj(), Dt)
    ok_cov &= np.allclose(Dtk @ Jc @ Dtk.conj().T, Jc, atol=1e-12)
R.check("the discrete average over Q^r phases equals the full twirl for Q = 1 + max|a_e - a_f - a_g + a_h| "
        f"(Q = {Qmin}), not for Q = 2; the twirled channel commutes with every D_theta and with time evolution",
        bool(ok_tw and ok_small and ok_cov))
# flagged twirl preserves the defect exactly
ok = True
for _ in range(20):
    d, dB = 4, 2
    U = random_unitary(d * dB, rng)
    tau = random_density(dB, rng)
    beta = rng.uniform(0.2, 2)
    H = np.diag(E)
    G0, *_ = defect_pair(U, tau, H, beta, d, dB)
    Q = Qmin
    thetas = list(itertools.product(range(Q), repeat=2))
    nf = len(thetas)
    Ut = np.zeros((d * nf * dB, d * nf * dB), dtype=complex)
    for k, th in enumerate(thetas):
        D = np.diag(np.exp(1j * 2 * math.pi * np.array([a @ np.array(th) for a in avec]) / Q))
        Uk = np.kron(D, np.eye(dB)) @ U @ np.kron(D.conj().T, np.eye(dB))
        Pk = np.zeros((nf, nf))
        Pk[k, k] = 1
        T4 = Uk.reshape(d, dB, d, dB)
        Ut += np.einsum("abce,fg->afbcge", T4, Pk).reshape(d * nf * dB, d * nf * dB)
    taut = np.kron(np.eye(nf) / nf, tau)
    G1, *_ = defect_pair(Ut, taut, H, beta, d, nf * dB)
    ok &= abs(G1 - G0) < 1e-9
R.check("the flagged twirl of a dilation has exactly the same Gibbs defect", bool(ok))

# ---------------------------------------------------------------------------------------------------- 8. replacement
ok = True
for _ in range(500):
    dB = int(rng.integers(2, 8))
    sig = random_density(dB, rng)
    w, v = np.linalg.eigh(sig)
    h = rng.uniform(0.01, 1)
    s = rng.uniform(0, h)
    xi = -np.log(w)
    xr = np.floor((xi + s) / h) * h - s                          # round down to the grid hZ - s
    sp_ = np.exp(-xr)
    sp_ /= sp_.sum()
    ok &= bool(np.all(sp_ <= math.exp(h) * w + 1e-15) and np.all(sp_ >= math.exp(-h) * w - 1e-15))
R.check("the randomly offset rounding of the bath energies gives e^{-h} sigma <= sigma' <= e^h sigma", bool(ok))
ok, best = True, 0.0
for h in np.linspace(0.01, 3, 300):
    u = np.linspace(-10, 10, 20001)
    lhs = np.minimum(1, np.abs(u) / h)
    rhs = np.abs(np.exp(u / 2) - 1) / (1 - math.exp(-h / 2))
    ok &= bool(np.all(lhs <= rhs + 1e-12))
    best = max(best, float(np.max(lhs / np.where(rhs > 0, rhs, np.inf))))
# Monte Carlo of the separation probability
mc = []
for _ in range(5):
    h, a, b = 0.7, rng.uniform(0, 3), rng.uniform(0, 3)
    s = rng.uniform(0, h, 200000)
    sep = np.mean(np.floor((a + s) / h) != np.floor((b + s) / h))
    mc.append(abs(sep - min(1, abs(a - b) / h)))
R.check("two logarithms are separated with probability min(1, |ln(p_a/p_b)|/h) <= |sqrt(p_a/p_b) - 1|/(1 - e^{-h/2})",
        ok and best > 0.999 and max(mc) < 5e-3, f"largest ratio {best:.4f} (equality at ln(p_a/p_b) = -h)")
ok = True
for r in (2, 3):
    for _ in range(40):
        v = rng.uniform(0, 1, r - 1)
        L = int(rng.integers(2, 25))
        found = any(all(abs(q * vk - round(q * vk)) <= 1 / L + 1e-12 for vk in v) for q in range(1, L ** (r - 1) + 1))
        ok &= found
R.check("Dirichlet: some 1 <= q <= L^{r-1} has |q v_k - p_k| <= 1/L for all k (r = 2, 3; random v, L)", bool(ok))
# lattice isometries J_k
omega = np.array([1.0, math.sqrt(2)])
q_L, pk = 5, 7                                                     # omega_0 = (1, 7/5) approximates sqrt2
omega0 = np.array([1.0, pk / q_L])
avec = [np.array([0, 0]), np.array([1, 0]), np.array([0, 1]), np.array([2, 1])]
Estar = 0.3
H = np.array([Estar + a @ omega for a in avec])
H0 = np.array([Estar + a @ omega0 for a in avec])
N, A = 6, 2
EL0 = 1.7
ok = True
for k in itertools.product(range(-N + A, N - A + 1), repeat=2):
    k = np.array(k)
    vals = [H[e] + EL0 + (k - avec[e]) @ (omega - omega0) - H0[e] for e in range(4)]
    ok &= max(vals) - min(vals) < 1e-12                           # J_k^*(H + H_L)J_k = H_0 + const
images = set()
for k in itertools.product(range(-N + A, N - A + 1), repeat=2):
    for e in range(4):
        images.add((e, tuple(np.array(k) - avec[e])))
ok &= len(images) == 4 * (2 * (N - A) + 1) ** 2                   # orthogonal images
for beta in (0.5, 2.0):
    labels = list(itertools.product(range(-N, N + 1), repeat=2))
    en = np.array([np.array(l) @ (omega - omega0) for l in labels])
    p = np.exp(-beta * (en - en.min()))
    p /= p.sum()
    outer = sum(pp for l, pp in zip(labels, p) if max(abs(l[0]), abs(l[1])) > N - 2 * A)
    bound = 4 * 2 * A / (2 * N + 1) + 2 * beta * N * np.sum(np.abs(omega - omega0))
    ok &= outer <= bound
R.check("lattice: J_k^*(H + H_L)J_k = H_0 + const with orthogonal images, and the outer labels have Gibbs probability "
        "<= 4rA/(2N+1) + 2 beta N ||omega - omega_0||_1", bool(ok))
G, r = sp.symbols("G r", positive=True)
L = G ** (-1 / (2 * r))
N_ = L ** sp.Rational(1, 3)
e1 = sp.simplify(sp.log(L ** sp.Rational(-1, 3)) / sp.log(G))
e2 = sp.simplify(sp.log(G ** sp.Rational(1, 4) * L ** (r / 2 - sp.Rational(1, 3))) / sp.log(G))
e3 = sp.simplify(sp.log(N_ / L) / sp.log(G))
hh = sp.symbols("h", positive=True)
bal = sp.solve(sp.Eq(hh, G ** sp.Rational(1, 4) * hh ** sp.Rational(-1, 2)), hh)
R.check("exponents: L^{-1/3} and G^{1/4} L^{r/2 - 1/3} are G^{1/(6r)}, N/L is smaller, and for r <= 1 the balance "
        "h = G^{1/4} h^{-1/2} gives G^{1/6}",
        sp.simplify(e1 - 1 / (6 * r)) == 0 and sp.simplify(e2 - 1 / (6 * r)) == 0
        and sp.simplify(e3 - 1 / (3 * r)) == 0 and any(sp.simplify(b - G ** sp.Rational(1, 6)) == 0 for b in bal))
R.close()
