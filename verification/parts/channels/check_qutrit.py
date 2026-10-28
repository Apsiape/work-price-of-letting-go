"""A Gibbs-preserving qutrit process that is not free in real time (Proposition "A Gibbs-preserving process that is
not free in real time", Lemma "Coherence and transfer", Appendix "The qutrit channel" and "A single input",
Section 8 "Open problems").

H = diag(0, E1, E2), lambda = e^{-beta E2}, Kraus operators diag(sqrt(1-lambda), 1, 0), sqrt(lambda)|2><0|, |0><2|.

Checks:
  1. the channel is trace preserving, time-covariant and Gibbs-preserving (exact, symbolic), so T_cap = 0 (sampled);
     its 0-1 coherence sqrt(1-lambda) is as large as positivity allows; the minimal Stinespring isometry;
  2. random exact dilations with an untouched purifying register (300, built from the general form of the proof): the
     dilation is exact and leaves R alone, Tr_B|v><w| = 0, the bath output at the Gibbs input is
     (1 - 2g_2)nu_v + g_2 nu_z + g_2 nu_w, and G_Dil >= g_1 D(nu_v||omega) >= g_1 log2 1/Tr(P omega)
     >= g_1 log2 1/(1 - g_2); the approximate estimate tends to the same value as the error vanishes;
  3. Lemma "Coherence and transfer" on 1500 random thermal operations (commensurate and incommensurate gaps, random
     baths), with the mode identities (eq. modes) and the covariance pattern, and on the truncated-oscillator
     construction, which attains the bound as K grows (c = 1 - W + W a, T20 = W(1 - a^2), W = lambda(1 - lambda^K)/
     (1 - lambda^{K+1}));
  4. Gibbs preservation forces T01 = 0, T02 = 1, T20 = lambda when the output populations on psi_0 are those of
     Phi(psi_0) (identity lambda(T02 - 1) = T01(1 - g1/g0), and a linear program);
  5. the single-input bound: delta(lambda) = Delta^2/(4 Delta + k) with k = 2 lambda(1 + 2s)/(1 - lambda); the least
     error compatible with Steps 1-2 and the Lemma, computed by bisection, is at least delta(lambda) for 40 values of
     lambda; the bound holds for every thermal operation tested; delta ~ lambda/32 as lambda -> 0 and
     ~ (1 - lambda)^2/2 as lambda -> 1;
  6. the bound u^2/(2c^2) exceeds delta(lambda) only for lambda above about 0.97 (for every E1 < E2);
  7. the numbers at E2 = 2E1, beta E1 = ln 2: lambda = 1/4, T_rt >= (2/7) log2(7/6) ~ 0.064, delta(1/4) ~ 5.9e-3;
  8. partial-swap thermal operations come within about 0.10 lambda of Phi(psi_0) at low temperature and (1-lambda)/2 at
     high temperature, and a numerical search over thermal operations with small baths finds nothing closer.
"""
import math

import numpy as np
import sympy as sp
from scipy.optimize import linprog, minimize, minimize_scalar

from qtools import Report, dm, entropy, h2, kraus_apply, random_unitary, relent, trace_norm

R = Report("Qutrit process")
rng = np.random.default_rng(20261016)


def channel(lam):
    a = math.sqrt(1 - lam)
    return [np.diag([a, 1, 0]).astype(complex), math.sqrt(lam) * np.outer(np.eye(3)[2], np.eye(3)[0]).astype(complex),
            np.outer(np.eye(3)[0], np.eye(3)[2]).astype(complex)]


def gibbs_pops(bE1, bE2):
    g = np.array([1, math.exp(-bE1), math.exp(-bE2)])
    return g / g.sum()


def delta_lam(lam):
    s = math.sqrt(1 - lam)
    D = s - (1 - lam)
    return (1 - lam) * D * D / (4 * (1 - lam) * D + 2 * lam * (1 + 2 * s))


# ---------------------------------------------------------------------------------------------------- 1. channel
lam_s, g0s, g1s = sp.symbols("lambda g0 g1", positive=True)
a_s = sp.sqrt(1 - lam_s)
Ks = [sp.diag(a_s, 1, 0), sp.sqrt(lam_s) * sp.Matrix(3, 3, lambda i, j: 1 if (i, j) == (2, 0) else 0),
      sp.Matrix(3, 3, lambda i, j: 1 if (i, j) == (0, 2) else 0)]
TP = sp.simplify(sum((Kk.T * Kk for Kk in Ks), sp.zeros(3)) - sp.eye(3))
gam = sp.diag(g0s, g1s, lam_s * g0s)
GP = sp.simplify(sum((Kk * gam * Kk.T for Kk in Ks), sp.zeros(3)) - gam)
R.check("trace preserving and Gibbs-preserving for every lambda in (0, 1) (symbolic, g2 = lambda g0)",
        TP == sp.zeros(3) and GP == sp.zeros(3))
ok = True
for bE1, bE2 in [(0.3, 1.1), (1.0, math.sqrt(5)), (0.5, 0.5 + math.pi / 7)]:
    K = channel(math.exp(-bE2))
    for _ in range(10):
        r = rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3))
        t = rng.uniform(0, 10)
        Dt = np.diag(np.exp(-1j * t * np.array([0, bE1, bE2])))
        ok &= np.allclose(kraus_apply(K, Dt @ r @ Dt.conj().T), Dt @ kraus_apply(K, r) @ Dt.conj().T, atol=1e-12)
R.check("time-covariant: Phi(e^{-iHt} X e^{iHt}) = e^{-iHt} Phi(X) e^{iHt} (random X, t, generic gaps)", bool(ok))
worst = -1e9
for _ in range(3000):
    bE1 = rng.uniform(0.05, 3)
    bE2 = bE1 + rng.uniform(0.05, 3)
    g = gibbs_pops(bE1, bE2)
    K = channel(math.exp(-bE2))
    G = rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3))
    r = G @ G.conj().T
    r /= np.trace(r).real
    gm = np.diag(g)
    worst = max(worst, relent(kraus_apply(K, r), gm) - relent(r, gm))
R.check("T_cap = max_rho [D(Phi(rho)||gamma) - D(rho||gamma)] = 0 (3000 sampled inputs, value 0 at gamma)", worst <= 1e-10,
        f"largest sampled value {worst:.1e}")
lam = 0.3
K = channel(lam)
T = np.array([[np.real(kraus_apply(K, dm(np.eye(3)[i]))[j, j]) for i in range(3)] for j in range(3)])
coh = kraus_apply(K, np.outer(np.eye(3)[0], np.eye(3)[1]))[0, 1]
R.check("it leaves level 1 alone, resets level 2, excites the ground state with probability lambda, and keeps the "
        "0-1 coherence sqrt(1-lambda) = sqrt(T00 T11), the largest positivity allows",
        np.allclose(T, [[1 - lam, 0, 1], [0, 1, 0], [lam, 0, 0]]) and abs(coh - math.sqrt(1 - lam)) < 1e-14
        and abs(abs(coh) - math.sqrt(T[0, 0] * T[1, 1])) < 1e-14)


# ---------------------------------------------------------------------------------------------------- 2. dilations
def random_exact_dilation(lam, m, rng):
    """Build M_v, M_z, M_w : C^m -> B with M_v^* M_w = 0, Tr(tau M_v^* M_z) = Tr(tau M_w^* M_z) = 0 and isometries;
    U|i>|r> = sum_k K_k|i> (x) M_k|r> is then an isometry (the proof's general form, with R purifying tau)."""
    tight = rng.random() < 0.3
    tau = np.ones(m) / m if tight else rng.dirichlet(np.ones(m) * rng.uniform(0.3, 3))
    dB = 4 * m
    Q = random_unitary(dB, rng)
    Mv, Mw, F = Q[:, :m], Q[:, m:2 * m], Q[:, 2 * m:3 * m]
    shift = np.roll(np.eye(m), 1, axis=0)                 # zero diagonal, so Tr(tau X) = 0
    th1, th2 = rng.uniform(0, math.pi / 2, 2) * (rng.random() < 0.8)
    if tight and m > 1:
        th1 = math.pi / 2
    ph = np.diag(np.exp(1j * rng.uniform(0, 2 * math.pi, m)))
    c1, c2 = math.cos(th1), math.sin(th1)
    Mz = c1 * (math.cos(th2) * F + math.sin(th2) * Mw @ shift @ ph) + c2 * Mv @ shift
    if m == 1:
        Mz = F
    return tau, [Mv, Mz, Mw]


def dilation_data(lam, g, tau, Ms):
    K = channel(lam)
    m = len(tau)
    dB = Ms[0].shape[0]
    # isometry U: S (x) C^m -> S (x) B
    U = sum(np.kron(K[k], Ms[k]) for k in range(3))
    phi = sum(math.sqrt(tau[r]) * np.kron(np.eye(m)[r], np.eye(m)[r]) for r in range(m))    # B0 (x) R
    return K, U, phi


worst_iso = worst_ch = worst_R = worst_vw = worst_om = 0.0
chain_ok, ratios, tight_tail = True, [], 0
for trial in range(300):
    bE1 = rng.uniform(0.1, 2.5)
    bE2 = bE1 + rng.uniform(0.1, 2.5)
    lam = math.exp(-bE2)
    g = gibbs_pops(bE1, bE2)
    m = int(rng.integers(1, 4))
    tau, Ms = random_exact_dilation(lam, m, rng)
    K, U, phi = dilation_data(lam, g, tau, Ms)
    dB = Ms[0].shape[0]
    worst_iso = max(worst_iso, np.abs(U.conj().T @ U - np.eye(3 * m)).max())
    # joint output state on S B R for an input rho
    rho = np.diag(g).astype(complex)
    inp = np.kron(rho, dm(phi))                         # S (x) B0 (x) R
    UR = np.kron(U, np.eye(m))
    out = UR @ inp @ UR.conj().T                         # S (x) B (x) R
    t6 = out.reshape(3, dB, m, 3, dB, m)
    sysout = np.einsum("abrcbr->ac", t6)
    worst_ch = max(worst_ch, np.abs(sysout - kraus_apply(K, rho)).max())
    rhoR = np.einsum("abrabs->rs", t6)
    worst_R = max(worst_R, np.abs(rhoR - np.diag(tau)).max())
    v, z, w = [(Mk @ np.diag(np.sqrt(tau))).reshape(-1) for Mk in Ms]        # vectors in B (x) R
    trB = lambda x, y: np.einsum("br,bs->rs", x.reshape(dB, m), y.reshape(dB, m).conj())
    worst_vw = max(worst_vw, np.abs(trB(v, w)).max())
    nu = lambda x: np.einsum("br,cr->bc", x.reshape(dB, m), x.reshape(dB, m).conj())
    Omega_SB = np.einsum("abrcdr->abcd", t6).reshape(3 * dB, 3 * dB)
    omega = np.einsum("abad->bd", Omega_SB.reshape(3, dB, 3, dB))
    nv, nz, nw = nu(v), nu(z), nu(w)
    worst_om = max(worst_om, np.abs(omega - ((1 - 2 * g[2]) * nv + g[2] * nz + g[2] * nw)).max())
    G = relent(Omega_SB, np.kron(np.diag(g), omega))
    # the support projector of nu_v and the chain
    wv, vv = np.linalg.eigh(nv)
    P = vv[:, wv > 1e-12] @ vv[:, wv > 1e-12].conj().T
    # D(nu_v||omega) on the support of omega
    Dv = relent(nv, omega + 1e-300 * np.eye(dB))
    TrP = float(np.trace(P @ omega).real)
    b3 = g[1] * math.log2(1 / (1 - g[2]))
    chain_ok &= G >= g[1] * Dv - 1e-9 and Dv >= math.log2(1 / TrP) - 1e-9 and TrP <= 1 - g[2] + 1e-12
    ratios.append(G / b3)
    tight_tail += g[1] * Dv / b3 < 1 + 1e-6
R.check("random exact dilations (300): U is an isometry implementing Phi exactly and leaving R untouched",
        worst_iso < 1e-12 and worst_ch < 1e-12 and worst_R < 1e-12, f"{worst_iso:.1e}, {worst_ch:.1e}, {worst_R:.1e}")
R.check("Tr_B|v><w| = 0, and the bath output at gamma is (1 - 2g2) nu_v + g2 nu_z + g2 nu_w",
        worst_vw < 1e-12 and worst_om < 1e-12)
R.check("G_Dil >= g1 D(nu_v||omega) >= g1 log2 1/Tr(P omega) >= g1 log2 1/(1 - g2) on every dilation",
        chain_ok and min(ratios) >= 1 - 1e-9 and tight_tail >= 30,
        f"min G / bound = {min(ratios):.3f}; the last two links are tight in {tight_tail} cases, the first is not")


def d2(p_, q_):
    out = 0.0
    if p_ > 0:
        out += p_ * math.log2(p_ / q_)
    if p_ < 1:
        out += (1 - p_) * math.log2((1 - p_) / (1 - q_))
    return out


ok = True
for bE1, bE2 in [(0.4, 1.0), (1.0, 2.0), (0.1, 3.0)]:
    g = gibbs_pops(bE1, bE2)
    a = math.sqrt(1 - math.exp(-bE2))
    target = g[1] * math.log2(1 / (1 - g[2]))
    vals = []
    for t in (1e-3, 1e-5, 1e-7, 1e-9):
        e = 2 * t / a
        vals.append(g[1] * d2(e, g[2] * (1 - e)) - t * math.log2(3) - 3 * h2(t))
    ok &= all(v2 >= v1 for v1, v2 in zip(vals, vals[1:])) and abs(vals[-1] - target) < 1e-6 and abs(d2(0, g[2]) - math.log2(1 / (1 - g[2]))) < 1e-15
R.check("the approximate estimate g1 d2(2t/a || g2(1 - 2t/a)) - t log2 3 - 3h(t) increases to g1 log2 1/(1-g2) as t -> 0",
        bool(ok))


# ---------------------------------------------------------------------------------------------------- 3. lemma
def thermal_op(E1, E2, beta, bath_levels, rng, structured=None):
    """Thermal operation with bath levels [(energy, degeneracy)], a random energy-conserving unitary (Haar inside each
    total-energy eigenspace), or a supplied unitary. Returns the Choi-type data: T, c, and the full channel."""
    HS = np.array([0.0, E1, E2])
    HB = np.concatenate([[e] * dg for e, dg in bath_levels])
    dB = len(HB)
    tot = (HS[:, None] + HB[None, :]).reshape(-1)
    if structured is None:
        U = np.zeros((3 * dB, 3 * dB), dtype=complex)
        keys = np.round(tot, 9)
        for e in np.unique(keys):
            idx = np.where(keys == e)[0]
            U[np.ix_(idx, idx)] = random_unitary(len(idx), rng)
    else:
        U = structured
    pB = np.exp(-beta * HB)
    pB /= pB.sum()
    gB = np.diag(pB)

    def theta(rho):
        out = U @ np.kron(rho, gB) @ U.conj().T
        return np.einsum("aibi->ab", out.reshape(3, dB, 3, dB))
    return U, HB, pB, theta


def lemma_data(theta):
    T = np.array([[np.real(theta(dm(np.eye(3)[i]))[j, j]) for i in range(3)] for j in range(3)])
    c = theta(np.outer(np.eye(3)[0], np.eye(3)[1]))[0, 1]
    return T, c


def oscillator(E2, Kmax, aprime):
    """Truncated oscillator bath 0, E2, ..., K E2 (one state each); rotate |0>|k> <-> |2>|k-1> by cosine a', level 1
    alone."""
    dB = Kmax + 1
    U = np.eye(3 * dB, dtype=complex)
    s = math.sqrt(1 - aprime ** 2)
    for k in range(1, dB):
        i, j = 0 * dB + k, 2 * dB + (k - 1)
        U[i, i], U[j, j], U[i, j], U[j, i] = aprime, aprime, -s, s
    return U, [(k * E2, 1) for k in range(dB)]


ok_lemma, ok_modes, ok_cov, gaps = True, True, True, []
for trial in range(1500):
    beta = 1.0
    E1 = rng.uniform(0.1, 2)
    E2 = 2 * E1 if trial % 3 == 0 else E1 + rng.uniform(0.1, 2)
    lam = math.exp(-beta * E2)
    if trial % 2 == 0:
        levels = []
        for a_ in range(3):
            for b_ in range(3):
                dg = int(rng.integers(0, 3))
                if dg:
                    levels.append((a_ * E1 + b_ * E2, dg))
        if not levels:
            levels = [(0.0, 1)]
        U, HB, pB, theta = thermal_op(E1, E2, beta, levels, rng)
    else:
        Kmax = int(rng.integers(1, 40))
        ap = rng.uniform(0, 1)
        U, levels = oscillator(E2, Kmax, ap)
        if rng.random() < 0.5:                         # perturb inside the total-energy blocks
            U2, HB, pB, _ = thermal_op(E1, E2, beta, levels, rng)
            eps = rng.uniform(0, 0.05)
            Hpert = (U2 - U2.conj().T) / 2j
            Hpert = (Hpert + Hpert.conj().T) / 2
            w_, v_ = np.linalg.eigh(Hpert)
            U = U @ ((v_ * np.exp(1j * eps * w_)) @ v_.conj().T)
        U, HB, pB, theta = thermal_op(E1, E2, beta, levels, rng, structured=U)
    T, c = lemma_data(theta)
    bound = 1 - lam + math.sqrt(max(0.0, lam * (lam - T[2, 0])))
    ok_lemma &= T[2, 0] <= lam + 1e-12 and abs(c) <= bound + 1e-12
    gaps.append(bound - abs(c))
    # modes: blocks A_E, B_E, C_E
    dB = len(HB)
    cm = T00 = T11 = T20 = 0
    seen = np.zeros(dB, bool)
    for i0 in range(dB):
        if seen[i0]:
            continue
        idx = np.where(np.abs(HB - HB[i0]) < 1e-9)[0]
        seen[idx] = True
        pE = pB[idx[0]]
        A = U[np.ix_(0 * dB + idx, 0 * dB + idx)]
        Bm = U[np.ix_(1 * dB + idx, 1 * dB + idx)]
        tgt = np.where(np.abs(HB - (HB[i0] - E2)) < 1e-9)[0]
        Cm = U[np.ix_(2 * dB + tgt, 0 * dB + idx)] if len(tgt) else np.zeros((0, len(idx)))
        cm += pE * np.trace(Bm.conj().T @ A)
        T00 += pE * np.linalg.norm(A) ** 2
        T11 += pE * np.linalg.norm(Bm) ** 2
        T20 += pE * np.linalg.norm(Cm) ** 2
    ok_modes &= abs(cm - c) < 1e-10 and abs(T00 - T[0, 0]) < 1e-10 and abs(T11 - T[1, 1]) < 1e-10 and abs(T20 - T[2, 0]) < 1e-10
    if E2 != 2 * E1:
        for (i_, k_) in [(0, 2), (2, 0), (1, 2), (0, 0), (2, 1)]:
            ok_cov &= abs(theta(np.outer(np.eye(3)[i_], np.eye(3)[k_]))[0, 1]) < 1e-12
gaps = np.array(gaps)
R.check("Lemma: T20 <= lambda and |c| <= 1 - lambda + sqrt(lambda(lambda - T20)) for 1500 thermal operations",
        ok_lemma and np.sum(gaps < 1e-3) >= 100, f"{np.sum(gaps < 1e-3)} within 1e-3 of equality, min gap {gaps.min():.2e}")
R.check("mode identities: c = sum_E p_E Tr(B_E^* A_E), T00, T11, T20 = sum_E p_E ||.||_2^2", bool(ok_modes))
R.check("covariance: <0|Theta(|i><k|)|1> = 0 unless E_k - E_i = E1 (incommensurate gaps)", bool(ok_cov))
ok = True
for lam in (0.1, 0.4, 0.8):
    E2 = -math.log(lam)
    for ap in (0.0, 0.3, 0.9):
        for Kmax in (1, 3, 10):
            U, levels = oscillator(E2, Kmax, ap)
            _, _, _, theta = thermal_op(0.37 * E2, E2, 1.0, levels, rng, structured=U)
            T, c = lemma_data(theta)
            W = lam * (1 - lam ** Kmax) / (1 - lam ** (Kmax + 1))
            ok &= abs(c - (1 - W + W * ap)) < 1e-12 and abs(T[2, 0] - W * (1 - ap ** 2)) < 1e-12
        U, levels = oscillator(E2, 400, ap)
        _, _, _, theta = thermal_op(0.37 * E2, E2, 1.0, levels, rng, structured=U)
        T, c = lemma_data(theta)
        # the square root turns a rounding error of 1e-16 in lambda - T20 into about 1e-8
        ok &= abs((1 - lam + math.sqrt(max(0.0, lam * (lam - T[2, 0])))) - abs(c)) < 1e-7
R.check("the truncated oscillator gives c = 1 - W + W a, T20 = W(1 - a^2) and attains the bound as K -> infinity", bool(ok))

# ---------------------------------------------------------------------------------------------------- 4. populations
T = sp.Matrix(3, 3, lambda i, j: sp.Symbol(f"T{i}{j}", nonnegative=True))
lam_, r1 = sp.symbols("lambda r1", positive=True)                # r1 = g1/g0 < 1
gvec = sp.Matrix([1, r1, lam_])                                   # Gibbs vector up to normalization
eqs = list(T * gvec - gvec) + [sum(T[:, j]) - 1 for j in range(3)] + [T[0, 0] + T[0, 1] - (1 - lam_), T[1, 0] + T[1, 1] - 1,
                                                                    T[2, 0] + T[2, 1] - lam_]
# derived identity: lambda (T02 - 1) = T01 (1 - r1) on the constraint set
sol = sp.solve([eqs[0], eqs[6]], [T[0, 0], T[0, 2]], dict=True)[0]
ident = sp.simplify(lam_ * (sol[T[0, 2]] - 1) - T[0, 1] * (1 - r1))
okLP = True
for _ in range(50):
    lv, rv = rng.uniform(0.05, 0.9), rng.uniform(0.05, 0.99)
    rv = min(rv, 0.99)
    lv = min(lv, rv * 0.999)                                      # E2 > E1: lambda < g1/g0
    A_eq, b_eq = [], []
    for row in range(3):
        cvec = np.zeros(9)
        cvec[3 * row:3 * row + 3] = [1, rv, lv]
        A_eq.append(cvec), b_eq.append([1, rv, lv][row])
    for col in range(3):
        cvec = np.zeros(9)
        cvec[[col, 3 + col, 6 + col]] = 1
        A_eq.append(cvec), b_eq.append(1)
    for row, val in [(0, 1 - lv), (1, 1), (2, lv)]:
        cvec = np.zeros(9)
        cvec[3 * row:3 * row + 2] = 1
        A_eq.append(cvec), b_eq.append(val)
    for idx, sense in [(1, -1), (2, 1), (6, 1), (6, -1)]:          # max T01, min T02, min/max T20
        cvec = np.zeros(9)
        cvec[idx] = -sense if sense == -1 else sense
        res = linprog(cvec, A_eq=np.array(A_eq), b_eq=b_eq, bounds=[(0, 1)] * 9, method="highs")
        val = res.x[idx]
        okLP &= res.status == 0 and {1: abs(val) < 1e-9, 2: abs(val - 1) < 1e-9, 6: abs(val - lv) < 1e-9}[idx]
R.check("Gibbs preservation with the populations of Phi(psi_0) forces T01 = 0, T02 = 1 and T20 = lambda "
        "(identity lambda(T02 - 1) = T01(1 - g1/g0), and 50 linear programs)", ident == 0 and okLP)

# ---------------------------------------------------------------------------------------------------- 5. single input
lv = sp.symbols("lambda", positive=True)
s = sp.sqrt(1 - lv)
Dl = s - (1 - lv)
k = 2 * lv * (1 + 2 * s) / (1 - lv)
dsym = (1 - lv) * Dl ** 2 / (4 * (1 - lv) * Dl + 2 * lv * (1 + 2 * s))
R.check("delta(lambda) = Delta^2/(4 Delta + k) with k = 2 lambda (1 + 2s)/(1 - lambda), and s/(1 - lambda) = 1/s",
        sp.simplify(dsym - Dl ** 2 / (4 * Dl + k)) == 0 and sp.simplify(s / (1 - lv) - 1 / s) == 0
        and sp.simplify(lv * (2 / (1 - lv) + 4 * s / (1 - lv)) - k) == 0)
R.check("Delta_lambda = sqrt(1 - lambda) - (1 - lambda) > 0 on (0, 1)",
        all(math.sqrt(1 - l_) - (1 - l_) > 0 for l_ in np.linspace(1e-9, 1 - 1e-9, 10001)))


def least_eps(lam, ny=4001):
    """Least eps for which some (y, x, T21) satisfies the constraints used in Steps 1-4:
    2 eps >= |y| + |x - T21|/2, (s - y)^2 <= (s^2 + 2 eps)(1 - T21), sqrt(lambda x) >= Delta - y, 0 <= x <= lambda,
    T21 >= 0, y <= s (bisection on eps, dense grid on y; feasibility in x and T21 is explicit)."""
    s_ = math.sqrt(1 - lam)
    D = s_ - (1 - lam)

    def feasible(eps):
        ys = np.linspace(-2 * eps, min(2 * eps, s_), ny)
        T21max = 1 - (s_ - ys) ** 2 / (s_ ** 2 + 2 * eps)
        xmin = np.where(D - ys > 0, (D - ys) ** 2 / lam, 0.0)
        room = 2 * (2 * eps - np.abs(ys))                  # |x - T21| <= room
        okk = (T21max >= 0) & (xmin <= lam) & (xmin <= T21max + room) & (room >= 0)
        return bool(np.any(okk))

    lo, hi = 0.0, 1.0
    for _ in range(60):
        mid = (lo + hi) / 2
        lo, hi = (lo, mid) if feasible(mid) else (mid, hi)
    return hi


rat = []
for lam in np.concatenate([np.geomspace(1e-4, 0.5, 20), 1 - np.geomspace(1e-4, 0.5, 20)]):
    rat.append(least_eps(lam) / delta_lam(lam))
R.check("the least error compatible with Steps 1-2 and the Lemma is >= delta(lambda) (40 values of lambda)",
        min(rat) >= 1 - 1e-6, f"ratio least/delta in [{min(rat):.3f}, {max(rat):.3f}]")
R.check("delta(lambda) ~ lambda/32 as lambda -> 0 and ~ (1 - lambda)^2/2 as lambda -> 1",
        abs(delta_lam(1e-7) / (1e-7 / 32) - 1) < 1e-5 and abs(delta_lam(1 - 1e-7) / ((1e-7) ** 2 / 2) - 1) < 1e-2)


def phi_psi0(lam):
    psi0 = (np.eye(3)[0] + np.eye(3)[1]) / math.sqrt(2)
    return kraus_apply(channel(lam), dm(psi0))


min_ratio, n_ops = 1e9, 0
for trial in range(600):
    E1 = rng.uniform(0.1, 2)
    E2 = 2 * E1 if trial % 3 == 0 else E1 + rng.uniform(0.1, 2)
    lam = math.exp(-E2)
    if trial % 2 == 0:
        levels = [(a_ * E1 + b_ * E2, int(rng.integers(1, 3))) for a_ in range(3) for b_ in range(3) if rng.random() < 0.6] or [(0.0, 1)]
        _, _, _, theta = thermal_op(E1, E2, 1.0, levels, rng)
    else:
        U, levels = oscillator(E2, int(rng.integers(5, 60)), rng.uniform(0, 1))
        _, _, _, theta = thermal_op(E1, E2, 1.0, levels, rng, structured=U)
    psi0 = (np.eye(3)[0] + np.eye(3)[1]) / math.sqrt(2)
    dist = 0.5 * trace_norm(theta(dm(psi0)) - phi_psi0(lam))
    min_ratio = min(min_ratio, dist / delta_lam(lam))
    n_ops += 1
R.check("1/2||Theta(psi_0) - Phi(psi_0)||_1 >= delta(lambda) for 600 thermal operations", min_ratio >= 1,
        f"min distance/delta = {min_ratio:.2f}")

# ---------------------------------------------------------------------------------------------------- 6. crossover
def u2c2_sup(lam):
    u = lam / (2 + lam) ** 2                      # sup over E1 in (0, E2) of g1 g2 (attained as E1 -> 0)
    c = 2 + 6 * u / math.sqrt(1 - lam)
    return u * u / (2 * c * c)


ok_u = True
for lam in np.linspace(0.001, 0.999, 999):
    for x_ in np.linspace(lam, 1, 60)[1:-1]:      # x = e^{-beta E1}, lambda < x < 1
        g0 = 1 / (1 + x_ + lam)
        u = x_ * g0 * lam * g0
        ok_u &= u <= lam / (2 + lam) ** 2 + 1e-15
cross = None
for lam in np.linspace(0.9, 0.999, 9901):
    if u2c2_sup(lam) > delta_lam(lam):
        cross = lam
        break
below = all(delta_lam(l_) >= u2c2_sup(l_) for l_ in np.linspace(0.001, 0.97, 5000))
R.check("u^2/(2c^2) exceeds delta(lambda) only for lambda above about 0.97, for every E1 < E2",
        ok_u and below and cross is not None and 0.97 <= cross <= 0.98, f"crossover at lambda = {cross:.4f}")

# ---------------------------------------------------------------------------------------------------- 7. numbers
g = gibbs_pops(math.log(2), 2 * math.log(2))
val = g[1] * math.log2(1 / (1 - g[2]))
R.check("E2 = 2E1, beta E1 = ln 2: lambda = 1/4, Gibbs (4/7, 2/7, 1/7), T_rt >= (2/7) log2(7/6) = 0.064",
        np.allclose(g, [4 / 7, 2 / 7, 1 / 7]) and abs(val - 2 / 7 * math.log2(7 / 6)) < 1e-15 and round(val, 3) == 0.064,
        f"{val:.5f}")
R.check("delta(1/4) = 5.9e-3", round(delta_lam(0.25), 4) == 0.0059, f"{delta_lam(0.25):.5f}")
R.check("T_rt >= g1 log2 1/(1 - g2) > 0 for every gap ratio and temperature (grid)",
        all(gibbs_pops(b1, b2)[1] * math.log2(1 / (1 - gibbs_pops(b1, b2)[2])) > 0
            for b1 in np.linspace(0.01, 8, 40) for b2 in np.linspace(0.02, 9, 40) if b2 > b1))


# ---------------------------------------------------------------------------------------------------- 8. partial swaps
def partial_swap_distance(lam):
    """Distance of the K -> infinity oscillator family (cosine a') from Phi(psi_0), minimized over a'."""
    s_ = math.sqrt(1 - lam)

    def dist(ap):
        T20 = lam * (1 - ap * ap)
        c = 1 - lam + lam * ap
        Xm = np.zeros((3, 3))
        Xm[0, 0] = (1 - T20) / 2 - (1 - lam) / 2
        Xm[2, 2] = T20 / 2 - lam / 2
        Xm[0, 1] = Xm[1, 0] = (c - s_) / 2
        return 0.5 * trace_norm(Xm)
    grid = np.concatenate([np.linspace(0, 1, 2001), np.geomspace(1e-7, 1, 2001)])
    vals = [dist(ap) for ap in grid]
    a0 = grid[int(np.argmin(vals))]
    res = minimize_scalar(dist, bounds=(max(0.0, a0 / 2 - 1e-6), min(1.0, 2 * a0 + 1e-3)), method="bounded",
                          options={"xatol": 1e-14})
    return min(min(vals), res.fun)


low = [partial_swap_distance(l_) / l_ for l_ in (1e-4, 1e-3)]
high = [partial_swap_distance(1 - e_) / (e_ / 2) for e_ in (1e-3, 1e-4, 1e-6)]
R.check("partial swaps come within about 0.10 lambda at low temperature and (1 - lambda)/2 at high temperature "
        "(ratio (1 - sqrt(1 - lambda))^2 -> 1)",
        all(0.095 <= r_ <= 0.105 for r_ in low) and high[0] < high[1] < high[2] <= 1 and high[2] > 0.99,
        f"low: {low[0]:.4f} lambda; high, 1 - lambda = 1e-3, 1e-4, 1e-6: " + ", ".join(f"{r_:.4f}" for r_ in high))


def search(lam, E1, Kmax, rng, starts=3):
    """Minimize the single-input distance over thermal operations whose bath has the two ladders k E2 and k E2 + E1
    (k = 0..K, generic E1), so that levels 0, 1 and 2 all mix: the unitary is a free unitary in every total-energy
    block (2- and 3-dimensional blocks), parametrized by Hermitian generators."""
    E2 = -math.log(lam)
    HS = np.array([0.0, E1, E2])
    HB = np.array([k * E2 for k in range(Kmax + 1)] + [k * E2 + E1 for k in range(Kmax + 1)])
    dB = len(HB)
    tot = (HS[:, None] + HB[None, :]).reshape(-1)
    blocks, seen = [], np.zeros(len(tot), bool)
    for i in range(len(tot)):
        if not seen[i]:
            b = np.where(np.abs(tot - tot[i]) < 1e-9)[0]
            seen[b] = True
            if len(b) > 1:
                blocks.append(b)
    npar = sum(len(b) ** 2 for b in blocks)
    pB = np.exp(-HB)
    pB /= pB.sum()
    target = phi_psi0(lam)
    psi0 = (np.eye(3)[0] + np.eye(3)[1]) / math.sqrt(2)
    inp = np.kron(dm(psi0), np.diag(pB))

    def unitary(x):
        U = np.eye(3 * dB, dtype=complex)
        pos = 0
        for b in blocks:
            m = len(b)
            Hm = np.zeros((m, m), dtype=complex)
            iu = np.triu_indices(m, 1)
            Hm[np.diag_indices(m)] = x[pos:pos + m]
            nk = len(iu[0])
            Hm[iu] = x[pos + m:pos + m + nk] + 1j * x[pos + m + nk:pos + m + 2 * nk]
            Hm = Hm + np.triu(Hm, 1).conj().T
            w_, v_ = np.linalg.eigh(Hm)
            U[np.ix_(b, b)] = (v_ * np.exp(1j * w_)) @ v_.conj().T
            pos += m * m
        return U

    def obj(x):
        U = unitary(x)
        out = np.einsum("aibi->ab", (U @ inp @ U.conj().T).reshape(3, dB, 3, dB))
        return 0.5 * trace_norm(out - target)
    best = 1e9
    for _ in range(starts):
        r = minimize(obj, rng.standard_normal(npar), method="L-BFGS-B", options={"maxiter": 400})
        best = min(best, r.fun)
    return best


ok = True
details = []
for lam in (0.05, 0.25, 0.6):
    E1 = 0.41 * -math.log(lam)
    b = search(lam, E1, 6, rng)
    ps = partial_swap_distance(lam)
    details.append(f"lambda={lam}: search {b:.4f}, partial swaps {ps:.4f}, delta {delta_lam(lam):.4f}")
    ok &= b >= ps - 1e-4 and b >= delta_lam(lam)
R.check("a numerical search over thermal operations (two-ladder baths, all levels mixing) finds nothing closer than "
        "partial swaps", bool(ok), "; ".join(details))
R.close()
