"""The delay process and delayed channels (Sections 2 and 7, "The delay process", "Delayed channels", and the
paragraph "Clocks" of the Discussion).

Checks:
  1. the two-swap device with a ground-state memory implements the delay process, and for every tester its score is
     S(rho_I2) - (beta E/ln2) <1|rho_I2|1> (random adaptive testers);
  2. the largest score over testers (Frank-Wolfe with an SDP oracle, certified bracket) is log2(1 + e^{-beta E}),
     attained at the Gibbs second input; the two terms maximized separately give 1;
  3. the lower-bound tester (ground state first, purified Gibbs state second) forces exactly log2(1 + e^{-beta E}) on
     the device and on randomly scrambled exact extensions;
  4. the work per episode kT ln(1 + e^{-beta E}) equals the free energy needed to prepare a ground state;
  5. delayed channels: the device "swap in, apply a dilation of Phi, swap the second input in" has largest score
     kappa_beta(Phi) + log2 Z_H for Phi = Hadamard, X, a phase rotation, amplitude damping and the identity, and
     kappa_beta(Phi) alone with a Gibbs filler (zero for the thermal delay process); for unitaries
     kappa_beta = (beta/ln2) lambda_max(U^* H U - H), and for amplitude damping the formula of the companion paper;
  6. for the Hadamard gate lambda_max = E/sqrt2 exactly (sympy), so the work is E/sqrt2 + kT ln(1 + e^{-beta E});
  7. P_Phi commutes with the common time translation exactly when Phi is time-covariant (Hadamard and X do not);
  8. averaging each slot of the delay process over its own phase moves it by strategy distance 1/2, while the common
     phase leaves it unchanged; and a covariant process is at least half the largest translate distance away from a
     non-covariant one (Remark "Why covariance"), tested on the delayed Hadamard.
"""
import math

import numpy as np
import sympy as sp

from qtools import HAD, I2, X, Report, dm, embed, entropy, gibbs, h2, herm, ket, random_density, random_unitary, sqrtm_psd
from combs import (Realization, Tester, TesterLP, link, maximize_score, random_tester, simulate, strategy_distance,
                   translation_generator)

R = Report("Delay process and delayed channels")
rng = np.random.default_rng(42)
LN2 = math.log(2)
SW = np.eye(4)[[0, 2, 1, 3]].astype(complex)
lp = TesterLP([2, 2])


def delayed(U_cell, filler):
    """Bath = cell (x) env; contact 1 swaps the input into the cell; contact 2 applies U_cell on (cell, env), then
    swaps the second input in and releases the cell."""
    denv = U_cell.shape[0] // 2
    dims = [2, 2, denv]
    c1 = embed(SW, [0, 1], dims)
    c2 = embed(SW, [0, 1], dims) @ embed(U_cell, [1, 2], dims)
    tau = np.kron(filler, dm(ket((0,), [denv])))
    return Realization.collision([2, 2], tau, [c1, c2])


def ad_unitary(p):
    s, c = math.sqrt(p), math.sqrt(1 - p)
    U = np.eye(4, dtype=complex)
    U[np.ix_([2, 1], [2, 1])] = [[c, -s], [s, c]]        # |10> -> c|10> + s|01>, basis (cell, env)
    return U


# 1-2. the delay process ---------------------------------------------------------------------------------------------
wid = 0.0
brackets = []
for bE in (0.3, LN2, 1.0, 2.5):
    H = np.diag([0.0, bE]).astype(complex)
    dev = delayed(np.eye(2, dtype=complex), dm(ket((0,))))
    for _ in range(20):
        te = random_tester([2, 2], rng, 2)
        s = simulate(dev, te, [H, H])
        rI2 = s["rin"][1]
        wid = max(wid, abs(s["SZF"] + s["energy"] / LN2 - (entropy(rI2) - bE / LN2 * rI2[1, 1].real)))
    _, val, up = maximize_score(dev, [H, H], 1.0, lp, iters=40)
    brackets.append((val, up, math.log2(1 + math.exp(-bE))))
R.check("for every tester the two-swap device scores S(rho_I2) - (beta E/ln2) <1|rho_I2|1> (80 adaptive testers)",
        wid < 1e-12, f"{wid:.1e}")
R.check("the largest score over testers is log2(1 + e^{-beta E}) (certified Frank-Wolfe bracket)",
        all(abs(v - t) < 1e-8 and up > t - 1e-6 and up < t + 1e-6 for v, up, t in brackets),
        ", ".join(f"{v:.9f}/{t:.9f}" for v, _, t in brackets))
ok2 = True
for bE in (0.3, LN2, 1.0, 2.5):
    qs = np.linspace(0, 1, 100001)
    f = np.array([h2(q) for q in qs]) - bE / LN2 * qs
    ok2 &= abs(f.max() - math.log2(1 + math.exp(-bE))) < 1e-9 and abs(qs[f.argmax()] - 1 / (1 + math.exp(bE))) < 2e-5
    ok2 &= max(h2(q) for q in qs[::1000]) == 1.0 and math.log2(1 + math.exp(-bE)) < 1
R.check("the maximum is attained at the Gibbs second input; the two terms maximized separately give 1 > log2(1+e^{-bE})",
        ok2)

# 3. the lower-bound tester on scrambled exact extensions -------------------------------------------------------------
def lower_tester(bE):
    """Slot 1: the ground state; slot 2: a purified Gibbs state.  T_1 is trivial; T_2 = (copy of O_1, purifier)."""
    g = gibbs(np.diag([0.0, bE]), 1.0)
    psi = np.array([[1.0], [0.0]], dtype=complex)        # (I_1, T_1) with dim T_1 = 1
    sq = sqrtm_psd(g)
    L = np.zeros((2 * 4, 2), dtype=complex)              # (O_1) -> (I_2, T_2 = (O_1 copy, r))
    for o in range(2):
        for i in range(2):
            for r in range(2):
                L[i * 4 + o * 2 + r, o] = sq[i, r]
    return Tester([2, 2], psi, [L], [1, 4])


wl = 0.0
for bE in (0.3, 1.0, 2.5):
    H = np.diag([0.0, bE]).astype(complex)
    te = lower_tester(bE)
    target = math.log2(1 + math.exp(-bE))
    for k in range(8):
        if k == 0:
            dev = delayed(np.eye(2, dtype=complex), dm(ket((0,))))
        else:
            # exact extension with junk: bath (cell, J), tau_J mixed; contact 2 entangles the stored second input with J
            dJ = 2
            dims = [2, 2, dJ]
            tauJ = random_density(dJ, rng)
            c1 = embed(SW, [0, 1], dims) @ embed(random_unitary(dJ, rng), [2], dims)
            c2 = embed(random_unitary(2 * dJ, rng), [1, 2], dims) @ embed(SW, [0, 1], dims)
            dev = Realization.collision([2, 2], np.kron(dm(ket((0,))), tauJ), [c1, c2])
        s = simulate(dev, te, [H, H])
        wl = max(wl, abs(s["SZF"] + s["energy"] / LN2 - target))
R.check("ground state first, purified Gibbs state second forces log2(1 + e^{-beta E}) on every exact extension tried",
        wl < 1e-12, f"{wl:.1e} over 24 extensions")

# 4. work and free energy ------------------------------------------------------------------------------------------------
ok4 = True
for bE in (0.3, 1.0, 2.5):
    F_ground, F_gibbs = 0.0, -math.log(1 + math.exp(-bE))          # beta F
    ok4 &= abs((F_ground - F_gibbs) - LN2 * math.log2(1 + math.exp(-bE))) < 1e-15
R.check("kT ln2 log2(1 + e^{-beta E}) = kT ln(1 + e^{-beta E}) = F(ground) - F(Gibbs)", ok4)

# 5. delayed channels ----------------------------------------------------------------------------------------------------
def kappa_unitary(U, H, beta):
    return beta / LN2 * np.linalg.eigvalsh(herm(U.conj().T @ H @ U - H)).max()


def kappa_ad(p, bE):
    """kappa_beta of amplitude damping: max_{0 <= y <= p} [h(y) - beta Delta y/ln2] (companion paper, the theorem on classical channels and partial reset, part (b))."""
    ys = np.linspace(0, p, 200001)
    return float(np.max(np.array([h2(y) for y in ys]) - bE / LN2 * ys))


rows = []
ok5 = True
th = 0.4
PH = np.diag([np.exp(-1j * th), np.exp(1j * th)])
for bE in (0.5, 1.0, 2.0):
    H = np.diag([0.0, bE]).astype(complex)
    logZ = math.log2(1 + math.exp(-bE))
    cases = [("Hadamard", HAD, kappa_unitary(HAD, H, 1.0)),
             ("X", X, kappa_unitary(X, H, 1.0)),
             ("phase", PH, 0.0),
             ("identity", I2, 0.0),
             ("amplitude damping 0.6", ad_unitary(0.6), kappa_ad(0.6, bE))]
    for name, U, kap in cases:
        for filler, extra in ((dm(ket((0,))), logZ), (gibbs(H, 1.0), 0.0)):
            dev = delayed(U, filler)
            _, val, up = maximize_score(dev, [H, H], 1.0, lp, iters=80)
            good = abs(val - (kap + extra)) < 2e-6 and up < kap + extra + 2e-6
            ok5 &= good
            rows.append(f"{name}{'' if extra else ' (Gibbs filler)'} bE={bE}: {val:.7f} vs {kap + extra:.7f}")
            if not good:
                print("    mismatch:", rows[-1], up)
R.check("delayed channels: largest score = kappa_beta(Phi) + log2 Z_H (ground filler) and kappa_beta(Phi) (Gibbs filler) "
        "for Hadamard, X, phase, identity, amplitude damping", ok5, f"{len(rows)} cases")

# 6. the Hadamard numbers ------------------------------------------------------------------------------------------------
E = sp.symbols("E", positive=True)
Hs = sp.diag(0, E)
Hd = sp.Matrix([[1, 1], [1, -1]]) / sp.sqrt(2)
ev = (Hd.T * Hs * Hd - Hs).eigenvals()
R.check("for the Hadamard gate, U^* H U - H has eigenvalues +-E/sqrt2, so the work is E/sqrt2 + kT ln(1+e^{-beta E})",
        set(sp.simplify(k) for k in ev) == {E / sp.sqrt(2), -E / sp.sqrt(2)})

# 7. covariance of P_Phi -------------------------------------------------------------------------------------------------
H = np.diag([0.0, 1.0]).astype(complex)
G = translation_generator([2, 2], [H, H])
cov = {}
for name, U in (("Hadamard", HAD), ("X", X), ("phase", PH), ("identity", I2), ("amplitude damping", ad_unitary(0.6))):
    Rch = delayed(U, dm(ket((0,)))).R
    cov[name] = np.abs(Rch @ G - G @ Rch).max()
R.check("P_Phi commutes with the common translation for phase, identity and amplitude damping, not for Hadamard or X",
        cov["phase"] < 1e-12 and cov["identity"] < 1e-12 and cov["amplitude damping"] < 1e-12
        and cov["Hadamard"] > 0.1 and cov["X"] > 0.1)

# 8. separate phases and Remark "Why covariance" ----------------------------------------------------------------------------------------
def translate(Rch, us, H):
    D = [np.diag(np.exp(-1j * u * np.diag(H))) for u in us]
    T = np.kron(np.kron(D[0].conj(), D[0]), np.kron(D[1].conj(), D[1]))
    return T @ Rch @ T.conj().T


grid = 2 * np.pi * np.arange(8) / 8
delay = delayed(I2, dm(ket((0,)))).R
sep = sum(translate(delay, (u1, u2), H) for u1 in grid for u2 in grid) / 64
com = sum(translate(delay, (u, u), H) for u in grid) / 8
d_sep = strategy_distance(delay, sep, [2, 2])
d_com = strategy_distance(delay, com, [2, 2])
R.check("averaging each slot over its own phase moves the delay process by 1/2; the common phase leaves it unchanged",
        abs(d_sep - 0.5) < 1e-6 and abs(d_com) < 1e-6, f"{d_sep:.7f}, {d_com:.1e}")
Pnc = delayed(HAD, dm(ket((0,)))).R
far = max(strategy_distance(Pnc, translate(Pnc, (u, u), H), [2, 2]) for u in grid)
covs = [sum(translate(Pnc, (u, u), H) for u in grid) / 8]
for _ in range(3):   # other covariant processes: twirls of random processes
    rr = Realization.collision([2, 2], random_density(2, rng), [random_unitary(4, rng) for _ in range(2)]).R
    covs.append(sum(translate(rr, (u, u), H) for u in grid) / 8)
dists = [strategy_distance(Pnc, Pc, [2, 2]) for Pc in covs]
R.check("every covariant process tried is at least half the largest translate distance from the delayed Hadamard",
        min(dists) >= far / 2 - 1e-6, f"largest translate distance {far:.4f}; distances {', '.join(f'{x:.4f}' for x in dists)}")
R.close()
