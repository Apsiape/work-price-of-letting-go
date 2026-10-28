"""Setting, testers and port bounds (Sections 2-3 and Appendix A).

Checks:
  1. two independent engines agree: direct simulation of adaptive testers with quantum memory against random collisions
     reproduces the link-product formulas, the observer's state nu_ZF = sqrt(x) R^F sqrt(x) (eq. (testerstate)), and
     S(Z|F) = S(omega_t) - S(tau) (Appendix A, "Collisions");
  2. the rare-branch record of EPR halves is the tester record and satisfies (E5); conversely every positive chain,
     including extreme points returned by SDPs, is realized by a tester (Appendix E, after (E5));
  3. random processes satisfy the causal constraints (eq. (causal)); Tr t = d and x <= d I;
  4. Lemma "Covariant realization" on random covariant combs, including rank-deficient ones: the minimal
     realization is a chain of isometries that reproduces the process and conserves energy for the stated memory
     Hamiltonians; on a non-covariant comb the energy check fails;
  5. the delay process commutes with the common time translation and not with separate ones (eq. (cov));
  6. the port bounds: omega_t <= d^2 omega_0 (eq. (domination)), sharp constant c d attained; the strategy distance
     bound (eq. (choidistance)) via an SDP; the score bound 2 log2 d + (beta/ln2) sum span(H_j), attained in its
     entropy part (Proposition "Basic properties" (c), Appendix A, (E1));
  7. the minimax ingredients: the score is concave in the tester, and flagged mixtures of extensions score exactly
     the mixture (Lemma "Minimax");
  8. causal accumulation: each episode adds S(Z|F) to the device entropy, also when the device is correlated with
     earlier outputs (Lemma 'Causal accumulation');
  9. the accounting identity (eq. (accounting)) and its Appendix E form (E3) on random energy-conserving devices;
 10. Proposition "Basic properties" (b): a product of one-use collisions scores at most the sum of one-use scores at the average inputs,
     with equality for product testers;
 11. the ports example: switching a thermal qubit to a maximally mixed zero-H qubit yields beta^{-1} ln(2/(1+e^{-beta E})).
"""
import math

import numpy as np

from qtools import (Report, dm, embed, entropy, entropy_nat, gibbs, herm, ket, near_unitary, ptrace, random_density,
                    random_energy_conserving_unitary, random_unitary, relent, sqrtm_psd)
from combs import (Realization, TesterLP, block_isometry, causal_defect, flat_record, link, minimal_realization, nu_ZF,
                   omega_map, random_tester, realize_record, record_prefixes, simulate, strategy_distance,
                   translation_generator)

R = Report("Setting, testers and port bounds")
rng = np.random.default_rng(20261009)
LN2 = math.log(2)


def rand_herm(d):
    a = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    return herm(a)


# 1. two engines -----------------------------------------------------------------------------------------------
worst = dict(omega=0.0, ports=0.0, energy=0.0, SZF=0.0, nu=0.0)
count = 0
for dims in ([2, 2], [2, 3], [3, 2], [2, 2, 2]):
    for _ in range(6):
        dB = int(rng.integers(2, 4))
        real = Realization.collision(dims, random_density(dB, rng, rank=int(rng.integers(1, dB + 1))),
                                     [random_unitary(d * dB, rng) for d in dims])
        H = [rand_herm(d) for d in dims]
        for _ in range(3):
            te = random_tester(dims, rng, int(rng.integers(1, 4)))
            s, l = simulate(real, te, H), link(real, te.record(), H)
            worst["omega"] = max(worst["omega"], np.abs(s["omega"] - l["omega"]).max())
            worst["ports"] = max(worst["ports"], max(np.abs(a - b).max() for a, b in zip(s["rin"] + s["rout"], l["rin"] + l["rout"])))
            worst["energy"] = max(worst["energy"], abs(s["energy"] - l["energy"]))
            worst["SZF"] = max(worst["SZF"], abs(s["SZF"] - (entropy(l["omega"]) - real.S_tau())))
            nu = nu_ZF(real, te.record())
            dZ = nu.shape[0] // real.dF
            worst["nu"] = max(worst["nu"], abs(entropy(nu) - entropy(ptrace(nu, [dZ, real.dF], [1])) - s["SZF"]))
            count += 1
R.check(f"simulation of {count} adaptive testers with quantum memory = link products (bath, ports, energy)",
        max(worst["omega"], worst["ports"], worst["energy"]) < 1e-12,
        f"{worst['omega']:.1e}, {worst['ports']:.1e}, {worst['energy']:.1e}")
R.check("S(Z|F) from the simulation = S(omega_t) - S(tau) = S(Z|F) of nu_ZF = sqrt(x) R^F sqrt(x), x = t^T",
        max(worst["SZF"], worst["nu"]) < 1e-10, f"{worst['SZF']:.1e}, {worst['nu']:.1e}")

# 2. records -------------------------------------------------------------------------------------------------------
w_epr = w_chain = w_conv = 0.0
for dims in ([2, 2], [2, 3, 2], [3, 2], [2, 2, 2]):
    c = int(np.prod(dims[:-1]))
    for _ in range(8):
        te = random_tester(dims, rng, int(rng.integers(1, 4)))
        Zn = te.record()
        w_epr = max(w_epr, np.abs(te.record_by_epr() - Zn).max())
        Zs = record_prefixes(Zn, dims)
        w_chain = max(w_chain, abs(np.trace(Zs[0]) - 1), abs(np.trace(Zn) - c), -min(np.linalg.eigvalsh(Zk).min() for Zk in Zs))
        for k in range(1, len(dims)):                 # Tr_{I_k} Z_k = Z_{k-1} (x) I_{O_{k-1}}
            pre = Zs[k - 1].shape[0]
            t = Zs[k].reshape(pre * dims[k - 1], dims[k], pre * dims[k - 1], dims[k])
            w_chain = max(w_chain, np.abs(np.einsum("aibi->ab", t) - np.kron(Zs[k - 1], np.eye(dims[k - 1]))).max())
        w_conv = max(w_conv, np.abs(realize_record(Zn, dims).record() - Zn).max())
R.check("the physical record of inputs and EPR partners is Z_n, with Z_n >= 0, Tr_{I_j} Z_j = I (x) Z_{j-1}, "
        "Tr Z_1 = 1, Tr Z_l = c (E5)", w_epr < 1e-12 and w_chain < 1e-12, f"{w_epr:.1e}, {w_chain:.1e}")
lp22 = TesterLP([2, 2])
for _ in range(10):
    Zx, _ = lp22.solve(rand_herm(8))
    w_conv = max(w_conv, np.abs(realize_record(Zx, [2, 2]).record() - Zx).max())
R.check("every positive chain (random records and 10 SDP extreme points) is realized by a tester with that record",
        w_conv < 1e-6, f"{w_conv:.1e}")

# 3. causal constraints, Tr t = d, x <= d I ------------------------------------------------------------------------
wc, wt = 0.0, 0.0
for dims in ([2, 2], [2, 3], [2, 2, 2], [3, 2]):
    for _ in range(5):
        dB = int(rng.integers(1, 4))
        real = Realization.collision(dims, random_density(dB, rng), [random_unitary(d * dB, rng) for d in dims])
        wc = max(wc, causal_defect(real.R, dims))
        Zn = random_tester(dims, rng).record()
        t = np.kron(Zn, np.eye(dims[-1]))
        d = int(np.prod(dims))
        wt = max(wt, abs(np.trace(t) - d), np.linalg.eigvalsh(t).max() - d)
R.check("random processes satisfy Tr_{O_j} R^(j) = I_{I_j} (x) R^(j-1) (eq. (causal))", wc < 1e-12, f"{wc:.1e}")
R.check("tester operators have Tr t = d and x <= d I", wt < 1e-10)

# 4. Covariant realization -------------------------------------------------------------------------------------------------------
def covariant_comb(spec):
    """spec: list of (port energies, memory energies after the slot)."""
    dims = [len(pe) for pe, _ in spec]
    mem_e = [np.array([0.0])]
    isos = []
    for pe, me in spec:
        ein = (np.asarray(pe)[:, None] + mem_e[-1][None, :]).reshape(-1)        # (I_j, M_{j-1})
        eout = (np.asarray(pe)[:, None] + np.asarray(me, float)[None, :]).reshape(-1)
        isos.append(block_isometry(ein, eout, rng))
        mem_e.append(np.asarray(me, float))
    init = np.ones(1)
    return dims, Realization(dims, init, isos, [len(m) for m in mem_e], 1), [np.diag(np.asarray(pe, float)).astype(complex) for pe, _ in spec]


def lemma2_defects(dims, Rch, H):
    Vs, pref = minimal_realization(Rch, dims)
    iso = rep = en = inv = 0.0
    HA_prev = np.zeros((1, 1))
    for j, (V, d) in enumerate(zip(Vs, dims), start=1):
        Rb0 = pref[j - 1].conj()
        w, v = np.linalg.eigh(herm(Rb0))
        Pi = (v[:, w > 1e-10]) @ v[:, w > 1e-10].conj().T
        Pin = np.kron(np.eye(d), Pi)
        iso = max(iso, np.abs(V.conj().T @ V - Pin).max())
        full = [x for dd in dims[:j] for x in (dd, dd)]
        HA = sum(embed(H[l], [2 * l], full) - embed(H[l].T, [2 * l + 1], full) for l in range(j))
        lhs = (np.kron(H[j - 1], np.eye(HA.shape[0])) + np.kron(np.eye(d), HA)) @ V @ Pin
        rhs = V @ (np.kron(H[j - 1], np.eye(HA_prev.shape[0])) + np.kron(np.eye(d), HA_prev)) @ Pin
        en = max(en, np.abs(lhs - rhs).max())
        inv = max(inv, np.abs(pref[j].conj() @ HA - HA @ pref[j].conj()).max())
        HA_prev = HA
    mems = [1] + [V.shape[0] // d for V, d in zip(Vs, dims)]
    rebuilt = Realization(dims, np.ones(1), Vs, mems, 1).R
    rep = np.abs(rebuilt - Rch).max()
    return iso, rep, en, inv


specs = [
    [([0, 1], [0, 1, -1]), ([0, 1], [0, 1, -1, 2, -2])],                       # final memory 5 < 16: rank deficient
    [([0, 1], [0, 0, 1, -1]), ([0, 1], [-2, -1, -1, 0, 0, 0, 1, 1, 2])],
    [([0, 1, 2], [0, 1, -1, 2, -2]), ([0, 1], [0, 1, -1, 2, -2, 3, -3])],
    [([0, 2], [0, 2, -2]), ([0, 1], [0, 1, -1, 2, -2, 3]), ([0, 1], list(range(-4, 5)))],
]
worst4 = [0.0] * 4
ranks = []
for spec in specs:
    for _ in range(3):
        dims, real, H = covariant_comb(spec)
        Rch = real.R
        G = translation_generator(dims, H)
        assert np.abs(Rch @ G - G @ Rch).max() < 1e-10
        ranks.append((np.linalg.matrix_rank(Rch, tol=1e-9), Rch.shape[0]))
        worst4 = [max(a, b) for a, b in zip(worst4, lemma2_defects(dims, Rch, H))]
deficient = sum(r < n for r, n in ranks)
R.check("Covariant realization: the minimal realization V_j consists of isometries on I_j (x) supp and reproduces the process",
        worst4[0] < 1e-8 and worst4[1] < 1e-8, f"{worst4[0]:.1e}, {worst4[1]:.1e}; {deficient} of {len(ranks)} "
        f"Choi operators rank deficient")
R.check("Covariant realization: each V_j conserves energy when A_j carries sum_{l<=j} (H_l on I_l' - H_l^T on O_l'), and the supports "
        "are invariant", worst4[2] < 1e-8 and worst4[3] < 1e-8 and deficient >= 3, f"{worst4[2]:.1e}, {worst4[3]:.1e}")
dims, real, H = covariant_comb(specs[0])
noncov = Realization(dims, np.ones(1), [random_unitary(r.shape[0], rng)[:, :r.shape[1]] for r in real.isos],
                     real.mem, 1)
R.check("on a comb without covariance the same energy check fails (the check is not vacuous)",
        lemma2_defects(dims, noncov.R, H)[2] > 1e-2)

# 5. common versus separate covariance of the delay process -------------------------------------------------------
SW = np.eye(4)[[0, 2, 1, 3]].astype(complex)
delay = Realization.collision([2, 2], dm(ket((0,))), [SW, SW])
Hq = [np.diag([0.0, 1.0]).astype(complex)] * 2
Gc = translation_generator([2, 2], Hq)
G1 = translation_generator([2, 2], Hq, slots=[0])
R.check("the delay process commutes with the common translation and not with the translation of slot 1 alone",
        np.abs(delay.R @ Gc - Gc @ delay.R).max() < 1e-12 and np.abs(delay.R @ G1 - G1 @ delay.R).max() > 0.1)

# 6. port bounds ---------------------------------------------------------------------------------------------------
def domination_ratio(real, Zn):
    om, _ = omega_map(real)
    w0 = om(flat_record(real.dims))
    wv, vv = np.linalg.eigh(herm(w0))
    keep = wv > 1e-12
    S = vv[:, keep] / np.sqrt(wv[keep])
    wt = om(Zn)
    leak = np.linalg.norm(wt - vv[:, keep] @ vv[:, keep].conj().T @ wt @ vv[:, keep] @ vv[:, keep].conj().T)
    return np.linalg.eigvalsh(herm(S.conj().T @ wt @ S)).max(), leak


ratios = []
for dims in ([2, 2], [2, 3], [2, 2, 2]):
    d, c = int(np.prod(dims)), int(np.prod(dims[:-1]))
    for _ in range(6):
        dB = int(rng.integers(2, 5))
        real = Realization.collision(dims, random_density(dB, rng), [random_unitary(dd * dB, rng) for dd in dims])
        for _ in range(4):
            rr, leak = domination_ratio(real, random_tester(dims, rng).record())
            ratios.append((rr / (c * d), rr / d ** 2, leak))
# the recording collision: store each input, emit half of an EPR pair, keep its partner
phi = np.eye(2).reshape(-1) / math.sqrt(2)
tau_rec = dm(np.kron(np.kron(ket((0,)), phi), ket((0,))))                    # (A_1, E_1, R_1, A_2)
dimsB = [2, 2, 2, 2, 2]                                                         # (port, A_1, E_1, R_1, A_2)
U1 = embed(SW, [0, 2], dimsB) @ embed(SW, [0, 1], dimsB)                        # I_1 -> A_1, then port <-> E_1
U2 = embed(SW, [0, 4], dimsB)
recorder = Realization.collision([2, 2], tau_rec, [U1, U2])
psi = np.kron(ket((0,)), ket((0,)))                                              # I_1 = |0>, trivial memory
Lid = np.eye(4, dtype=complex)                                                   # I_2 := O_1 (memory kept)
from combs import Tester
best = Tester([2, 2], psi.reshape(2, 2), [Lid], [2, 2])
rr_rec, _ = domination_ratio(recorder, best.record())
R.check("omega_t <= d^2 omega_0 for every tester (eq. (domination)); in fact omega_t <= c d omega_0",
        max(r[1] for r in ratios) <= 1 + 1e-9 and max(r[0] for r in ratios) <= 1 + 1e-9 and max(r[2] for r in ratios) < 1e-9,
        f"{len(ratios)} random cases, largest ratio to c d: {max(r[0] for r in ratios):.3f}")
R.check("the sharp constant c d = 8 is attained by a collision that records the inputs and emits EPR halves",
        abs(rr_rec - 8) < 1e-9, f"ratio {rr_rec:.6f}; the stated d^2 = 16 is valid but not tight")

worst_cd, worst_sharp = 0.0, 0.0
for dims in ([2], [2, 2]):
    d, c = int(np.prod(dims)), int(np.prod(dims[:-1]))
    for _ in range(12):
        dB = int(rng.integers(1, 3))
        U = [random_unitary(dd * dB, rng) for dd in dims]
        tau = random_density(dB, rng)
        r1 = Realization.collision(dims, tau, U).R
        eps = rng.choice([0.05, 0.2, 0.6])
        r2 = Realization.collision(dims, tau, [near_unitary(u, eps, rng) for u in U]).R
        dc = strategy_distance(r1, r2, dims)
        tn = float(np.sum(np.abs(np.linalg.eigvalsh(herm(r1 - r2)))))
        worst_cd = max(worst_cd, dc / (d * d * 0.5 * tn / d))
        worst_sharp = max(worst_sharp, dc / (0.5 * min(c, d // dims[0]) * tn))
# a one-slot family attaining the sharp constant: measure-and-prepare channels differing on one outcome
s0, s1 = random_density(2, rng), random_density(2, rng)
Rmp = np.kron(dm(ket((0,))), s0) + np.kron(dm(ket((1,))), s1)
Rmp2 = np.kron(dm(ket((0,))), s1) + np.kron(dm(ket((1,))), s1)
dmp = strategy_distance(Rmp, Rmp2, [2])
tight = dmp / (0.5 * float(np.sum(np.abs(np.linalg.eigvalsh(Rmp - Rmp2)))))
R.check("strategy distance (SDP) <= d^2 (1/2)||J - J'||_1 (eq. (choidistance)), and <= (min(c, d/d_1)/2)||R - R'||_1",
        worst_cd <= 1 + 1e-6 and worst_sharp <= 1 + 1e-6 and abs(tight - 1) < 1e-6,
        f"largest ratios {worst_cd:.3f} (stated), {worst_sharp:.3f} (sharp); sharp constant attained: {tight:.6f}")

# score bound
beta = 1.0
wscore = 0.0
for dims in ([2, 2], [2, 3], [2, 2, 2]):
    d = int(np.prod(dims))
    for _ in range(6):
        dB = int(rng.integers(1, 4))
        real = Realization.collision(dims, random_density(dB, rng), [random_unitary(dd * dB, rng) for dd in dims])
        H = [rand_herm(dd) for dd in dims]
        bound = 2 * math.log2(d) + beta / LN2 * sum(np.ptp(np.linalg.eigvalsh(h)) for h in H)
        for _ in range(4):
            s = simulate(real, random_tester(dims, rng), H)
            wscore = max(wscore, abs(s["SZF"] + beta / LN2 * s["energy"]) / bound)
# entropy part attained: store every input and emit half of an EPR pair at every slot (tau pure)
tau3 = dm(np.kron(np.kron(ket((0,)), phi), np.kron(ket((0,)), phi)))          # (A_1, E_1, R_1, A_2, E_2, R_2)
dimsC = [2] * 7
V1 = embed(SW, [0, 2], dimsC) @ embed(SW, [0, 1], dimsC)
V2 = embed(SW, [0, 5], dimsC) @ embed(SW, [0, 4], dimsC)
rec2 = Realization.collision([2, 2], tau3, [V1, V2])
s_flat = entropy(omega_map(rec2)[0](flat_record([2, 2]))) - rec2.S_tau()
R.check("|S(Z|F) + e_beta| <= 2 log2 d + (beta/ln2) sum_j span(H_j) (Prop. 'Basic properties' (c), App. A, (E1)); the entropy part "
        "2 log2 d is attained", wscore <= 1 + 1e-12 and abs(s_flat - 2 * math.log2(4)) < 1e-12,
        f"largest ratio {wscore:.3f}; S(Z|F) = {s_flat:.6f} for the flat tester against the recorder")

# 7. minimax ingredients ------------------------------------------------------------------------------------------
dims = [2, 2]
H = [np.diag([0.0, 0.8]).astype(complex), np.diag([0.0, 1.3]).astype(complex)]
gaps, near = [], 0
for _ in range(8):
    dB = int(rng.integers(2, 4))
    real = Realization.collision(dims, random_density(dB, rng), [random_unitary(2 * dB, rng) for _ in dims])
    om, _ = omega_map(real)
    def score(Z):
        return entropy(om(Z)) - real.S_tau() + beta / LN2 * link(real, Z, H)["energy"]
    for _ in range(15):
        Z1 = random_tester(dims, rng).record()
        lam = rng.choice([1e-3, 1e-2, 0.3, 1.0])
        Z2 = (1 - lam) * Z1 + lam * random_tester(dims, rng).record()
        g = score((Z1 + Z2) / 2) - (score(Z1) + score(Z2)) / 2
        gaps.append(g)
        near += g < 1e-5
R.check("the score is concave in the tester: midpoint gap >= 0 on 120 pairs", min(gaps) > -1e-12 and near >= 30,
        f"smallest gap {min(gaps):.2e}, {near} pairs within 1e-5 of equality")
# flagged mixture of two extensions
dB = 2
taus = [random_density(dB, rng), random_density(dB, rng)]
Us = [[random_unitary(2 * dB, rng) for _ in dims] for _ in range(2)]
pf = 0.37
tau_mix = np.kron(np.diag([pf, 1 - pf]), np.zeros((dB, dB)))
tau_mix = np.kron(dm(ket((0,))), pf * taus[0]) + np.kron(dm(ket((1,))), (1 - pf) * taus[1])
Umix = []
for j in range(2):
    U = np.zeros((2 * 2 * dB, 2 * 2 * dB), dtype=complex)                       # order (port, flag, B)
    for f in range(2):
        Pf = dm(ket((f,)))
        U += embed(np.kron(Pf, np.eye(1)), [1], [2, 2, dB]) @ embed(Us[f][j], [0, 2], [2, 2, dB])
    Umix.append(U)
mix = Realization.collision(dims, tau_mix, Umix)
parts = [Realization.collision(dims, taus[f], Us[f]) for f in range(2)]
wf = 0.0
for _ in range(10):
    te = random_tester(dims, rng)
    sm, s0_, s1_ = (simulate(x, te, H) for x in (mix, parts[0], parts[1]))
    val = lambda s: s["SZF"] + beta / LN2 * s["energy"]
    wf = max(wf, abs(val(sm) - pf * val(s0_) - (1 - pf) * val(s1_)))
wproc = np.abs(mix.R - pf * parts[0].R - (1 - pf) * parts[1].R).max()
R.check("a flagged mixture of extensions implements the mixture and scores exactly the mixture (flag entropy cancels)",
        wf < 1e-10 and wproc < 1e-12, f"{wf:.1e}, {wproc:.1e}")

# 8. causal accumulation ------------------------------------------------------------------------------------------
wacc = 0.0
for _ in range(10):
    dD = int(rng.integers(2, 4))
    rhoD = random_density(dD, rng)
    init = sqrtm_psd(rhoD).reshape(-1)                                       # (D, F_0)
    dF = dD
    U = [random_unitary(2 * dD, rng) for _ in dims]
    for episode in range(2):
        real = Realization(dims, init, U, [dD] * 3, dF)
        te = random_tester(dims, rng, 2)
        s = simulate(real, te, H)
        st = s["state"]                                                       # (O_2, T_2, D, F)
        sh = st.shape
        full = st.reshape(sh[0] * sh[1], sh[2], sh[3])
        rho_ZF = np.einsum("zdf,ydg->zfyg", full, full.conj()).reshape(sh[0] * sh[1] * sh[3], -1)
        rho_F = np.einsum("zdf,zdg->fg", full, full.conj())
        D_before = entropy(np.einsum("df,ef->de", init.reshape(dD, dF), init.reshape(dD, dF).conj()))
        wacc = max(wacc, abs(entropy(s["omega"]) - D_before - (entropy(rho_ZF) - entropy(rho_F))))
        # next episode: the device is correlated with the released outputs and references, now part of F
        init = full.transpose(1, 0, 2).reshape(dD, -1).reshape(-1)
        dF = sh[0] * sh[1] * sh[3]
R.check("each episode raises S(D) by exactly S(Z|F), with F holding all earlier outputs and references (Lemma 'Causal accumulation')",
        wacc < 1e-10, f"{wacc:.1e}")

# 9. accounting identities ----------------------------------------------------------------------------------------
wid = wid3 = 0.0
for _ in range(40):
    bt = rng.uniform(0.3, 2.0)
    eC, eB, eR, eS = (rng.integers(0, 3, 2), rng.integers(0, 4, 3), rng.integers(0, 3, 4), rng.integers(0, 2, 2))
    dimsA = [2, 3, 4, 2, 2]                                                 # C, B, R, S, reference
    Etot = (eC[:, None, None, None] + eB[None, :, None, None] + eR[None, None, :, None] + eS[None, None, None, :]).reshape(-1)
    U = np.kron(random_energy_conserving_unitary(Etot, rng), np.eye(2))
    HC, HB, HR, HS = (np.diag(e).astype(complex) for e in (eC, eB, eR, eS))
    gR = gibbs(HR, bt)
    rC, rB = random_density(2, rng), random_density(3, rng)
    psiS = rng.standard_normal(4) + 1j * rng.standard_normal(4)
    rho0 = np.kron(np.kron(np.kron(rC, rB), gR), dm(psiS / np.linalg.norm(psiS)))
    rho1 = U @ rho0 @ U.conj().T
    m = lambda rho, k: ptrace(rho, dimsA, k)
    E = lambda Hh, rho: float(np.trace(Hh @ rho).real)
    dEC, dEB = E(HC, m(rho1, [0])) - E(HC, m(rho0, [0])), E(HB, m(rho1, [1])) - E(HB, m(rho0, [1]))
    dES = E(HS, m(rho1, [3])) - E(HS, m(rho0, [3]))
    dSC, dSB = entropy(m(rho1, [0])) - entropy(m(rho0, [0])), entropy(m(rho1, [1])) - entropy(m(rho0, [1]))
    w = bt / LN2 * (-(dEC + dEB)) + dSC + dSB
    A = entropy(m(rho1, [0, 1, 2])) - entropy(m(rho0, [0, 1, 2]))
    Ifin = entropy(m(rho1, [0])) + entropy(m(rho1, [1])) + entropy(m(rho1, [2])) - entropy(m(rho1, [0, 1, 2]))
    rhs = A + bt / LN2 * dES + relent(m(rho1, [2]), gR) + Ifin
    wid = max(wid, abs(w - rhs))
    # (E3) in nats with a pure energy-eigenstate battery
    rBp = dm(ket((int(rng.integers(0, 3)),), [3]))
    rho0 = np.kron(np.kron(np.kron(rC, rBp), gR), dm(psiS / np.linalg.norm(psiS)))
    rho1 = U @ rho0 @ U.conj().T
    Wmean = -(E(HB, m(rho1, [1])) - E(HB, m(rho0, [1])))
    dFC = (E(HC, m(rho1, [0])) - E(HC, m(rho0, [0]))) - (entropy_nat(m(rho1, [0])) - entropy_nat(m(rho0, [0]))) / bt
    lhs = Wmean - dFC + entropy_nat(m(rho1, [1])) / bt
    dSD = entropy_nat(m(rho1, [0, 1, 2])) - entropy_nat(m(rho0, [0, 1, 2]))
    I3 = (entropy_nat(m(rho1, [0])) + entropy_nat(m(rho1, [1])) + entropy_nat(m(rho1, [2]))
          - entropy_nat(m(rho1, [0, 1, 2])))
    rhs3 = dSD / bt + (E(HS, m(rho1, [3])) - E(HS, m(rho0, [3]))) + (relent(m(rho1, [2]), gR, math.e) + I3) / bt
    wid3 = max(wid3, abs(lhs - rhs3))
R.check("accounting identity w = A + (beta/ln2) dE_sys + D(R_fin||gamma_R) + I(C:B:R)_fin (eq. (accounting)), "
        "40 random energy-conserving devices", wid < 1e-9, f"{wid:.1e}")
R.check("(E3): W_mean - dF(C) + S(W_f)/beta = dS_D/beta + dE_pay + [D(G||gamma_G) + I(C:W:G)]/beta", wid3 < 1e-9,
        f"{wid3:.1e}")

# 10. Proposition "Basic properties" (b): product of one-use collisions ------------------------------------------------------------
dB = 2
Hc = np.diag([0.0, 1.1]).astype(complex)
wprod, eq_gap, near = -1.0, 0.0, 0
for _ in range(6):
    tau1, U1c = random_density(dB, rng), random_unitary(2 * dB, rng)
    one = Realization.collision([2], tau1, [U1c])
    om1, _ = omega_map(one)
    def f1(rho):
        lk = link(one, rho, [Hc])
        return entropy(lk["omega"]) - one.S_tau() + beta / LN2 * lk["energy"]
    # two uses on separate baths: bath (B_1, B_2), contact j acts on (I_j, B_j)
    U1 = embed(U1c, [0, 1], [2, dB, dB])
    U2 = embed(U1c, [0, 2], [2, dB, dB])
    two = Realization.collision([2, 2], np.kron(tau1, tau1), [U1, U2])
    for _ in range(12):
        te = random_tester([2, 2], rng, 2)
        lam = rng.choice([0.0, 0.0, 1e-3, 0.05, 1.0])
        if lam < 1:   # partly adaptive: mix the transition with a product-tester transition
            r1 = random_density(2, rng)
            Zp = np.kron(te.record(1), np.kron(np.eye(2), r1))
            Zt = (1 - lam) * Zp + lam * te.record()
        else:
            Zt = te.record()
        s = link(two, Zt, [Hc, Hc])
        val = entropy(s["omega"]) - two.S_tau() + beta / LN2 * s["energy"]
        bound = f1(s["rin"][0]) + f1(s["rin"][1])
        wprod = max(wprod, val - bound)
        near += bound - val < 1e-4
        if lam == 0.0:
            eq_gap = max(eq_gap, abs(bound - val))
R.check("Basic properties (b): product collisions score <= f(rho_I1) + f(rho_I2) for adaptive testers, = for product testers",
        wprod < 1e-10 and eq_gap < 1e-10 and near >= 30, f"largest excess {wprod:.1e}, {near} cases within 1e-4")

# 11. the ports example -------------------------------------------------------------------------------------------
ok = True
for bE in (0.1, 0.5, math.log(2), 2.0, 5.0):
    Fin = -math.log(1 + math.exp(-bE))                # beta F of the thermal qubit with gaps (0, E)
    Fout = -math.log(2)                               # beta F of the maximally mixed zero-H qubit
    ok &= Fin - Fout > 0 and abs((Fin - Fout) - math.log(2 / (1 + math.exp(-bE)))) < 1e-15
R.check("switching a thermal (0, E) qubit to a maximally mixed zero-H qubit yields beta^{-1} ln(2/(1+e^{-beta E})) > 0",
        ok)
R.close()
