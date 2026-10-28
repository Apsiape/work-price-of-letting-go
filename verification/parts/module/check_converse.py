"""The strong converse (Section 4 and Appendix C).

Checks:
  1. b_beta(P_B) = beta E_init/ln2 + log2 Tr(P_B e^{-beta H_B}): for one eigenstate it is beta(E_init - E_fin)/ln2; a
     projector of rank R_B with energies >= E_init - W has b_beta <= beta W/ln2 + log2 R_B (equality when all energies are
     E_init - W);
  2. C.1: averaging a tester over a grid of common translations makes x commute with H_Z = sum_j (H_Oj - H_Ij^T); mixing in
     the flat tester makes it full rank; the minimal dilations V_k = (I (x) sqrt(C_k^T))(|I>> (x) I) are isometries that
     reproduce the tester and intertwine sum_{l<=k} H_Il + H_Mk with sum_{l<k} H_Ol; the stage isometries F_k with
     V_k = (I (x) F_k)(V_{k-1} (x) I) exist and intertwine the stage energies;
  3. C.1: Tr H_Z nu_Z = sum_j (energy delivered in O_j - energy injected in I_j) for invariant testers (it fails for
     non-invariant ones);
  4. C.2: in a block of dimension m the m^2 vectors e_i, e_i + e_k, e_i + i e_k, normalized by their frame operator, give
     rank-one effects that sum to I and are informationally complete; L <= d^4 overall; the instrument with Kraus
     operators sqrt(1-gamma) I and sqrt(gamma)|u><v_x| is trace preserving, charge conserving, and its outcome law
     determines the pinching;
  5. C.3: the number of outcome strings with at most 2 gamma N tests is at most 2^{N theta_gamma},
     theta_gamma = h(2 gamma) + 2 gamma log2 L, for 0 < gamma < 1/4 (exact integers);
  6. Lemma "cap" (C.4): on random instances satisfying its hypotheses, every step of its proof (commutation, block ranks,
     rejected weight, operator inequality, bound on Tr_A Pi) and the conclusion
     H_min^s(A|E) <= log2[e^{beta(E_i - L_E)} Z_K/(p Z_E)] + 2 log2(2/(1-s)), with H_min^s computed by an SDP;
  7. C.4-C.5: at s = 1/2 the additive constant is 4; the cap becomes eq. (cap); 4 delta/r <= 1/16; the bound
     1 - 2 log2(delta p_G) <= 13 + 4 log2(1/p); the assembled inequality; and with a = min{delta/16, delta^2/(256 C_f^2)}
     the right-hand side exceeds N(K - delta) for all large N (explicit threshold).
"""
import itertools
import math

from qtools import Report, dm, embed, entropy, herm, ket, random_density, random_unitary, sqrtm_psd  # noqa: I001
import cvxpy as cp
import numpy as np

from combs import Realization, Tester, flat_record, link, nu_ZF, random_tester, realize_record, record_prefixes

R = Report("The strong converse")
rng = np.random.default_rng(31415)
LN2 = math.log(2)
beta = 1.0

# 1. b_beta ------------------------------------------------------------------------------------------------------
ok1 = True
near1 = 0
for _ in range(200):
    n = int(rng.integers(2, 8))
    EB = np.sort(rng.uniform(0, 5, n))
    Ein = float(rng.choice(EB))
    k = int(rng.integers(0, n))
    b1 = beta * Ein / LN2 + math.log2(math.exp(-beta * EB[k]))
    ok1 &= abs(b1 - beta * (Ein - EB[k]) / LN2) < 1e-12
    S = rng.choice(n, int(rng.integers(1, n + 1)), replace=False)
    W = Ein - EB[S].min()
    if rng.random() < 0.3:
        EB2 = EB.copy()
        EB2[S] = EB[S].min()
        EBu = EB2
    else:
        EBu = EB
    bb = beta * Ein / LN2 + math.log2(np.sum(np.exp(-beta * EBu[S])))
    bound = beta * W / LN2 + math.log2(len(S))
    ok1 &= bb <= bound + 1e-12
    near1 += abs(bb - bound) < 1e-12
R.check("b_beta of one eigenstate is beta(E_init - E_fin)/ln2; a rank-R_B projector with energies >= E_init - W has "
        "b_beta <= beta W/ln2 + log2 R_B, with equality when all energies are E_init - W", ok1 and near1 >= 30,
        f"{near1} equality cases")

# 2-3. C.1 ---------------------------------------------------------------------------------------------------------
def charge_Z(dims, H):
    """H_Z = sum_j (H_Oj - H_Ij^T) on (I_1, O_1, ..., I_n, O_n)."""
    full = [x for d in dims for x in (d, d)]
    return sum(embed(H[j], [2 * j + 1], full) - embed(H[j].T, [2 * j], full) for j in range(len(dims)))


def invariant_tester(dims, H, rng, mix=0.05, K=16):
    Zn = random_tester(dims, rng, 2).record()
    full = [x for d in dims[:-1] for x in (d, d)] + [dims[-1]]
    gen = sum(embed(H[j], [2 * j], full) for j in range(len(dims))) - sum(embed(H[j].T, [2 * j + 1], full)
                                                                           for j in range(len(dims) - 1))
    # gen = sum H_I - sum H_O^T on the record space; average Z over e^{-iu gen} for u on a grid (integer energies)
    w, v = np.linalg.eigh(herm(gen))
    Zavg = np.zeros_like(Zn)
    for u in 2 * np.pi * np.arange(K) / K:
        Uu = (v * np.exp(-1j * u * w)) @ v.conj().T
        Zavg += Uu @ Zn @ Uu.conj().T / K
    return (1 - mix) * Zavg + mix * flat_record(dims)


def minimal_dilations(Zs, dims):
    """V_k : O_{<k} -> I_{<=k} (x) copy space, V_k|o> = sum_i |i> (x) sqrt(C_k^T)|i, o> (interleaved order)."""
    Vs = []
    for k, Ck in enumerate(Zs, start=1):
        S = sqrtm_psd(Ck.T)
        dI = [dims[l] for l in range(k)]
        dO = [dims[l] for l in range(k - 1)]
        Din, Dout = int(np.prod(dO)) if dO else 1, int(np.prod(dI))
        D = Ck.shape[0]
        V = np.zeros((Dout * D, Din), dtype=complex)
        for o in range(Din):
            o_dig = list(np.unravel_index(o, dO)) if dO else []
            for i in range(Dout):
                i_dig = list(np.unravel_index(i, dI))
                inter = []
                for l in range(k):
                    inter.append(i_dig[l])
                    if l < k - 1:
                        inter.append(o_dig[l])
                full_dims = [x for l in range(k) for x in ((dims[l], dims[l]) if l < k - 1 else (dims[l],))]
                idx = np.ravel_multi_index(inter, full_dims)
                V[i * D:(i + 1) * D, o] = S[:, idx]
        Vs.append(V)
    return Vs


dims = [2, 2, 2]
H = [np.diag([0.0, 1.0]).astype(complex), np.diag([0.0, 2.0]).astype(complex), np.diag([0.0, 1.0]).astype(complex)]
ok2a = ok2b = ok2c = ok2d = ok2e = True
for _ in range(4):
    Zn = invariant_tester(dims, H, rng)
    x = np.kron(Zn, np.eye(dims[-1])).T
    HZ = charge_Z(dims, H)
    ok2a &= np.abs(x @ HZ - HZ @ x).max() < 1e-10
    ok2b &= np.linalg.eigvalsh(herm(x)).min() > 1e-6
    Zs = record_prefixes(Zn, dims)
    Vs = minimal_dilations(Zs, dims)
    for k, (V, Ck) in enumerate(zip(Vs, Zs), start=1):
        ok2c &= np.abs(V.conj().T @ V - np.eye(V.shape[1])).max() < 1e-10
        dI = [dims[l] for l in range(k)]
        dO = [dims[l] for l in range(k - 1)]
        Dout, D = int(np.prod(dI)), Ck.shape[0]
        # tracing the copy space reproduces the tester channel: Choi entries <i|T(|o><o'|)|i'> = C[(i,o),(i',o')]
        T = np.einsum("iao,jap->iojp", V.reshape(Dout, D, -1), V.conj().reshape(Dout, D, -1))
        full_dims = [x_ for l in range(k) for x_ in ((dims[l], dims[l]) if l < k - 1 else (dims[l],))]
        Cr = np.zeros_like(Ck)
        for (i, o, j, p_), val in np.ndenumerate(T):
            i_dig, j_dig = list(np.unravel_index(i, dI)), list(np.unravel_index(j, dI))
            o_dig = list(np.unravel_index(o, dO)) if dO else []
            p_dig = list(np.unravel_index(p_, dO)) if dO else []
            r = [x_ for l in range(k) for x_ in ((i_dig[l], o_dig[l]) if l < k - 1 else (i_dig[l],))]
            c = [x_ for l in range(k) for x_ in ((j_dig[l], p_dig[l]) if l < k - 1 else (j_dig[l],))]
            Cr[np.ravel_multi_index(r, full_dims), np.ravel_multi_index(c, full_dims)] = val
        ok2c &= np.abs(Cr - Ck).max() < 1e-10
        # energies: sum_{l<k} H_Ol on the input; sum_{l<=k} H_Il + H_Mk on the output; H_Mk on the copy space
        HO = sum(embed(H[l], [l], dO) for l in range(k - 1)) if dO else np.zeros((1, 1))
        HI = sum(embed(H[l], [l], dI) for l in range(k))
        HM = sum(embed(H[l], [2 * l + 1], full_dims) for l in range(k - 1)) - sum(embed(H[l].T, [2 * l], full_dims)
                                                                                 for l in range(k))
        lhs = (np.kron(HI, np.eye(D)) + np.kron(np.eye(Dout), HM)) @ V
        rhs = V @ HO
        ok2d &= np.abs(lhs - rhs).max() < 1e-10
        if k > 1:
            # stage isometry F_k with V_k = (I_{I<k} (x) F_k)(V_{k-1} (x) I_{O_{k-1}})
            Vp = Vs[k - 2]
            Dprev = Zs[k - 2].shape[0]
            Doutp = int(np.prod(dI[:-1]))
            A = np.kron(Vp, np.eye(dims[k - 2]))                       # rows (I_<k, copy_{k-1}, O_{k-1})
            nin = V.shape[1]
            a = A.reshape(Doutp, Dprev * dims[k - 2], nin).transpose(2, 0, 1).reshape(nin * Doutp, -1)
            b = V.reshape(Doutp, dims[k - 1] * D, nin).transpose(2, 0, 1).reshape(nin * Doutp, -1)
            FT = np.linalg.pinv(a, rcond=1e-10) @ b
            F = FT.T                                                    # (I_k, copy_k) <- (copy_{k-1}, O_{k-1})
            ok2e &= np.abs(a @ FT - b).max() < 1e-8
            # intertwining on the range of V_{k-1} (x) I
            Hin = np.kron(HM_prev, np.eye(dims[k - 2])) + np.kron(np.eye(Dprev), H[k - 2])
            Hout = np.kron(H[k - 1], np.eye(D)) + np.kron(np.eye(dims[k - 1]), HM)
            Prng = a.conj().T @ np.linalg.pinv(a.conj().T, rcond=1e-10)  # projector onto the row range of a
            ok2e &= np.abs((Hout @ F - F @ Hin) @ Prng.T).max() < 1e-8
        HM_prev = HM
R.check("C.1: grid-averaged testers commute with H_Z, and mixing in the flat tester makes them full rank", ok2a and ok2b)
R.check("C.1: V_k = (I (x) sqrt(C_k^T))(|I>> (x) I) are isometries that reproduce the tester channel", ok2c)
R.check("C.1: V_k intertwines sum_{l<k} H_Ol with sum_{l<=k} H_Il + H_Mk, H_Mk = sum_{l<k} H_Ol' - sum_{l<=k} H_Il'^T",
        ok2d)
R.check("C.1: stage isometries F_k with V_k = (I (x) F_k)(V_{k-1} (x) I) exist and intertwine the stage energies", ok2e)

w3, bad3 = 0.0, 0.0
for _ in range(10):
    dB = 2
    real = Realization.collision(dims, random_density(dB, rng), [random_unitary(2 * dB, rng) for _ in dims])
    Zn = invariant_tester(dims, H, rng)
    x = np.kron(Zn, np.eye(dims[-1])).T
    sx = sqrtm_psd(x)
    nu = sx @ real.R @ sx
    lk = link(real, Zn, H)
    w3 = max(w3, abs(np.trace(charge_Z(dims, H) @ nu).real - lk["energy"]))
    Zr = random_tester(dims, rng, 2).record()
    xr = np.kron(Zr, np.eye(dims[-1])).T
    sxr = sqrtm_psd(xr)
    bad3 = max(bad3, abs(np.trace(charge_Z(dims, H) @ sxr @ real.R @ sxr).real - link(real, Zr, H)["energy"]))
R.check("C.1: Tr H_Z nu_Z = energy delivered minus energy injected for invariant testers (10 random processes)",
        w3 < 1e-10 and bad3 > 1e-3, f"{w3:.1e}; for non-invariant testers the difference reaches {bad3:.2f}")

# 4. C.2 ---------------------------------------------------------------------------------------------------------
ok4 = True
for m in range(1, 7):
    vecs = [np.eye(m)[i] for i in range(m)]
    for i, k in itertools.combinations(range(m), 2):
        vecs.append(np.eye(m)[i] + np.eye(m)[k])
        vecs.append(np.eye(m)[i] + 1j * np.eye(m)[k])
    Sf = sum(np.outer(v, v.conj()) for v in vecs)
    w, V = np.linalg.eigh(Sf)
    Sih = (V / np.sqrt(w)) @ V.conj().T
    effs = [Sih @ np.outer(v, v.conj()) @ Sih for v in vecs]
    ok4 &= len(vecs) == m * m and np.allclose(sum(effs), np.eye(m))
    M = np.array([np.concatenate([e.real.reshape(-1), e.imag.reshape(-1)]) for e in effs])
    ok4 &= np.linalg.matrix_rank(M) == m * m
R.check("C.2: in a block of dimension m the frame-normalized vectors give m^2 rank-one effects summing to I that span the "
        "Hermitian matrices (m = 1..6)", ok4)
ok4b = True
for _ in range(20):
    d2 = 16
    sizes = []
    while sum(sizes) < d2:
        sizes.append(int(min(rng.integers(1, 6), d2 - sum(sizes))))
    ok4b &= sum(s * s for s in sizes) <= 16 ** 2
    # an instrument on one block of the charge: probabilities determine the pinching
    m = sizes[0]
    gam = float(rng.uniform(0.01, 0.24))
    vecs = [np.eye(m)[i] for i in range(m)]
    for i, k in itertools.combinations(range(m), 2):
        vecs += [np.eye(m)[i] + np.eye(m)[k], np.eye(m)[i] + 1j * np.eye(m)[k]]
    Sf = sum(np.outer(v, v.conj()) for v in vecs)
    w, V = np.linalg.eigh(Sf)
    vx = [(V / np.sqrt(w)) @ V.conj().T @ v for v in vecs]
    u = np.eye(m)[0]
    Ks = [math.sqrt(1 - gam) * np.eye(m)] + [math.sqrt(gam) * np.outer(u, vv.conj()) for vv in vx]
    ok4b &= np.allclose(sum(Kk.conj().T @ Kk for Kk in Ks), np.eye(m))
    # charge conservation: each Kraus operator maps the block into itself (u has the energy of the block)
    nu = random_density(m, rng)
    q = [float(np.trace(Kk @ nu @ Kk.conj().T).real) for Kk in Ks]
    ok4b &= abs(q[0] - (1 - gam)) < 1e-12 and abs(sum(q) - 1) < 1e-12
    # the outcome law determines the block: solve Tr(Lambda_x nu) = q_x/gamma over a real basis of Hermitian matrices
    basis = []
    for i in range(m):
        for j in range(m):
            Bm = np.zeros((m, m), dtype=complex)
            if i == j:
                Bm[i, i] = 1
            elif i < j:
                Bm[i, j] = Bm[j, i] = 1
            else:
                Bm[i, j], Bm[j, i] = 1j, -1j
            basis.append(Bm)
    G = np.array([[np.trace(np.outer(vv, vv.conj()) @ Bm).real for Bm in basis] for vv in vx])
    coef = np.linalg.solve(G, np.array(q[1:]) / gam)
    rec = sum(c_ * Bm for c_, Bm in zip(coef, basis))
    ok4b &= np.allclose(rec, nu, atol=1e-9)
R.check("C.2: L = sum m_b^2 <= d^4; the instrument is trace preserving and its outcome law determines the block", ok4b)

# 5. C.3 counting ------------------------------------------------------------------------------------------------
ok5, ratios5 = True, []
for N in (20, 50, 100, 200, 400):
    for gam in (0.02, 0.05, 0.1, 0.2, 0.24):
        for Lc in (2, 5, 16, 256):
            kmax = math.floor(2 * gam * N)
            count = sum(math.comb(N, k) * Lc ** k for k in range(kmax + 1))
            th = (-(2 * gam) * math.log2(2 * gam) - (1 - 2 * gam) * math.log2(1 - 2 * gam)) + 2 * gam * math.log2(Lc)
            ok5 &= math.log2(count) <= N * th + 1e-9
            ratios5.append(math.log2(count) / (N * th))
R.check("C.3: sum_{k <= 2 gamma N} C(N,k) L^k <= 2^{N theta_gamma} for 0 < gamma < 1/4 (exact integers)", ok5,
        f"largest exponent ratio {max(ratios5):.3f}")

# 6. Lemma "cap" (C.4) ----------------------------------------------------------------------------------------------
def hmin_smooth(rhoAE, dA, dE, s):
    sig = cp.Variable((dA * dE, dA * dE), hermitian=True)
    Xv = cp.Variable((dA * dE, dA * dE), complex=True)
    Yv = cp.Variable((dE, dE), hermitian=True)
    cons = [sig >> 0, cp.real(cp.trace(sig)) <= 1, cp.kron(np.eye(dA), Yv) - sig >> 0,
            cp.bmat([[rhoAE, Xv], [Xv.H, sig]]) >> 0, cp.real(cp.trace(Xv)) >= math.sqrt(1 - s * s)]
    pr = cp.Problem(cp.Minimize(cp.real(cp.trace(Yv))), cons)
    pr.solve(solver="CLARABEL")
    return -math.log2(pr.value)


ok6 = dict(comm=True, rank=True, rej=True, op=True, tr=True, concl=True)
slacks, main_gap = [], []
inst = 0
while inst < 24:
    dA, dE, dK = 3, 3, 3
    eA = np.sort(rng.integers(0, 4, dA)).astype(float)
    eE = np.sort(rng.integers(0, 4, dE)).astype(float)
    eK = np.sort(rng.integers(0, 4, dK)).astype(float)
    Ei = float(rng.integers(0, 4))
    LE = float(eA.min() + rng.integers(0, 2))
    Kmask = rng.random(dK) < 0.8
    if not Kmask.any():
        continue
    idx = [(a, e, k) for a in range(dA) for e in range(dE) for k in range(dK)
           if abs(eA[a] + eK[k] - eE[e] - Ei) < 1e-9 and eA[a] >= LE and Kmask[k]]
    if len(idx) < 3:
        continue
    psi = np.zeros(dA * dE * dK, dtype=complex)
    for (a, e, k) in idx:
        psi[(a * dE + e) * dK + k] = rng.standard_normal() + 1j * rng.standard_normal()
    psi /= np.linalg.norm(psi)
    om = dm(psi)
    oAE = herm(om.reshape(dA * dE, dK, dA * dE, dK).trace(axis1=1, axis2=3))
    oE = herm(oAE.reshape(dA, dE, dA, dE).trace(axis1=0, axis2=2))
    gE = np.exp(-beta * eE)
    ZE = gE.sum()
    Mx = np.diag(np.sqrt(ZE / gE)) @ oE @ np.diag(np.sqrt(ZE / gE))
    p = 1 / np.linalg.eigvalsh(herm(Mx)).max()
    ZK = float(np.sum(np.exp(-beta * eK[Kmask])))
    HAE = np.kron(np.diag(eA), np.eye(dE)) - np.kron(np.eye(dA), np.diag(eE))
    ok6["comm"] &= np.abs(oAE @ HAE - HAE @ oAE).max() < 1e-12
    for s in (0.25, 0.5):
        a0 = (1 - s) / (2 * ZK)
        Pi = np.zeros((dA * dE, dA * dE), dtype=complex)
        rej = 0.0
        for kval in np.unique(eK[Kmask]):
            ks = [k for k in range(dK) if Kmask[k] and eK[k] == kval]
            Pk = sum(dm(ket((k,), [dK])) for k in ks)
            blk = herm((np.kron(np.eye(dA * dE), Pk) @ om).reshape(dA * dE, dK, dA * dE, dK).trace(axis1=1, axis2=3))
            w, V = np.linalg.eigh(blk)
            ok6["rank"] &= int(np.sum(w > 1e-12)) <= len(ks)
            acc = w >= a0 * math.exp(-beta * kval)
            Pi += V[:, acc] @ V[:, acc].conj().T
            rej += float(np.sum(w[(~acc) & (w > 0)]))
        ok6["rej"] &= rej <= (1 - s) / 2 + 1e-12
        Ephase = np.diag(np.exp(beta * (np.diag(HAE).real - Ei)))
        ok6["op"] &= np.linalg.eigvalsh(herm(oAE @ Pi - a0 * Ephase @ Pi)).min() > -1e-12
        trA = herm(Pi.reshape(dA, dE, dA, dE).trace(axis1=0, axis2=2))
        ok6["tr"] &= np.linalg.eigvalsh(trA).max() <= math.exp(beta * (Ei - LE)) / (a0 * p * ZE) + 1e-9
        H = hmin_smooth(oAE, dA, dE, s)
        bound = math.log2(math.exp(beta * (Ei - LE)) * ZK / (p * ZE)) + 2 * math.log2(2 / (1 - s))
        ok6["concl"] &= H <= bound + 1e-6
        slacks.append(bound - H)
        main_gap.append(H - (bound - 2 * math.log2(2 / (1 - s))))
    inst += 1
R.check("Lemma 'cap': omega_AE commutes with H_A - H_E, and its block at K-energy k has rank <= d_k", ok6["comm"] and ok6["rank"])
R.check("Lemma 'cap': rejected weight <= (1-s)/2, omega_AE Pi >= a_0 e^{beta(H_A - H_E - E_i)} Pi, "
        "Tr_A Pi <= e^{beta(E_i - L_E)}/(a_0 p Z_E) I_E", ok6["rej"] and ok6["op"] and ok6["tr"])
R.check("Lemma 'cap': H_min^s(A|E) <= log2[e^{beta(E_i - L_E)} Z_K/(p Z_E)] + 2 log2(2/(1-s)) (SDP, 24 instances, s = 1/4, 1/2)",
        ok6["concl"], f"smallest slack {min(slacks):.3f} bits; H_min^s comes within {-max(main_gap):.3f} bits of the main term")

# 7. C.4-C.5 constants -------------------------------------------------------------------------------------------
ok7 = abs(2 * math.log2(2 / (1 - 0.5)) - 4) < 1e-15
for _ in range(500):
    p = float(10 ** rng.uniform(-12, 0))
    pG = float(rng.uniform(p, 1))
    dl = p / 64
    r = p / pG
    ok7 &= 4 * dl / r <= 1 / 16 + 1e-15
    ok7 &= 1 - 2 * math.log2(dl * pG) <= 13 + 4 * math.log2(1 / p) + 1e-9
    # the cap with Z_K = Z_T Tr(P_B e^{-beta H_B}) |G|, Z_E = Z_T, E_i = E_init, L_E = N(dE - u), s = 1/2
    ZT, trPB, Gc, Einit, L_E = (float(rng.uniform(1, 50)), float(rng.uniform(0.01, 5)), float(rng.integers(1, 1000)),
                                float(rng.uniform(0, 10)), float(rng.uniform(0, 10)))
    lhs = math.log2(math.exp(beta * (Einit - L_E)) * ZT * trPB * Gc / (p * ZT)) + 4
    bbeta = beta * Einit / LN2 + math.log2(trPB)
    ok7 &= abs(lhs - (bbeta - beta * L_E / LN2 + math.log2(Gc) + math.log2(1 / p) + 4)) < 1e-9
R.check("C.4-C.5: 2 log2(2/(1-s)) = 4 at s = 1/2; the cap is eq. (cap); 4 delta/r <= 1/16; "
        "1 - 2 log2(delta p_G) <= 13 + 4 log2(1/p)", ok7)
ok7b, thresholds = True, []
for dlt in (0.01, 0.1, 0.5, 1.0):
    for Cf in (0.5, 3.0, 20.0):
        a = min(dlt / 16, dlt ** 2 / (256 * Cf ** 2))
        K = 1.0
        # explicit threshold: N delta/8 >= C sqrt(13 N) and N delta/8 > 4
        N0 = max(64 * 13 * Cf ** 2 / dlt ** 2, 32 / dlt) + 1
        for N in np.unique(np.concatenate([np.geomspace(N0, N0 * 1e6, 40), [N0]])):
            pp = 2.0 ** (-a * N)                                   # the extreme case log2(1/p) = a N
            rhs = N * (K - dlt / 2) - Cf * math.sqrt(N * (13 + 4 * a * N)) - 2 * a * N - 4
            ok7b &= rhs > N * (K - dlt)
        thresholds.append(N0)
R.check("C.5: with a = min{delta/16, delta^2/(256 C_f^2)} and log2(1/p) <= aN, the right-hand side exceeds N(K - delta) "
        "for all N >= max(832 C_f^2/delta^2, 32/delta)", ok7b, f"thresholds up to {max(thresholds):.1e}")
R.close()
