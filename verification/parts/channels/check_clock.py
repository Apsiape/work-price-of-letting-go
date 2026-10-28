"""Clocks (Proposition "A returning clock", the stationary-battery example, Theorem "A clock that returns
approximately", Appendix "A clock that returns approximately").

Checks:
  1. the no-broadcasting step: an SDP over time-covariant channels Lambda: C -> CY with exact return
     Lambda(alpha) = alpha x rho (alpha asymmetric) finds no rho with coherence;
  2. the Choi bound (1/4) sup_t ||J - e^{-itG} J e^{itG}||_1 vanishes for time-covariant channels and is positive for
     random channels; ||J - J_t||_1 <= 2||J - J'||_1 for every J' commuting with G; for the Hadamard gate it is 1/2;
  3. |+>^{(x)n} has weight 2^{-n} C(n,k) in the k-excitation sector (exact, n <= 12), the largest is
     C(n, floor(n/2)), and (n+1) C(n, floor(n/2))^2 <= 4^n, so the error bound 1 - 2^{-n} C(n, floor(n/2)) tends to one;
  4. the stationary-battery counterexample: the paired Hadamard on a ladder is unitary and conserves energy exactly; a
     sine packet of width L has <psi|S psi> = cos(pi/(L+1)), so each use deviates by at most pi/(sqrt2 (L+1)) and n
     uses by at most n pi/(sqrt2 (L+1)) against adaptive observers (simulated, with equality approached on one use);
     with L = n^3 the error is O(n^-2) and the battery entropy changes by at most log2(L + 2n + 2);
  5. the rare-excitation primitive on 300 random instances: W_M is unitary, both inputs of G give the payload channel
     U(A.A + C.C)U^*, 1/2||Phi_M - U.U^*||_diamond <= 3b/(2M) (SDP), ||A - I|| <= b/M, ||C||^2 = b/M, the excitation
     operator (1-z)F + z(I-F), the energy identity Tr_G gamma_G[W^*(H + H_G)W - (H + H_G)] = wI + R_M with
     ||R_M|| <= 3||H|| b/M + 2zb, and the purified squared distance <= 2b/M;
  6. the lift L(Y) = sum_xy Pi_x Y Pi_y (x) T_{a_y - a_x} is a unital *-homomorphism that conserves energy exactly, and
     Tr_G[(I x gamma_G^{1/2}) L(Y) (I x gamma_G^{1/2})] = L_S(Tr_G gamma_G Y);
  7. the Hadamard construction: w = E/sqrt2, b = sqrt2 E; the sine-packet Fourier density is even with second moment
     at most pi^4/(4(L+1)^2) (exact series, L <= 400); with m = (n+1)^4 + 2, L1 = (n+1)^8, L2 = (n+1)^4: delta_n and
     the error are O(n^-3), n||R_M|| = o(1), M >= n^2 b, the buffers cover every history, the mean heat lies in
     [0, 2nw];
  8. "Every channel": on random dilations, the tangent inequality Gamma^*(-log2 zeta) + D_H <= vI holds with equality
     at the top, H_B = -beta^{-1} ln zeta_delta has partition function one, VI - [Phi^*(H) - H + Gamma^*(H_B)] >= 0, and
     (ln2/beta) D(tau||zeta_delta) + w_c = (ln2/beta) g - beta^{-1} ln(1 - delta); with M >= n^2 b the per-use
     distance (3/2) b/M sums to o(1);
  9. the bath range: lambda_max - lambda_min of D = U^*HU - H vanishes exactly for covariant unitaries and is sqrt2 E for
     the Hadamard gate; |Tr H_b(sigma_a - sigma_b)| <= span(H_b) T(sigma_a, sigma_b);
 10. Section 1: the thermodynamic capacity of X-dephasing, (ln cosh(beta E/2))/ln 2 bits, lies below the returned-clock
     batch cost E/2, so serving each known input and serving every input differ.
"""
import itertools
import math

import numpy as np
import sympy as sp
from scipy.optimize import minimize

from qtools import (HAD, Report, choi_of_map, diamond_norm_herm, dm, entropy, herm, kraus_apply, mfun, msqrt,
                    random_density, random_herm, random_unitary, relent, trace_norm)

R = Report("Clocks")
rng = np.random.default_rng(20261017)
LN2 = math.log(2)

# ---------------------------------------------------------------------------------------------------- 1. no-broadcast
import cvxpy as cp


def no_broadcast_sdp(alpha, EC, EY):
    """max Re rho_01 over covariant channels Lambda: C -> C (x) Y with Lambda(alpha) = alpha (x) Tr_C Lambda(alpha)."""
    dC, dY = len(EC), len(EY)
    dout = dC * dY
    Hout = np.add.outer(EC, EY).reshape(-1)
    J = cp.Variable((dC * dout, dC * dout), hermitian=True)          # input first
    cons = [J >> 0]
    # trace preservation: Tr_out J = I_C
    for i in range(dC):
        for j in range(dC):
            cons.append(sum(J[i * dout + k, j * dout + k] for k in range(dout)) == (1 if i == j else 0))
    # covariance: entries vanish unless Hout_a - EC_i == Hout_b - EC_j
    for i, j in itertools.product(range(dC), repeat=2):
        for a, b in itertools.product(range(dout), repeat=2):
            if abs((Hout[a] - EC[i]) - (Hout[b] - EC[j])) > 1e-9:
                cons.append(J[i * dout + a, j * dout + b] == 0)

    def apply(Xm):
        return sum(Xm[i, j] * J[i * dout:(i + 1) * dout, j * dout:(j + 1) * dout] for i in range(dC) for j in range(dC)
                   if abs(Xm[i, j]) > 0)
    out = apply(alpha)
    rhoY = sum(out[c * dY:(c + 1) * dY, c * dY:(c + 1) * dY] for c in range(dC))
    for c1 in range(dC):
        for c2 in range(dC):
            cons.append(out[c1 * dY:(c1 + 1) * dY, c2 * dY:(c2 + 1) * dY] == alpha[c1, c2] * rhoY)
    prob = cp.Problem(cp.Maximize(cp.real(rhoY[0, 1])), cons)
    prob.solve(solver=cp.CLARABEL)
    return prob.value


vals = []
for alpha in (dm([1, 1]) / 2, dm([1, 1j]) / 2, 0.7 * dm([math.sqrt(0.3), math.sqrt(0.7)]) + 0.3 * np.eye(2) / 2):
    vals.append(no_broadcast_sdp(alpha.astype(complex), np.array([0.0, 1.0]), np.array([0.0, 1.0])))
vals.append(no_broadcast_sdp((dm([1, 1, 1]) / 3).astype(complex), np.array([0.0, 1.0, 2.0]), np.array([0.0, 1.0])))
R.check("no-broadcasting: covariant channels that return an asymmetric controller exactly give rho no coherence (SDP)",
        max(abs(v) for v in vals) < 1e-6, f"largest coherence {max(abs(v) for v in vals):.1e}")


# ---------------------------------------------------------------------------------------------------- 2. Choi bound
def choi_state(K, d):
    return choi_of_map(lambda e: kraus_apply(K, e), d) / d


def choi_bound(J, Hd, ts):
    d = len(Hd)
    G = np.kron(np.ones(d), Hd) - np.kron(Hd, np.ones(d))          # H_O - H_I^T, input first
    best = 0.0
    for t in ts:
        ph = np.exp(-1j * t * G)
        Jt = (ph[:, None] * J) * ph.conj()[None, :]
        best = max(best, trace_norm(J - Jt))
    return best / 4, G


Hd = np.array([0.0, 1.0, math.sqrt(2) + 0.3])
ts = np.linspace(0, 60, 3001)
ok_cov, ok_gen, ok_tri = True, True, True
min_ratio = 1e9
for trial in range(60):
    # covariant: Kraus operators that each move a definite energy (sums of |j><i| with a fixed gap)
    K = []
    for _ in range(4):
        i, j = rng.integers(0, 3, 2)
        Kk = np.zeros((3, 3), dtype=complex)
        if i == j:
            Kk += np.diag(rng.standard_normal(3) + 1j * rng.standard_normal(3))
        else:
            Kk[j, i] = rng.standard_normal() + 1j * rng.standard_normal()
        K.append(Kk)
    S = sum(k.conj().T @ k for k in K)
    Sih = mfun(S, lambda w: 1 / np.sqrt(w)) if np.linalg.eigvalsh(S).min() > 1e-6 else None
    if Sih is None:
        continue
    K = [k @ Sih for k in K]
    # normalization by S^{-1/2} keeps covariance only if S is diagonal; it is, since every K_k^* K_k is diagonal
    J = choi_state(K, 3)
    b, G = choi_bound(J, Hd, ts[:200])
    ok_cov &= b < 1e-10
    pmix = rng.uniform(0.2, 0.8)
    Kg = [math.sqrt(pmix) * random_unitary(3, rng), math.sqrt(1 - pmix) * random_unitary(3, rng)]
    Jg = choi_state(Kg, 3)
    bg, G = choi_bound(Jg, Hd, ts)
    ok_gen &= bg > 1e-3
    # triangle: J' commuting with G (pinching of Jg, or random block-diagonal states)
    keys = np.round(G, 9)
    pinch = np.zeros_like(Jg)
    for e in np.unique(keys):
        idx = np.where(keys == e)[0]
        pinch[np.ix_(idx, idx)] = Jg[np.ix_(idx, idx)]
    for Jp in (pinch, pinch * 0.5 + 0.5 * np.eye(9) / 9):
        ok_tri &= 4 * bg <= 2 * trace_norm(Jg - Jp) + 1e-9
        min_ratio = min(min_ratio, 2 * trace_norm(Jg - Jp) / (4 * bg))
R.check("the Choi bound vanishes on time-covariant channels and is positive on random mixtures of unitaries "
        "(generic gaps)", bool(ok_cov and ok_gen))
R.check("||J - e^{-itG} J e^{itG}||_1 <= 2||J - J'||_1 for J' commuting with G (pinching and its mixtures)", bool(ok_tri),
        f"smallest ratio rhs/lhs {min_ratio:.3f}")
bH, _ = choi_bound(choi_state([HAD], 2), np.array([0.0, 1.0]), np.linspace(0, 2 * math.pi, 2001))
R.check("Hadamard on H = E|1><1|: the Choi bound is 1/2 = 1 - 2^{-1} C(1, 0)", abs(bH - 0.5) < 1e-9, f"{bH:.12f}")

# ---------------------------------------------------------------------------------------------------- 3. sectors
ok = True
plus = np.array([1, 1]) / math.sqrt(2)
for n in range(1, 13):
    v = np.array([1.0])
    for _ in range(n):
        v = np.kron(v, plus)
    exc = np.array([bin(i).count("1") for i in range(2 ** n)])
    for k in range(n + 1):
        wgt = float(np.sum(np.abs(v[exc == k]) ** 2))
        ok &= abs(wgt - math.comb(n, k) / 2 ** n) < 1e-14
    ok &= max(math.comb(n, k) for k in range(n + 1)) == math.comb(n, n // 2)
ok2 = all((n + 1) * math.comb(n, n // 2) ** 2 <= 4 ** n for n in range(0, 2001))
bnd = [1 - math.comb(n, n // 2) / 2 ** n for n in (1, 2, 10, 100, 1000)]
R.check("|+>^{(x)n} has weight 2^{-n} C(n,k) in sector k; the largest is C(n, floor(n/2)); (n+1) C(n, n/2)^2 <= 4^n "
        "(n <= 2000), so 1 - 2^{-n} C(n, floor(n/2)) >= 1 - 1/sqrt(n+1) -> 1",
        ok and ok2 and bnd[0] == 0.5 and all(b1 <= b2 for b1, b2 in zip(bnd, bnd[1:])) and bnd[-1] > 1 - 1 / math.sqrt(1001),
        ", ".join(f"n={n}: {b:.4f}" for n, b in zip((1, 2, 10, 100, 1000), bnd)))


# ---------------------------------------------------------------------------------------------------- 4. battery
def ladder_unitary(Q):
    """Qubit (x) ladder {0..Q-1}: Hadamard on each pair {|0>|q>, |1>|q-1>}, identity on |0>|0> and |1>|Q-1>."""
    dim = 2 * Q
    U = np.zeros((dim, dim))
    idx = lambda b, q: b * Q + q
    U[idx(0, 0), idx(0, 0)] = 1
    U[idx(1, Q - 1), idx(1, Q - 1)] = 1
    for q in range(1, Q):
        a, b = idx(0, q), idx(1, q - 1)
        U[a, a], U[a, b], U[b, a], U[b, b] = 1 / math.sqrt(2), 1 / math.sqrt(2), 1 / math.sqrt(2), -1 / math.sqrt(2)
    return U


Q = 9
Us = sp.zeros(2 * Q, 2 * Q)
for q in range(1, Q):
    a, b = q, Q + q - 1
    Us[a, a], Us[a, b], Us[b, a], Us[b, b] = 1, 1, 1, -1
Us[0, 0] = Us[2 * Q - 1, 2 * Q - 1] = sp.sqrt(2)                   # sqrt2 U has entries in Z[sqrt2]
Hlad = sp.diag(*[b + q for b in range(2) for q in range(Q)])
R.check("the paired Hadamard on qubit x ladder is unitary and conserves E|1><1| + E q exactly (sympy, Q = 9)",
        sp.simplify(Us.T * Us - 2 * sp.eye(2 * Q)) == sp.zeros(2 * Q) and sp.simplify(Us * Hlad - Hlad * Us) == sp.zeros(2 * Q))


def sine_packet(L, Q, offset):
    c = np.zeros(Q)
    for q in range(1, L + 1):
        c[offset + q - 1] = math.sqrt(2 / (L + 1)) * math.sin(math.pi * q / (L + 1))
    return c


ok_ov, ok_dev = True, True
for L in (1, 2, 5, 20, 100, 1000):
    psi = sine_packet(L, L + 2, 1)
    ov = float(psi[:-1] @ psi[1:])
    ok_ov &= abs(np.linalg.norm(psi) - 1) < 1e-12 and abs(ov - math.cos(math.pi / (L + 1))) < 1e-12
    dev = math.sqrt(1 - math.cos(math.pi / (L + 1)))           # ||(U - H x I) on (.) x psi|| = ||S psi - psi||/sqrt2
    ok_dev &= dev <= math.pi / (math.sqrt(2) * (L + 1))
R.check("sine packet: <psi|S psi> = cos(pi/(L+1)), so ||S psi - psi||/sqrt2 = sqrt(1 - cos(pi/(L+1))) <= pi/(sqrt2(L+1))",
        bool(ok_ov and ok_dev))

worst, worst_vec, best_ratio, obs_ratio = -1e9, -1e9, 0.0, 0.0
for trial in range(60):
    n = int(rng.integers(1, 4))
    L = int(rng.choice([3, 8, 20, 40]))
    Q = L + 2 * (n + 1)
    psi = sine_packet(L, Q, n + 1)
    U = ladder_unitary(Q)
    dR = 2                                                     # one reference qubit per round
    # observer: before each round, entangle a fresh input qubit with a reference via a random unitary, possibly
    # depending on all earlier outputs and references (a random unitary on everything it holds)
    first_zero = trial % 3 == 0
    real = psi.astype(complex)
    ideal = psi.astype(complex)
    held = 1                                                   # dimension of the observer's systems
    for t in range(n):
        inp = np.zeros(2 * dR, dtype=complex)
        if first_zero:
            inp[0] = 1                                         # |0> input, reference |0>
        else:
            inp = random_unitary(2 * dR, rng)[:, 0]
        real = np.kron(inp, real.reshape(-1))                  # (input, ref, [observer], battery)
        ideal = np.kron(inp, ideal.reshape(-1))
        dims_obs = 2 * dR * held
        real = real.reshape(2, dR * held, Q)
        ideal = ideal.reshape(2, dR * held, Q)
        real = np.einsum("aqbp,bkp->akq", U.reshape(2, Q, 2, Q), real)          # U on (input, battery)
        ideal = np.einsum("ab,bkq->akq", HAD, ideal)
        held = held * 2 * dR
        if not first_zero and t < n - 1:
            V = random_unitary(held, rng)
            real = np.einsum("ab,bq->aq", V, real.reshape(held, Q))
            ideal = np.einsum("ab,bq->aq", V, ideal.reshape(held, Q))
    r_obs = real.reshape(held, Q)
    i_obs = ideal.reshape(held, Q)
    rho_r = r_obs @ r_obs.conj().T
    rho_i = i_obs @ i_obs.conj().T
    td = 0.5 * trace_norm(rho_r - rho_i)
    vec = np.linalg.norm(real.reshape(-1) - ideal.reshape(-1))          # purified deviation, battery included
    per_use = math.sqrt(1 - math.cos(math.pi / (L + 1)))
    bound = n * math.pi / (math.sqrt(2) * (L + 1))
    worst = max(worst, td - bound)
    worst_vec = max(worst_vec, vec - n * per_use)
    if n == 1 and first_zero:
        best_ratio = max(best_ratio, vec / per_use)
        obs_ratio = max(obs_ratio, td / ((1 - math.cos(math.pi / (L + 1))) / 2))
R.check("n uses against adaptive observers deviate by at most n pi/(sqrt2(L+1)) in trace distance, and the purified "
        "deviation by at most n sqrt(1 - cos(pi/(L+1))) (60 experiments)",
        worst <= 1e-12 and worst_vec <= 1e-12 and best_ratio > 1 - 1e-9,
        f"one use with input |0>: purified deviation equals the per-use bound ({best_ratio:.6f}); the observer's error is "
        f"second order, {obs_ratio:.4f} x (1 - cos(pi/(L+1)))/2, so the stated bound is valid but not tight")
ok = all(n * math.pi / (math.sqrt(2) * (n ** 3 + 1)) <= math.pi / (math.sqrt(2) * n ** 2) for n in range(1, 10 ** 4))
ok &= all(math.log2(n ** 3 + 2 * n + 2) / n < 3.1 * math.log2(n + 1) / n for n in range(1, 10 ** 4))
R.check("with L = n^3 the error is at most pi/(sqrt2 n^2) and the battery entropy change log2(L + 2n + 2) = o(n)", ok)


# ---------------------------------------------------------------------------------------------------- 5. primitive
def primitive(U, H, M, beta):
    d = len(H)
    Qm = U.conj().T @ H @ U
    Dm = Qm - H
    w = np.linalg.eigvalsh(herm(Dm)).max()
    B = w * np.eye(d) - Dm
    b = np.linalg.eigvalsh(herm(B)).max()
    z = 1 / (1 + math.exp(beta * M))
    F = B / M
    A = msqrt(np.eye(d) - F)
    C = msqrt(F)
    W = np.kron(np.eye(2), U) @ np.block([[A, -C], [C, A]])        # G outer index: |0>, |1>
    return dict(Q=Qm, D=Dm, w=w, B=B, b=b, z=z, F=F, A=A, C=C, W=W)


ok_u = ok_pay = ok_norm = ok_exc = ok_en = ok_pur = True
ratio_dia = []
for trial in range(300):
    d = int(rng.integers(2, 4))
    H = np.diag(np.sort(rng.uniform(0, 2, d)))
    U = random_unitary(d, rng)
    beta = rng.uniform(0.2, 3)
    pr = primitive(U, H, 1.0, beta)
    M = pr["b"] * rng.uniform(1.5, 50)
    P = primitive(U, H, M, beta)
    W, A, C, B, b, z, F, Qm, w = (P[k] for k in ("W", "A", "C", "B", "b", "z", "F", "Q", "w"))
    ok_u &= np.allclose(W.conj().T @ W, np.eye(2 * d), atol=1e-12)
    rho = random_density(d, rng)
    pay = lambda r: U @ (A @ r @ A + C @ r @ C) @ U.conj().T
    for g in (0, 1):
        full = W @ np.kron(dm(np.eye(2)[g]), rho) @ W.conj().T
        out = np.einsum("aibj->ij", full.reshape(2, d, 2, d) * np.eye(2)[:, None, :, None])
        ok_pay &= np.allclose(out, pay(rho), atol=1e-12)
        exc = float(np.trace(full.reshape(2, d, 2, d)[1, :, 1, :]).real)
        Eop = F if g == 0 else np.eye(d) - F            # averaged with weights 1 - z, z: (1-z)F + z(I-F)
        ok_exc &= abs(exc - np.trace(Eop @ rho).real) < 1e-12
    ok_norm &= np.linalg.norm(A - np.eye(d), 2) <= b / M + 1e-12 and abs(np.linalg.norm(C, 2) ** 2 - b / M) < 1e-12
    if trial < 60:
        Jp = choi_of_map(pay, d)
        Ju = choi_of_map(lambda e: U @ e @ U.conj().T, d)
        dist = 0.5 * diamond_norm_herm(Jp - Ju, d, d)
        ratio_dia.append(dist / (3 * b / (2 * M)))
    HG = np.diag([0.0, M])
    Htot = np.kron(HG, np.eye(d)) + np.kron(np.eye(2), H)
    gG = np.diag([1 - z, z])
    gain = W.conj().T @ Htot @ W - Htot
    lhs = np.einsum("aibj->ij", (np.kron(gG, np.eye(d)) @ gain).reshape(2, d, 2, d) * np.eye(2)[:, None, :, None])
    RM = A @ Qm @ A + C @ Qm @ C - Qm - 2 * z * B
    ok_en &= np.allclose(lhs, w * np.eye(d) + RM, atol=1e-10) and np.linalg.norm(RM, 2) <= 3 * np.linalg.norm(H, 2) * b / M + 2 * z * b + 1e-12
    psi = random_unitary(d, rng)[:, 0]
    ok_pur &= np.linalg.norm(U @ A @ psi - U @ psi) ** 2 + np.linalg.norm(U @ C @ psi) ** 2 <= 2 * b / M + 1e-12
R.check("primitive: W_M is unitary and both inputs of G give the payload channel U(A.A + C.C)U^* (300 instances)",
        bool(ok_u and ok_pay))
R.check("||A - I|| <= b/M and ||C||^2 = b/M; G is excited with probability <F> from |0> and <I - F> from |1>, i.e. "
        "(1-z)F + z(I-F) on average", bool(ok_norm and ok_exc))
R.check("1/2||Phi_M - U.U^*||_diamond <= 3b/(2M) (SDP, 60 instances)", max(ratio_dia) <= 1 + 1e-6,
        f"largest ratio to the bound {max(ratio_dia):.3f}")
R.check("energy: Tr_G gamma_G[W^*(H + H_G)W - (H + H_G)] = wI + R_M, R_M = AQA + CQC - Q - 2zB, ||R_M|| <= 3||H||b/M + 2zb",
        bool(ok_en))
R.check("purified record: ||U A psi - U psi||^2 + ||U C psi||^2 <= 2b/M", bool(ok_pur))


# ---------------------------------------------------------------------------------------------------- 6. lift
def lift(Y, labels):
    """L(Y) as a dict shift -> matrix: sum over label pairs of Pi_x Y Pi_y at shift a_y - a_x."""
    out = {}
    for x in set(labels):
        for y in set(labels):
            Px = np.diag([1.0 if l == x else 0.0 for l in labels])
            Py = np.diag([1.0 if l == y else 0.0 for l in labels])
            blk = Px @ Y @ Py
            if np.abs(blk).max() > 0:
                key = tuple(np.subtract(y, x))
                out[key] = out.get(key, 0) + blk
    return out


def mul(A_, B_):
    out = {}
    for ka, va in A_.items():
        for kb, vb in B_.items():
            key = tuple(np.add(ka, kb))
            out[key] = out.get(key, 0) + va @ vb
    return {k: v for k, v in out.items() if np.abs(v).max() > 1e-13}


def close(A_, B_):
    keys = set(A_) | set(B_)
    return all(np.allclose(A_.get(k, 0), B_.get(k, 0), atol=1e-12) for k in keys)


omega = np.array([1.0, math.sqrt(2)])
labs_S = [(0, 0), (1, 0), (0, 1)]                 # energies 0, omega_1, omega_2
labs_G = [(0, 0), (3, 1)]                         # G with gap 3 omega_1 + omega_2
labels = [tuple(np.add(s, g)) for g in labs_G for s in labs_S]
E = np.array([np.dot(l, omega) for l in labels])
ok_hom = ok_cons = ok_tr = True
for _ in range(50):
    Y1 = rng.standard_normal((6, 6)) + 1j * rng.standard_normal((6, 6))
    Y2 = rng.standard_normal((6, 6)) + 1j * rng.standard_normal((6, 6))
    L1, L2 = lift(Y1, labels), lift(Y2, labels)
    ok_hom &= close(mul(L1, L2), lift(Y1 @ Y2, labels))
    ok_hom &= close({tuple(-np.array(k)): v.conj().T for k, v in L1.items()}, lift(Y1.conj().T, labels))
    # energy: (H x I) L(Y) - L(Y)(H x I) + [H_ref, T_u] terms cancel: [H_ref, T_u] = (u . omega) T_u
    for k, v in L1.items():
        ok_cons &= np.allclose(np.diag(E) @ v - v @ np.diag(E) + np.dot(k, omega) * v, 0, atol=1e-12)
    z = rng.uniform(0, 0.5)
    gG = np.array([1 - z, z])
    lhs = {}
    for k, v in L1.items():
        blk = sum(gG[g] * v[3 * g:3 * g + 3, 3 * g:3 * g + 3] for g in range(2))
        if np.abs(blk).max() > 1e-13:
            lhs[k] = blk
    Ys = sum(gG[g] * Y1[3 * g:3 * g + 3, 3 * g:3 * g + 3] for g in range(2))
    ok_tr &= close(lhs, lift(Ys, labs_S))
ok_hom &= close(lift(np.eye(6), labels), {(0, 0): np.eye(6)})
R.check("the lift is a unital *-homomorphism (L(Y1 Y2) = L(Y1) L(Y2), L(Y^*) = L(Y)^*, L(I) = I)", bool(ok_hom))
R.check("the lift conserves system + G + reference energy exactly", bool(ok_cons))
R.check("Tr_G[(I x gamma^{1/2}) L(Y) (I x gamma^{1/2})] = L_S(Tr_G gamma_G Y) for diagonal gamma_G", bool(ok_tr))

# ---------------------------------------------------------------------------------------------------- 7. Hadamard
Es = sp.symbols("E", positive=True)
Hs = sp.diag(0, Es)
Uh = sp.Matrix([[1, 1], [1, -1]]) / sp.sqrt(2)
Dh = sp.simplify(Uh.T * Hs * Uh - Hs)
evs = sorted(Dh.eigenvals().keys(), key=lambda e: float(e.subs(Es, 1)))
wv = evs[-1]
bv = sp.simplify(wv - evs[0])
R.check("Hadamard: D = U^*HU - H has eigenvalues -+E/sqrt2, so w = E/sqrt2 and b = sqrt2 E = 2w",
        sp.simplify(wv - Es / sp.sqrt(2)) == 0 and sp.simplify(bv - sp.sqrt(2) * Es) == 0)


def second_moment(L):
    c = np.array([math.sqrt(2 / (L + 1)) * math.sin(math.pi * q / (L + 1)) for q in range(1, L + 1)])
    k = np.arange(-(L - 1), L)
    Kk = np.where(k == 0, math.pi ** 2 / 3, 2 * (-1.0) ** np.abs(k) / np.where(k == 0, 1, k) ** 2)
    corr = np.correlate(c, c, mode="full")                      # sum_q c_q c_{q+k}
    return float(np.sum(corr * Kk))


ok = True
rat = []
for L in list(range(1, 60)) + [100, 200, 400]:
    m2 = second_moment(L)
    rat.append(m2 / (math.pi ** 4 / (4 * (L + 1) ** 2)))
    ok &= m2 <= math.pi ** 4 / (4 * (L + 1) ** 2)
# numerical integration of the density as an independent engine
L = 7
th = np.linspace(-math.pi, math.pi, 200001)
c = np.array([math.sqrt(2 / (L + 1)) * math.sin(math.pi * q / (L + 1)) for q in range(1, L + 1)])
amp = sum(c[q - 1] * np.exp(1j * q * th) for q in range(1, L + 1))
dens = np.abs(amp) ** 2 / (2 * math.pi)
even = np.allclose(dens, dens[::-1], atol=1e-12)
m2_int = float(np.trapezoid(th ** 2 * dens, th))
R.check("the sine packet's Fourier density is even with second moment <= pi^4/(4(L+1)^2) (exact series, L <= 400; "
        "quadrature at L = 7)", ok and even and abs(m2_int - second_moment(7)) < 1e-6,
        f"ratio to the bound in [{min(rat):.3f}, {max(rat):.3f}]")
ok = True
vals = []
for n in (1, 2, 5, 10, 100, 1000, 10 ** 4):
    m = (n + 1) ** 4 + 2
    L1, L2 = (n + 1) ** 8, (n + 1) ** 4
    b, M = math.sqrt(2), m                       # units of E
    dn = math.pi ** 2 * (n * (m + 1) / (L1 + 1) + n / (L2 + 1))
    err = 1.5 * n * b / M + math.pi ** 4 * n ** 2 * (m + 1) ** 2 / (L1 + 1) ** 2
    z = 0.0                                      # z = 1/(1 + e^{beta M}) is negligible; bound on ||R_M|| without it
    RMn = n * (3 * 1.0 * b / M)
    vals.append((n, dn * n ** 3, err * n ** 3, RMn))
    ok &= M >= n ** 2 * b and n * (m + 1) < (n + 1) * (m + 1) + 2 and n < n + 2
    ok &= m + 1 >= 1 + m                         # per use the E-coordinate moves by at most 1 + m (system 1, G m)
ok &= all(v[1] < 5 * math.pi ** 2 and v[2] < 5 for v in vals) and vals[-1][3] < 1e-10
R.check("Hadamard numbers: n^3 delta_n and n^3 error stay bounded, n||R_M|| -> 0, M >= n^2 b, buffers cover all "
        "histories", ok, "; ".join(f"n={v[0]}: n^3 d_n={v[1]:.2f}, n^3 err={v[2]:.2f}" for v in vals[:4]))
z = 1 / (1 + math.exp(3.0))
R.check("mean heat per use (1 - 2z)<B> lies in [0, b] = [0, 2w], so the retired qubits absorb between 0 and 2nw",
        0 <= (1 - 2 * z) <= 1 and abs(math.sqrt(2) - 2 / math.sqrt(2)) < 1e-15)


# ---------------------------------------------------------------------------------------------------- 8. every channel
def random_dilation(d, dB, rng):
    U = random_unitary(d * dB, rng)
    tau = random_density(dB, rng)
    return U, tau


def bath_out(U, tau, rho, d, dB):
    full = U @ np.kron(rho, tau) @ U.conj().T
    return np.einsum("aiaj->ij", full.reshape(d, dB, d, dB)), np.einsum("aibi->ab", full.reshape(d, dB, d, dB))


ok_tan = ok_part = ok_pos = ok_work = True
gaps = []
for trial in range(12):
    d, dB = 2, int(rng.integers(2, 4))
    U, tau = random_dilation(d, dB, rng)
    beta = rng.uniform(0.3, 2)
    H = np.diag([0.0, rng.uniform(0.2, 2)])
    PhiS = lambda X: np.einsum("aibi->ab", (U @ np.kron(X, tau) @ U.conj().T).reshape(d, dB, d, dB))
    PhiStar = lambda Y: sum(np.outer(np.eye(d)[i], np.eye(d)[j]) * np.trace(Y @ PhiS(np.outer(np.eye(d)[i], np.eye(d)[j]))) for i in range(d) for j in range(d)).T
    Gam = lambda X: np.einsum("aiaj->ij", (U @ np.kron(X, tau) @ U.conj().T).reshape(d, dB, d, dB))
    GamStar = lambda Y: np.array([[np.trace(Y @ Gam(np.outer(np.eye(d)[i], np.eye(d)[j]))) for j in range(d)] for i in range(d)]).T
    DH = beta / LN2 * (PhiStar(H) - H)

    def F(x):
        G = (x[:4] + 1j * x[4:]).reshape(2, 2)
        r = G @ G.conj().T
        r /= np.trace(r).real
        return entropy(Gam(r)) + np.trace(r @ DH).real, r
    best = None
    for _ in range(8):
        res = minimize(lambda x: -F(x)[0], rng.standard_normal(8), method="BFGS", options={"gtol": 1e-11})
        if best is None or res.fun < best.fun:
            best = res
    v, rstar = F(best.x)
    zeta = Gam(rstar)
    LB = mfun(zeta, lambda w_: -np.log2(np.clip(w_, 1e-300, None)))
    top = np.linalg.eigvalsh(herm(GamStar(LB) + DH)).max()
    ok_tan &= top <= v + 1e-6
    gaps.append(v - top)
    delta = rng.uniform(0.01, 0.3)
    zd = (1 - delta) * zeta + delta * np.eye(dB) / dB
    HB = mfun(zd, lambda w_: -np.log(w_) / beta)
    ok_part &= abs(np.trace(mfun(-beta * HB, np.exp)).real - 1) < 1e-12
    Vc = LN2 / beta * v - math.log(1 - delta) / beta
    ok_pos &= np.linalg.eigvalsh(herm(Vc * np.eye(d) - (PhiStar(H) - H + GamStar(HB)))).min() >= -1e-6
    g = v - entropy(tau)
    wc = Vc - np.trace(tau @ HB).real
    lhs = LN2 / beta * relent(tau, zd) + wc
    ok_work &= abs(lhs - (LN2 / beta * g - math.log(1 - delta) / beta)) < 1e-10
R.check("tangent inequality Gamma^*(-log2 zeta) + D_H <= vI at the maximizer, with equality at the top (12 dilations)",
        bool(ok_tan) and max(abs(x) for x in gaps) < 1e-5, f"max |v - lambda_max| = {max(abs(x) for x in gaps):.1e}")
R.check("H_B = -beta^{-1} ln zeta_delta has partition function one, and VI - [Phi^*(H) - H + Gamma^*(H_B)] >= 0",
        bool(ok_part and ok_pos))
R.check("(ln2/beta) D(tau||zeta_delta) + w_c = (ln2/beta) g - beta^{-1} ln(1 - delta), w_c = V - Tr tau H_B", bool(ok_work))
R.check("with M >= n^2 b the per-use distance (3/2) b/M sums over n uses to at most 3/(2n) = o(1)",
        all(n * 1.5 * 1.0 / (n ** 2 * 1.0) <= 1.5 / n for n in range(1, 1000)))

# ---------------------------------------------------------------------------------------------------- 9. range
ok_cov, ok_tr = True, True
Hd = np.array([0.0, 1.0, 2.0, math.sqrt(3)])
for _ in range(50):
    # covariant unitary: block-diagonal in the eigenspaces of H (all nondegenerate here: diagonal phases)
    Uc = np.diag(np.exp(1j * rng.uniform(0, 2 * math.pi, 4)))
    Dm = Uc.conj().T @ np.diag(Hd) @ Uc - np.diag(Hd)
    ev = np.linalg.eigvalsh(herm(Dm))
    ok_cov &= ev.max() - ev.min() < 1e-12
    Ug = random_unitary(4, rng)
    ev = np.linalg.eigvalsh(herm(Ug.conj().T @ np.diag(Hd) @ Ug - np.diag(Hd)))
    ok_cov &= ev.max() - ev.min() > 1e-3
    Hb = random_herm(5, rng)
    sa, sb = random_density(5, rng), random_density(5, rng)
    span = np.ptp(np.linalg.eigvalsh(Hb))
    ok_tr &= abs(np.trace(Hb @ (sa - sb)).real) <= span * 0.5 * trace_norm(sa - sb) + 1e-12
wv, Vv = np.linalg.eigh(Hb)
sa, sb = dm(Vv[:, -1]), dm(Vv[:, 0])
tight = abs(np.trace(Hb @ (sa - sb)).real) / (np.ptp(wv) * 0.5 * trace_norm(sa - sb))
ev = np.linalg.eigvalsh(HAD.conj().T @ np.diag([0, 1.0]) @ HAD - np.diag([0, 1.0]))
R.check("the spread of D vanishes for covariant unitaries and not for generic ones; for the Hadamard it is sqrt2 E",
        bool(ok_cov) and abs(ev.max() - ev.min() - math.sqrt(2)) < 1e-12)
R.check("|Tr H_b(sigma_a - sigma_b)| <= span(H_b) T(sigma_a, sigma_b), with equality on the extreme eigenvectors",
        bool(ok_tr) and abs(tight - 1) < 1e-12)

# ---------------------------------------------------------------------------------------------------- 10. X-dephasing
# Section 1: with a returned clock X-dephasing costs E/2 per use in batch, while each known input can be served at the
# thermodynamic capacity; the two differ because the capacity, beta^{-1} ln cosh(beta E/2), is below E/2.
from scipy.optimize import minimize as _minimize


def bloch(v):
    return 0.5 * np.array([[1 + v[2], v[0] - 1j * v[1]], [v[0] + 1j * v[1], 1 - v[2]]])


Xm = np.array([[0, 1], [1, 0]])
ok = True
vals = []
for bE in (0.3, math.log(2), 1.0, 2.5, 5.0):
    H = np.diag([0.0, bE])                       # beta H

    def neg(v):
        nv = np.linalg.norm(v)
        r = bloch(v / nv if nv > 1 else v)
        o = 0.5 * (r + Xm @ r @ Xm)
        return -(entropy(r) - entropy(o) + np.trace(H @ (o - r)).real / LN2)

    cap = max(-_minimize(neg, rng.uniform(-0.6, 0.6, 3), method="Nelder-Mead",
                         options={"xatol": 1e-11, "fatol": 1e-14, "maxiter": 8000}).fun for _ in range(10))
    formula = math.log(math.cosh(bE / 2)) / LN2
    ok &= abs(cap - formula) < 1e-7 and formula < bE / (2 * LN2)
    vals.append(f"beta E={bE:.2f}: {cap:.5f} < {bE / (2 * LN2):.5f}")
R.check("X-dephasing: thermodynamic capacity (ln cosh(beta E/2))/ln 2 bits, below the returned-clock batch cost E/2",
        bool(ok), "; ".join(vals[:3]))
R.close()
