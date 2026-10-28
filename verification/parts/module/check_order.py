"""Order costs work (Proposition "Order costs work" and its proof in Section 7).

Checks:
  1. the masked-record device (M ~ Bern(p); add a into M at slot 1; apply V^M to Q at slot 2) implements the process
     P_{p,V} exactly as a comb, for V = X and V = Z, and the process satisfies the causal constraints;
  2. as one channel on AQ the process is a thermal operation: a flat coin dephases A by a controlled-Z, a Gibbs coin
     with excited population p applies V, and A controls V on Q; every gate conserves energy (for V = X only when Q is
     degenerate), and no battery is used;
  3. the record M = a xor r shares exactly 1 - h(p) bits with the released a;
  4. the lower-bound inequality S(D_after) - S(D_before) >= 1 - h(e1) - h(e2) of the proof, with e2 the probability that
     the value of a xor r read from the second output and the kept reference differs from a, on perturbed real-time
     devices, for a classical observer (V = X) and a quantum probe (V = Z); the ideal device attains equality;
  5. e1 and e2 - p are at most the strategy distance of the device to P_{p,V} (SDP);
  6. the best tester against the masked-record collision scores exactly 1 - h(p), while the one-channel thermal
     realization scores at most 0 against every tester (rate 0 if a may be withheld);
  7. forming the biased bits one at a time costs log2(2(1-p)) > 1 - h(p) per bit (the single-shot formation cost),
     against 1 - h(p) collectively.
"""
import math

import mpmath as mp
import numpy as np

from qtools import (CNOT, CZ, HAD, P0, P1, I2, X, Z, Report, apply, dm, embed, entropy, h2, herm, ket, near_unitary,
                    ptrace, random_density)
from combs import Realization, TesterLP, causal_defect, maximize_score, strategy_distance

R = Report("Order costs work")
rng = np.random.default_rng(1007)
SQ = lambda p: np.diag(np.sqrt([1 - p, p])).astype(complex)


def masked_collision(p, V):
    """Bath M ~ Bern(p) purified by F; contact 1 = CNOT(A -> M); contact 2 = controlled-V(M -> Q). Order (port, bath)."""
    cv = np.kron(I2, P0) + np.kron(V, P1)
    return Realization.collision([2, 2], np.diag([1 - p, p]).astype(complex), [CNOT, cv])


def held_realization(p, V):
    """Reference realization: copy a into a blank register c, keep a coin r, apply V^c V^r at slot 2."""
    init = np.kron(ket((0,)), SQ(p).reshape(-1))             # (c, r) (x) F with F purifying r
    init = init.reshape(2, 2, 2).reshape(4, 2)
    U1 = embed(CNOT, [0, 1], [2, 2, 2])                       # (port, c, r)
    cv_c = np.kron(I2, P0) + np.kron(V, P1)
    U2 = embed(cv_c, [0, 1], [2, 2, 2]) @ embed(cv_c, [0, 2], [2, 2, 2])
    return Realization([2, 2], init.reshape(-1), [U1, U2], [4, 4, 4], 2)


# 1. masked device = process -----------------------------------------------------------------------------------
ok1 = True
wcaus = 0.0
for p in (0.1, 0.25, 0.4):
    for V in (X, Z):
        a, b = masked_collision(p, V).R, held_realization(p, V).R
        ok1 &= np.abs(a - b).max() < 1e-12
        wcaus = max(wcaus, causal_defect(a, [2, 2]))
R.check("the masked-record device implements P_{p,V} exactly (V = X, Z; p = 0.1, 0.25, 0.4)", ok1)
R.check("P_{p,V} satisfies the causal constraints: the first output does not depend on Q", wcaus < 1e-12)

# 2. thermal operation as one channel ----------------------------------------------------------------------------
def batch_channel(p, V):
    def ch(rho):
        out = np.zeros((4, 4), dtype=complex)
        for aa in (0, 1):
            for r, pr in ((0, 1 - p), (1, p)):
                K = np.kron(dm(ket((aa,))), np.linalg.matrix_power(V, aa ^ r))
                out += pr * K @ rho @ K.conj().T
        return out
    return ch


def choi(ch, d=4):
    out = np.zeros((d * d, d * d), dtype=complex)
    for i in range(d):
        for j in range(d):
            e = np.zeros((d, d), dtype=complex)
            e[i, j] = 1
            out += np.kron(e, ch(e))
    return out


ok2 = ok2e = True
bad_x = 0.0
for p in (0.1, 0.3):
    for V in (X, Z):
        # registers (A, Q, c1, c2): c1 flat coin (H = 0), c2 Gibbs coin with excited population p
        dims = [2, 2, 2, 2]
        cv = np.kron(P0, I2) + np.kron(P1, V)                   # control first, target second
        gates = [embed(CZ, [2, 0], dims), embed(cv, [3, 1], dims), embed(cv, [0, 1], dims)]
        G = gates[2] @ gates[1] @ gates[0]
        coins = np.kron(I2 / 2, np.diag([1 - p, p]))
        circ = lambda rho: ptrace(G @ np.kron(rho, coins) @ G.conj().T, dims, [0, 1])
        ok2 &= np.abs(choi(circ) - choi(batch_channel(p, V))).max() < 1e-12
        for _ in range(5):
            eA, eQ = rng.uniform(0, 2, 2)
            if V is X:
                eQ = 0.0
            gap = math.log((1 - p) / p)
            Htot = (embed(np.diag([0, eA]), [0], dims) + embed(np.diag([0, eQ]), [1], dims)
                    + embed(np.diag([0, gap]), [3], dims))
            ok2e &= all(np.abs(g @ Htot - Htot @ g).max() < 1e-12 for g in gates)
            if V is X:
                Hbad = Htot + embed(np.diag([0, 1.0]), [1], dims)
                bad_x = max(bad_x, np.abs(gates[2] @ Hbad - Hbad @ gates[2]).max())
R.check("as one channel on AQ, P_{p,V} = controlled-Z from a flat coin, then V from a Gibbs coin, then controlled-V "
        "from A (two Gibbs coins, no battery)", ok2)
R.check("every gate conserves energy for diagonal Hamiltonians (V = X: Q degenerate); controlled-X fails otherwise",
        ok2e and bad_x > 0.5)

# 3. mutual information of the record ----------------------------------------------------------------------------
mp.mp.dps = 40
ok3 = True
for p in (mp.mpf("0.01"), mp.mpf("0.1"), mp.mpf(1) / 3, mp.mpf("0.45")):
    joint = {(aa, m): mp.mpf(1) / 2 * (p if m != aa else 1 - p) for aa in (0, 1) for m in (0, 1)}
    H = lambda dist: -sum(v * mp.log(v, 2) for v in dist if v > 0)
    pa = [sum(v for (aa, m), v in joint.items() if aa == x) for x in (0, 1)]
    pm = [sum(v for (aa, m), v in joint.items() if m == x) for x in (0, 1)]
    I = H(pa) + H(pm) - H(joint.values())
    hp = -p * mp.log(p, 2) - (1 - p) * mp.log(1 - p, 2)
    ok3 &= abs(I - (1 - hp)) < mp.mpf(10) ** -35
R.check("I(M : a) = 1 - h(p) exactly for the masked record M = a xor r (40 digits)", ok3)

# 4. the lower-bound inequality on perturbed devices --------------------------------------------------------------
def run_device(p, V, u1, u2, rhoD, quantum):
    """One episode; registers (A, Q[, R], M, E).  Returns e1, e2, S(D_after) - S(D_before)."""
    if quantum:
        dims = [2, 2, 2, 2, 2]
        sA, sQ, sM = 0, 1, 3
        phi = (ket((0, 0)) + ket((1, 1))) / math.sqrt(2)
    else:
        dims = [2, 2, 2, 2]
        sA, sQ, sM = 0, 1, 2
    D_sites = [sM, sM + 1]
    U1 = embed(u1, [sA] + D_sites, dims)
    U2 = embed(u2, [sQ] + D_sites, dims)
    e1 = e2 = 0.0
    Dfin = np.zeros((4, 4), dtype=complex)
    for aa in (0, 1):
        probes = [(dm(phi), 1.0, None)] if quantum else [(dm(ket((q,))), 0.5, q) for q in (0, 1)]
        for probe, wq, q in probes:
            rho = np.kron(np.kron(dm(ket((aa,))), probe), rhoD)
            rho = apply(U1, rho)
            pA = np.real(np.diag(ptrace(rho, dims, [sA])))
            e1 += 0.5 * wq * pA[1 - aa]
            rho = apply(U2, rho)
            if quantum:
                XX = embed(np.kron(X, X), [1, 2], dims)
                plus = float(np.trace((np.eye(32) + XX) / 2 @ rho).real)     # reads a xor r = 0
                e2 += 0.5 * (1 - plus if aa == 0 else plus)
            else:
                pQ = np.real(np.diag(ptrace(rho, dims, [sQ])))
                # value of a xor r read as y2 xor q; error when it differs from a
                e2 += 0.5 * wq * pQ[1 - (aa ^ q)]
            Dfin += 0.5 * wq * ptrace(rho, dims, D_sites)
    return e1, e2, entropy(Dfin) - entropy(rhoD)


worst = {False: 1e9, True: 1e9}
near = {False: 0, True: 0}
exact_gap = 0.0
n_cases = 0
for quantum in (False, True):
    V = Z if quantum else X
    base1 = np.kron(CNOT, I2)                                    # (A, M, E): A controls M
    cv = np.kron(np.kron(P0, I2) + np.kron(P1, V), I2)          # (M, Q, E) ordering fixed below
    for trial in range(250):
        p = float(rng.choice([0.05, 0.15, 0.3, 0.45]))
        eps = float(rng.choice([0.0, 0.003, 0.01, 0.03, 0.1, 0.3]))
        lam = float(rng.choice([0.0, 0.0, 0.01, 0.1]))
        rhoD = (1 - lam) * np.kron(np.diag([1 - p, p]), dm(ket((0,)))) + lam * random_density(4, rng)
        base2 = embed(np.kron(P0, I2) + np.kron(P1, V), [1, 0], [2, 2, 2])  # sites (Q, M, E): M controls Q
        u1 = near_unitary(base1, eps, rng) if eps else base1
        u2 = near_unitary(base2, eps, rng) if eps else base2
        e1, e2, dS = run_device(p, V, u1, u2, rhoD, quantum)
        slack = dS - (1 - h2(e1) - h2(e2))
        worst[quantum] = min(worst[quantum], slack)
        near[quantum] += slack < 0.02
        if eps == 0 and lam == 0:
            exact_gap = max(exact_gap, abs(slack), abs(e1), abs(e2 - p))
        n_cases += 1
R.check("S(D_after) - S(D_before) >= 1 - h(e1) - h(e2) on 250 perturbed devices with a classical observer (V = X)",
        worst[False] > -1e-10 and near[False] >= 60, f"smallest slack {worst[False]:.2e}, {near[False]} within 0.02")
R.check("the same with a quantum probe, half of a maximally entangled pair (V = Z)",
        worst[True] > -1e-10 and near[True] >= 60, f"smallest slack {worst[True]:.2e}, {near[True]} within 0.02")
R.check("the ideal masked device attains equality: e1 = 0, e2 = p, entropy increase 1 - h(p)", exact_gap < 1e-12)

# 5. e1 <= eps and e2 <= p + eps ----------------------------------------------------------------------------------
ok5, cases5 = True, 0
for trial in range(8):
    p = 0.2
    eps = [0.01, 0.05, 0.1, 0.2][trial % 4]
    base1 = np.kron(CNOT, I2)
    base2 = embed(np.kron(P0, I2) + np.kron(P1, X), [1, 0], [2, 2, 2])
    u1, u2 = near_unitary(base1, eps, rng), near_unitary(base2, eps, rng)
    rhoD = np.kron(np.diag([1 - p, p]), dm(ket((0,))))
    e1, e2, _ = run_device(p, X, u1, u2, rhoD, False)
    # the device as a comb: memory (M, E) purified by F; contacts on (port, M, E)
    sq = np.zeros((4, 4), dtype=complex)
    sq[:, :] = np.diag(np.sqrt([1 - p, 0, p, 0]))
    dev = Realization([2, 2], sq.reshape(-1), [u1, u2], [4, 4, 4], 4)
    d_c = strategy_distance(dev.R, masked_collision(p, X).R, [2, 2])
    ok5 &= e1 <= d_c + 1e-7 and e2 <= p + d_c + 1e-7
    cases5 += 1
R.check("e1 <= eps and e2 <= p + eps, with eps the strategy distance of the device to P_{p,X} (8 devices, SDP)", ok5)

# 6. scores of the two realizations ------------------------------------------------------------------------------
lp = TesterLP([2, 2])
ok6, det = True, []
for p in (0.1, 0.3):
    for V in (X, Z):
        HA = np.diag([0.0, 0.7]).astype(complex)
        HQ = np.zeros((2, 2), dtype=complex) if V is X else np.diag([0.0, 1.3]).astype(complex)
        _, val, up = maximize_score(masked_collision(p, V), [HA, HQ], 1.0, lp, iters=60)
        ok6 &= abs(val - (1 - h2(p))) < 1e-7 and up < 1 - h2(p) + 1e-6
        det.append(f"{val:.8f}")
R.check("the best tester against the masked-record collision scores exactly 1 - h(p)", ok6, ", ".join(det))
lp1 = TesterLP([4])
ok6b = True
for p in (0.1, 0.3):
    for V in (X, Z):
        gap = math.log((1 - p) / p)
        HA, HQ = np.diag([0.0, 0.7]), (np.zeros((2, 2)) if V is X else np.diag([0.0, 1.3]))
        # thermal realization as one slot on AQ: bath (c1, c2) in its Gibbs state, the three gates
        dims = [2, 2, 2, 2]
        cv = np.kron(P0, I2) + np.kron(P1, V)
        G = embed(cv, [0, 1], dims) @ embed(cv, [3, 1], dims) @ embed(CZ, [2, 0], dims)
        one = Realization.collision([4], np.kron(I2 / 2, np.diag([1 - p, p])).astype(complex), [G])
        Hport = np.kron(HA, np.eye(2)) + np.kron(np.eye(2), HQ)
        _, val, up = maximize_score(one, [Hport.astype(complex)], 1.0, lp1, iters=40)
        ok6b &= up < 1e-6 and abs(val) < 1e-6
R.check("if a may be withheld, the one-channel thermal realization scores at most 0 for every tester (rate 0)", ok6b)

# 7. formation costs ----------------------------------------------------------------------------------------------
ok7 = True
for p in np.linspace(0.01, 0.49, 49):
    single = math.log2(2 * (1 - p))                 # D_max(Bern(p) || uniform), single-shot formation
    ok7 &= single > 1 - h2(p) + 1e-12 and 1 - h2(p) > 0
R.check("single-shot formation of a Bern(p) bit costs log2(2(1-p)) > 1 - h(p) for 0 < p < 1/2", ok7)
R.close()
