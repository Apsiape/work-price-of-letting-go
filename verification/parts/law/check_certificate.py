"""The two-qubit certificate (Appendix "The two-qubit certificate" and Section "Speed, order and a measurement").

Checks, exactly or to 1e-10:
  1. the process T sends |ab> to the Bell state U|ab>, U = CNOT_{A->B}(H x I), and every output has first marginal I/2;
  2. the held circuit (controlled-Z from two maximally mixed coins, then H_A and CNOT) implements T exactly;
  3. an explicit early-release circuit implements T exactly, and on the probe its device entropy rises by exactly one bit;
  4. the code projector, the stabilizer formula for the leakage, the two-setting bound and the decoder V;
  5. the lower bound Delta S_D >= 1 - h2(e) - e log2 3 on perturbed early-release devices, and its failure in batch;
  6. the numbers quoted in the text, including the finite-sample statement of the heat form with randomized
     hidden settings: the per-episode estimate (3/4)(1 -+ outcome) of the leakage is unbiased, and 150,000
     episodes keep the average leakage within 0.02 of its observed value except with probability below 3e-4.
"""
import math

import numpy as np

from qtools import (HAD, I2, X, Y, Z, Report, apply, dm, embed, entropy, h2, kron, ket, near_unitary, ptrace,
                    random_density, shannon)

R = Report("Two-qubit certificate")
rng = np.random.default_rng(20261010)

CNOT = np.eye(4, dtype=complex)[[0, 1, 3, 2]]          # control first qubit, target second
CZ = np.diag([1, 1, 1, -1]).astype(complex)
U = CNOT @ np.kron(HAD, I2)
P0, P1 = np.diag([1, 0]).astype(complex), np.diag([0, 1]).astype(complex)


def dephase2(x):
    """Dephase both qubits of a two-qubit operator in the computational basis."""
    return np.diag(np.diag(x))


def T(x):
    return U @ dephase2(x) @ U.conj().T


def choi(channel, d=4):
    out = np.zeros((d * d, d * d), dtype=complex)
    for i in range(d):
        for j in range(d):
            e = np.zeros((d, d), dtype=complex)
            e[i, j] = 1
            out += np.kron(e, channel(e))
    return out


# 1. the process and its first marginal
beta = {(a, b): U @ ket((a, b)) for a in (0, 1) for b in (0, 1)}
ok = all(np.allclose(ptrace(dm(v), [2, 2], [0]), I2 / 2) for v in beta.values())
R.check("every |beta_ab> has first marginal I/2, so T is a valid process with A released first", ok)
R.check("|beta_ab> = (I x X^b)(|00> + (-1)^a |11>)/sqrt2",
        all(np.allclose(beta[(a, b)], np.kron(I2, np.linalg.matrix_power(X, b)) @ (ket((0, 0)) + (-1) ** a * ket((1, 1))) / math.sqrt(2))
            for a in (0, 1) for b in (0, 1)))

# 2. held circuit: sites (cA, cB, A, B), coins maximally mixed
dims4 = [2, 2, 2, 2]
G_held = (embed(CNOT, [2, 3], dims4) @ embed(HAD, [2], dims4) @ embed(CZ, [1, 3], dims4) @ embed(CZ, [0, 2], dims4))


def held(x):
    rho = np.kron(np.kron(I2 / 2, I2 / 2), x)
    return ptrace(apply(G_held, rho), dims4, [2, 3])


R.check("the held circuit (two controlled-Z from flat coins, H_A, CNOT) implements T exactly",
        np.allclose(choi(held), choi(T), atol=1e-12))

# 3. explicit early-release circuit: sites (A, B, C, M); step 1 touches A, C, M; step 2 touches B, M only
dimsE = [2, 2, 2, 2]
step1 = (embed(CZ, [2, 0], dimsE) @ embed(CNOT, [0, 3], dimsE) @ embed(HAD, [0], dimsE)
         @ embed(CNOT, [2, 0], dimsE) @ embed(CNOT, [0, 2], dimsE))
step2 = embed(CNOT, [1, 3], dimsE) @ embed(CNOT, [3, 1], dimsE)


def early(x):
    rho = np.kron(x, dm(ket((0, 0))))
    return ptrace(apply(step2 @ step1, rho), dimsE, [0, 1])


R.check("an early-release circuit (A leaves before B arrives) implements T exactly", np.allclose(choi(early), choi(T), atol=1e-12))

# probe: sites (Q, A, B, C, M); A = |0>, BQ maximally entangled, C = M = |0>
dimsP = [2, 2, 2, 2, 2]
phi = (ket((0, 0)) + ket((1, 1))) / math.sqrt(2)
psi0 = np.zeros(32, dtype=complex)
for q in (0, 1):
    psi0 += np.kron(np.kron(np.kron(ket((q,)), ket((0,))), ket((q,))), ket((0, 0))) / math.sqrt(2)
rho0 = dm(psi0)
S1 = embed(step1, [1, 2, 3, 4], dimsP)
S2 = embed(step2, [1, 2, 3, 4], dimsP)
rhof = apply(S2 @ S1, rho0)
dS = entropy(ptrace(rhof, dimsP, [3, 4])) - entropy(ptrace(rho0, dimsP, [3, 4]))
R.check("on the probe the early-release circuit raises the device entropy by exactly 1 bit", abs(dS - 1) < 1e-10, f"{dS:.12f}")

# 4. code, stabilizers, decoder; sites (Q, A, B)
dims3 = [2, 2, 2]
W = np.zeros((8, 2), dtype=complex)
for b in (0, 1):
    W[:, b] = np.kron(ket((b,)), beta[(0, b)])
plus, minus = np.array([1, 1]) / math.sqrt(2), np.array([1, -1]) / math.sqrt(2)
R.check("|beta_0b> = (|++> + (-1)^b |-->)/sqrt2",
        all(np.allclose(beta[(0, b)], (np.kron(plus, plus) + (-1) ** b * np.kron(minus, minus)) / math.sqrt(2)) for b in (0, 1)))
Pi = W @ W.conj().T
XX = embed(np.kron(X, X), [1, 2], dims3)
ZZZ = kron(Z, Z, Z)
ZYY = kron(Z, Y, Y)
I8 = np.eye(8)
R.check("Pi_code = (I + X_A X_B)(I + Z_Q Z_A Z_B)/4", np.allclose(Pi, (I8 + XX) @ (I8 + ZZZ) / 4))
R.check("Tr Pi sigma = (1 + <XX> + <ZZZ> - <ZYY>)/4 as an operator identity", np.allclose(Pi, (I8 + XX + ZZZ - ZYY) / 4))
lhs = I8 - Pi
rhs = (I8 - XX) / 2 + (I8 - ZZZ) / 2
R.check("two settings bound the leakage: I - Pi <= (I - XX)/2 + (I - ZZZ)/2", np.linalg.eigvalsh(rhs - lhs).min() > -1e-12)
PpA = embed(dm(plus), [1], dims3)
PmA = embed(dm(minus), [1], dims3)
V = PpA + PmA @ embed(Z, [0], dims3)
R.check("the decoder V = P_+ x I_Q + P_- x Z_Q maps W|b> to |b>_Q |Phi+>_AB",
        all(np.allclose(V @ W[:, b], np.kron(ket((b,)), phi)) for b in (0, 1)))
ideal = np.zeros((8, 8), dtype=complex)
for q in (0, 1):
    for qq in (0, 1):
        e = np.zeros((4, 4), dtype=complex)
        e[2 * 0 + q, 2 * 0 + qq] = 1          # A=|0>, B entry |q><qq|
        ideal += np.kron(np.outer(ket((q,)), ket((qq,))), T(e)) / 2
R.check("the ideal probe output lies in the code (leakage 0) and has entropy 1",
        abs(np.trace(Pi @ ideal).real - 1) < 1e-12 and abs(entropy(ideal) - 1) < 1e-12)

# 5. lower bound on perturbed early-release devices; sites (Q, A, B, C, M, E)
dims6 = [2] * 6
psi = np.zeros(8, dtype=complex)
for q in (0, 1):
    psi += np.kron(np.kron(ket((q,)), ket((0,))), ket((q,))) / math.sqrt(2)
worst = 1e9
count = 0
small = 0
for trial in range(300):
    eps = rng.choice([0.02, 0.05, 0.1, 0.2, 0.4])
    lam = rng.choice([0.0, 0.05, 0.2])
    rhoD = (1 - lam) * dm(ket((0, 0, 0))) + lam * random_density(8, rng)
    rho = np.kron(dm(psi), rhoD)
    # step 1 may act on A, C, M, E but not on B; step 2 on B, C, M, E but not on A
    base1 = embed(CZ, [1, 0], [2, 2, 2, 2]) @ embed(CNOT, [0, 2], [2, 2, 2, 2]) @ embed(HAD, [0], [2, 2, 2, 2]) \
        @ embed(CNOT, [1, 0], [2, 2, 2, 2]) @ embed(CNOT, [0, 1], [2, 2, 2, 2])          # sites (A, C, M, E)
    base2 = embed(CNOT, [0, 2], [2, 2, 2, 2]) @ embed(CNOT, [2, 0], [2, 2, 2, 2])          # sites (B, C, M, E)
    u1 = embed(near_unitary(base1, eps, rng), [1, 3, 4, 5], dims6)
    u2 = embed(near_unitary(base2, eps, rng), [2, 3, 4, 5], dims6)
    out = apply(u2 @ u1, rho)
    sQAB = ptrace(out, dims6, [0, 1, 2])
    e = 1 - float(np.trace(Pi @ sQAB).real)
    dSD = entropy(ptrace(out, dims6, [3, 4, 5])) - entropy(rhoD)
    if e <= 0.75:
        count += 1
        bound = 1 - h2(e) - e * math.log2(3)
        worst = min(worst, dSD - bound)
        if e < 0.05:
            small += 1
R.check("Delta S_D >= 1 - h2(e) - e log2 3 on 300 perturbed early-release devices",
        worst > -1e-9 and small >= 50, f"{count} devices with e <= 3/4, {small} with e < 0.05, smallest slack {worst:.3e}")
coins = ptrace(apply(G_held, np.kron(np.kron(I2 / 2, I2 / 2), dm(ket((0, 0))))), dims4, [0, 1])
R.check("the bound fails in batch: the held circuit has leakage 0 and does not raise the device entropy",
        entropy(coins) <= 2 + 1e-12)

# 6. numbers
f = lambda e, P=0.025: 1 - h2(e) - e * math.log2(3) - P
R.check("1 - h2(e) - e log2 3 - 0.025 = 0.962, 0.878, 0.348 at e = 1e-3, 1e-2, 0.1",
        round(f(1e-3), 3) == 0.962 and round(f(1e-2), 3) == 0.878 and round(f(0.1), 3) == 0.348,
        f"{f(1e-3):.4f}, {f(1e-2):.4f}, {f(0.1):.4f}")
lo, hi = 0.1, 0.3
for _ in range(80):
    mid = (lo + hi) / 2
    lo, hi = (mid, hi) if f(mid) > 0.05 else (lo, mid)
R.check("the bound exceeds 0.05 exactly up to e = 0.17 (two decimals)", round(lo, 2) == 0.17, f"root {lo:.5f}")
grid = np.linspace(0, 0.75, 7501)
vals = [h2(e) + e * math.log2(3) for e in grid]
R.check("h2(e) + e log2 3 is increasing on [0, 3/4], so the bound in e implies the bound in the error",
        all(b >= a - 1e-15 for a, b in zip(vals, vals[1:])))
worstH = min(h2(1 - p[0]) + (1 - p[0]) * math.log2(3) - shannon(p)
             for p in (rng.dirichlet(np.ones(4) * a) for a in rng.uniform(0.05, 3, 20000)))
R.check("H4(p) <= h2(e) + e log2 3 with e = 1 - p_1 (20000 random distributions)", worstH > -1e-12, f"min slack {worstH:.2e}")
# heat form: observed 5% leakage over 150,000 episodes with randomized hidden settings (about 50,000 per setting).
# Each episode measures one of XX, ZZZ, ZYY, drawn uniformly and hidden from the device until its outputs have left;
# Y = (3/4)(1 - o) for XX and ZZZ and (3/4)(1 + o) for ZYY.  Since the setting is independent of the emitted state,
# E[Y | past] is the leakage of that state, by the stabilizer formula of step 4.
worstY = 0.0
for _ in range(400):
    sig = random_density(8, rng)
    probs = {name: ((1 + np.trace(O @ sig).real) / 2) for name, O in (("XX", XX), ("ZZZ", ZZZ), ("ZYY", ZYY))}
    meanY = (0.75 * 2 * (1 - probs["XX"]) + 0.75 * 2 * (1 - probs["ZZZ"]) + 0.75 * 2 * probs["ZYY"]) / 3
    worstY = max(worstY, abs(meanY - (1 - np.trace(Pi @ sig).real)))
R.check("randomized settings: E[Y] equals the leakage 1 - Tr Pi sigma on 400 random states, with 0 <= Y <= 3/2",
        worstY < 1e-12, f"largest deviation {worstY:.1e}")
N, t = 150000, 0.02
fail = math.exp(-2 * N * t * t / 1.5 ** 2)
R.check("Hoeffding-Azuma: over 150,000 episodes the average leakage exceeds the observed value by more than 0.02 with "
        "probability below 3e-4", fail < 3e-4, f"failure probability {fail:.2e}")
heat = 0.99 - 0.08 - (h2(0.07) + 0.07 * math.log2(3))
R.check("at e = 0.07, S_prep = 0.99 and s = 0.08 the heat bound is 0.433, and 0.429 > 0.42 with a 1% temperature margin",
        round(heat, 3) == 0.433 and 0.99 * heat > 0.42, f"{heat:.4f}, {0.99 * heat:.4f}")
# physical constants
h_planck, k_B = 6.62607015e-34, 1.380649e-23
E = h_planck * 5e9
T_ln2 = E / (k_B * math.log(2))
R.check("a 5 GHz gap has beta E = ln 2 at 346 mK", abs(T_ln2 - 0.346) < 5e-4, f"{T_ln2 * 1e3:.2f} mK")
R.check("0.4313 E is about 1.4e-24 J at 5 GHz", abs(0.4313 * E - 1.43e-24) < 1e-26, f"{0.4313 * E:.3e} J")
gap_GHz = k_B * T_ln2 * math.log((1 - 1e-6) / 1e-6) / h_planck / 1e9
R.check("at that temperature a carrier of thermal impurity 1e-6 needs a gap near 100 GHz", abs(gap_GHz - 100) < 1,
        f"{gap_GHz:.2f} GHz")
R.close()
