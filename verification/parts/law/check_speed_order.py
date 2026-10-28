"""Speed and order in the collision model (Section "Speed, order and a measurement").

Checks:
  1. the work identity of a K-step collision stroke: excess work over the free-energy change = kT sum_j d(q_{j-1}||q_j);
  2. A_K(a, b) >= l^2/(2K) for cooling strokes 0 < b < a <= 1/2, at every K (l the thermodynamic length);
  3. the bound fails outside that scope (heating, or starting above 1/2), while A_K >= l^2/(4K) holds in every direction;
  4. summing over strokes: sum_j l_j^2/K_j >= (sum_j l_j)^2 / K_tot; with one shared budget of M contacts the least
     leading dissipation is (L_B + L_O)^2/(2M), and two separate interfaces with the same total M reach the same
     value at the split K_B : K_O = L_B : L_O, so sharing adds no cross term; the difference L_B L_O / M arises
     only against separate interfaces granted M contacts each (2M in all); L_B = 2, L_O = 3, M = 100 gives
     0.125 for both allocations of M and 0.065 for 2M contacts;
  5. amplitude damping at p = 1/2, beta E = ln 2: real-time rate log2(3/2), batch rate 0.153640 E, order gap 0.431323 E;
  6. a fit c + s/K over 4 to 12 contacts biases the intercept by about a tenth of the order cost, and a 1/K^2 term or
     a window of 10 to 50 contacts brings the bias to about one percent;
  7. at fixed K, the work diverges as the target error vanishes, logarithmically for one contact and far more slowly for
     several.
"""
import math

import numpy as np
from scipy.optimize import minimize_scalar

from collision import A_K, d, h, length
from qtools import Report

R = Report("Speed and order")
rng = np.random.default_rng(7)
LN2 = math.log(2)

# 1. identity: with E_j = kT ln((1-q_j)/q_j), (q_{j-1}-q_j) beta E_j = h(q_{j-1}) - h(q_j) + d(q_{j-1}||q_j)
worst = 0.0
for _ in range(2000):
    p, q = rng.uniform(1e-6, 1 - 1e-6, 2)
    lhs = (p - q) * math.log((1 - q) / q)
    rhs = float(h(p) - h(q) + d(p, q))
    worst = max(worst, abs(lhs - rhs))
R.check("per-step identity (q_{j-1} - q_j) beta E_j = h(q_{j-1}) - h(q_j) + d(q_{j-1}||q_j)", worst < 1e-12, f"{worst:.1e}")

# 2. cooling bound at every K
ratio_min = 1e9
for a in np.linspace(0.05, 0.5, 10):
    for b in np.linspace(1e-4, a - 1e-3, 8):
        for K in (1, 2, 3, 4, 6, 8, 16, 32, 64):
            val, _ = A_K(a, b, K)
            ratio_min = min(ratio_min, val / (length(a, b) ** 2 / (2 * K)))
R.check("A_K(a, b) >= l^2/(2K) for every cooling stroke with 0 < b < a <= 1/2 and K = 1..64", ratio_min >= 1 - 1e-12,
        f"min ratio {ratio_min:.6f}")

# 3. scope
heat1 = A_K(0.1, 0.4, 1)[0] / (length(0.1, 0.4) ** 2 / 2)
above = A_K(0.9, 0.6, 1)[0] / (length(0.9, 0.6) ** 2 / 2)
R.check("outside the scope the factor 1/2 fails: heating 0.1 -> 0.4 and cooling 0.9 -> 0.6 at K = 1",
        heat1 < 1 and above < 1, f"ratios {heat1:.3f}, {above:.3f}")
ratio4 = 1e9
for _ in range(400):
    a, b = rng.uniform(1e-4, 1 - 1e-4, 2)
    if abs(a - b) < 1e-3:
        continue
    K = int(rng.choice([1, 2, 3, 5, 8, 20]))
    ratio4 = min(ratio4, A_K(a, b, K)[0] / (length(a, b) ** 2 / (4 * K)))
R.check("A_K >= l^2/(4K) in every direction (400 random strokes)", ratio4 >= 1 - 1e-9, f"min ratio {ratio4:.4f}")

# 4. summing over strokes, and the contact budget
ok = True
for _ in range(1000):
    m = int(rng.integers(1, 6))
    ls, Ks = rng.uniform(0, 3, m), rng.integers(1, 50, m)
    ok &= np.sum(ls ** 2 / Ks) >= np.sum(ls) ** 2 / np.sum(Ks) - 1e-12
R.check("sum_j l_j^2 / K_j >= (sum_j l_j)^2 / K_tot (Cauchy-Schwarz)", bool(ok))
# the contact budget: shared interface versus separate interfaces, with the same total and with M each
worst_split, worst_cross, beaten = 0.0, 0.0, False
for _ in range(1000):
    LB, LO = rng.uniform(0.1, 3, 2)
    M = float(rng.integers(2, 400))
    shared = (LB + LO) ** 2 / (2 * M)
    KB = M * LB / (LB + LO)
    split = LB ** 2 / (2 * KB) + LO ** 2 / (2 * (M - KB))
    worst_split = max(worst_split, abs(split - shared))
    for KBx in np.linspace(1e-3 * M, (1 - 1e-3) * M, 41):       # no other split of the same total does better
        beaten |= LB ** 2 / (2 * KBx) + LO ** 2 / (2 * (M - KBx)) < shared - 1e-12
    worst_cross = max(worst_cross, abs(shared - (LB ** 2 + LO ** 2) / (2 * M) - LB * LO / M))
R.check("same total M: separate interfaces split L_B : L_O reach (L_B + L_O)^2/(2M), the shared value, and no split "
        "beats it (1000 random cases)", worst_split < 1e-12 and not beaten, f"largest deviation {worst_split:.1e}")
R.check("the difference L_B L_O / M arises only against separate interfaces with M contacts each (2M in all)",
        worst_cross < 1e-12)
LB, LO, M = 2.0, 3.0, 100.0
ex_shared, ex_split = (LB + LO) ** 2 / (2 * M), LB ** 2 / (2 * 40.0) + LO ** 2 / (2 * 60.0)
ex_twice = (LB ** 2 + LO ** 2) / (2 * M)
R.check("example L_B = 2, L_O = 3, M = 100: 0.125 kT shared and split 40:60; 0.065 kT only with 2M = 200 contacts",
        abs(ex_shared - 0.125) < 1e-15 and abs(ex_split - 0.125) < 1e-15 and abs(ex_twice - 0.065) < 1e-15,
        f"{ex_shared:.3f}, {ex_split:.3f}, {ex_twice:.3f}")

# 5. amplitude damping at p = 1/2, beta E = ln 2 (Gibbs excited population 1/3); rates in units of E = kT ln 2
g1 = 1 / 3
res = minimize_scalar(lambda x: -(d(x / 2, g1) - d(x, g1)), bounds=(1e-12, 1), method="bounded", options={"xatol": 1e-14})
T_batch = -res.fun / LN2
online = math.log2(1.5)
R.check("batch rate 0.153640 E at x* = 0.1835, real-time rate log2(3/2) = 0.585 E, order gap 0.431323 E",
        round(T_batch, 6) == 0.153640 and round(res.x, 4) == 0.1835 and round(online - T_batch, 6) == 0.431323,
        f"{T_batch:.6f}, {res.x:.4f}, {online - T_batch:.6f}")

# 6. fit bias (target error 1e-6): a 1/K fit over 4..12 contacts is off by about a tenth of the order cost;
#    adding a 1/K^2 term, or fitting over 10..50 contacts, brings the bias to about one percent
delta = 1e-6
base = online + delta - float(h(delta)) / LN2
W = lambda K: base + A_K(g1, delta, K)[0] / LN2
gap = online - T_batch


def bias(Ks, quad):
    Ks = np.array(Ks, float)
    Ws = np.array([W(int(k)) for k in Ks])
    cols = [np.ones_like(Ks), 1 / Ks] + ([1 / Ks ** 2] if quad else [])
    return (np.linalg.lstsq(np.vstack(cols).T, Ws, rcond=None)[0][0] - base) / gap


b_small, b_small_q, b_large = bias(range(4, 13), False), bias(range(4, 13), True), bias(range(10, 51, 5), False)
R.check("intercept bias: 1/K fit over 4..12 contacts about a tenth of the order cost; with a 1/K^2 term, or over "
        "10..50 contacts, about one percent",
        0.09 <= abs(b_small) <= 0.13 and abs(b_small_q) <= 0.015 and abs(b_large) <= 0.015,
        f"{100 * b_small:+.1f}%, {100 * b_small_q:+.2f}%, {100 * b_large:+.2f}%")

# 7. divergence at fixed K
a1 = [A_K(g1, dl, 1)[0] for dl in (1e-6, 1e-9, 1e-12)]
slope1 = (a1[2] - a1[0]) / math.log(1e6)
a4 = [A_K(g1, dl, 4)[0] / LN2 for dl in (1e-6, 1e-15)]
R.check("one contact: A_1 grows like ln(1/delta)/3; four contacts: the excess grows by under 0.08 E from 1e-6 to 1e-15",
        abs(slope1 - 1 / 3) < 0.01 and 0 < a4[1] - a4[0] < 0.08, f"slope {slope1:.4f}; {a4[0]:.3f} -> {a4[1]:.3f} E")
R.close()
