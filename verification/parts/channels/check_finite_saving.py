"""A finite saving at 234 and 256 uses (Section 4, paragraph "A finite saving", with Appendix "Invertible environments").

Amplitude damping with p = 1/2 on H = Delta|1><1| at beta Delta = ln 2, so that one bit of work is one Delta.

Checks:
  1. the complement is again damping with p = 1/2; its inverse Y -> [[Y00 - Y11, sqrt2 Y01], [sqrt2 Y10, 2 Y11]] has
     diamond norm exactly 3: an exact upper certificate (Choi decomposition with Tr_out(P + N) = diag(1, 3)), an exact
     lower witness (input |1><1|), and an independent SDP;
  2. the real-time bound of eq. (converse) with the estimate of Appendix "Invertible environments" at the input with
     excited population x = 16/25, error 1e-8 and the three budgets of 1e-5:
        W/Delta >= n [h(x/2) - x/2 - eps - g_4(t)] - 3e-5,   t = sqrt(2 eps)(1 + 3/min(x, 1 - x)),
     evaluated with two engines (exact rationals with certified series bounds, and 60-digit mpmath): above 132.109 at
     n = 234 and 144.53 at n = 256;
  3. the batch construction: w = 137 (resp. 150) is the least integer with 2^w >= (3/2)^n, so preparing n pure
     environment qubits costs w Delta; a refund of r = 5 (resp. 11) Delta from 2^r positions is the largest whose
     decoding error stays within the budget; the nominal work is 132 Delta (resp. 139 Delta), the error is below
     8.71e-9, and the saving at 256 uses exceeds 5.5 Delta. The decoder error is computed from the structure checked in
     item 4: the position decoder accepts the true position with certainty and a wrong one with probability at most
     (5/6)^n, so by the Hayashi-Nagaoka inequality the infidelity is at most 4 (L - 1) (5/6)^n and the trace-distance
     error at most sqrt(8 L (5/6)^n); the formation of the pure qubits fails with probability 1e-12 (a ladder of 10^12
     tiles). These formulas are those of the construction behind the paragraph; the manuscript quotes only the result;
  4. the one-use structure: the support projector P1 of output and used environment commutes with the energy and
     Tr_M[(I x gamma) P1] = diag(5/6, 1/3) exactly; and the Hayashi-Nagaoka operator inequality on random instances.
"""
from fractions import Fraction
import math

import mpmath as mp
import numpy as np
import sympy as sp

from qtools import (Report, choi_of_map, diamond_norm_herm, h2_bounds, log2_bounds, msqrt, random_density, sqrt_bounds)

R = Report("A finite saving")
rng = np.random.default_rng(20261013)

# ---------------------------------------------------------------------------------------------------- 1. M = 3
s2 = sp.sqrt(2)


def inv_ad(Yv):
    return sp.Matrix([[Yv[0, 0] - Yv[1, 1], s2 * Yv[0, 1]], [s2 * Yv[1, 0], 2 * Yv[1, 1]]])


def ad_half(Yv):
    return sp.Matrix([[Yv[0, 0] + Yv[1, 1] / 2, Yv[0, 1] / s2], [Yv[1, 0] / s2, Yv[1, 1] / 2]])


E = lambda i, j: sp.Matrix(2, 2, lambda a, b: 1 if (a, b) == (i, j) else 0)
R.check("the complement of damping with p = 1/2 is damping with p = 1/2, and the stated map inverts it",
        all(sp.simplify(inv_ad(ad_half(E(i, j))) - E(i, j)) == sp.zeros(2) for i in range(2) for j in range(2)))
J = sp.zeros(4)
for i in range(2):
    for j in range(2):
        J += sp.kronecker_product(E(i, j), inv_ad(E(i, j)))
ev = J.eigenvals()
# exact upper certificate: J = P - N with P, N >= 0 from the spectral decomposition, Tr_out(P + N) = Tr_out|J|
Pm, Dg = J.diagonalize(normalize=True)
absJ = sp.simplify(Pm * sp.diag(*[abs(d) for d in Dg.diagonal()]) * Pm.T)
TrO = sp.Matrix(2, 2, lambda a, b: sp.simplify(sum(absJ[2 * a + k, 2 * b + k] for k in range(2))))
upper = max(TrO.eigenvals().keys())
lower = sum(abs(v) for v in inv_ad(E(1, 1)).eigenvals().keys())
Jn = np.array(J.evalf(), dtype=complex)
sdp = diamond_norm_herm(Jn, 2, 2)
R.check("||(Phi^c)^{-1}||_diamond = 3: Choi spectrum {3, 0, 0, -1}, Tr_out|J| = diag(1, 3), witness |1><1| -> trace norm 3",
        ev == {3: 1, 0: 2, -1: 1} and TrO == sp.diag(1, 3) and upper == 3 and lower == 3 and abs(sdp - 3) < 1e-6,
        f"SDP {sdp:.8f}")

# ---------------------------------------------------------------------------------------------------- 2. bound
EPS = Fraction(1, 10 ** 8)
BUDGET = 3 * Fraction(1, 10 ** 5)
X0 = Fraction(16, 25)
M = 3


def rt_bound_rational(n, x=X0, eps=EPS, budget=BUDGET, D=4):
    """Certified lower bound (exact rationals; logarithms from atanh series with tail bounds)."""
    lam = min(x, 1 - x)
    _, shi = sqrt_bounds(2 * eps)
    thi = shi * (1 + Fraction(M) / lam)
    assert thi <= 1
    # g_D is increasing in t, so an upper bound at thi bounds g_D(t)
    q = thi / (1 + thi)
    g_hi = 2 * thi * log2_bounds(D)[1] + (1 + thi) * h2_bounds(q)[1]
    per = h2_bounds(x / 2)[0] - x / 2 - eps - g_hi
    return n * per - budget


def rt_bound_mp(n, x=X0, eps=EPS, budget=BUDGET, D=4):
    mp.mp.dps = 60
    x, eps, budget = mp.mpf(x.numerator) / x.denominator, mp.mpf(eps.numerator) / eps.denominator, \
        mp.mpf(budget.numerator) / budget.denominator
    h = lambda q: -(q * mp.log(q, 2) + (1 - q) * mp.log(1 - q, 2))
    t = mp.sqrt(2 * eps) * (1 + M / min(x, 1 - x))
    g = 2 * t * mp.log(D, 2) + (1 + t) * h(t / (1 + t))
    return n * (h(x / 2) - x / 2 - eps - g) - budget


b234, b256 = rt_bound_rational(234), rt_bound_rational(256)
m234, m256 = rt_bound_mp(234), rt_bound_mp(256)
R.check("two engines agree on the real-time bound to 1e-25", abs(float(b234) - float(m234)) < 1e-9
        and abs(mp.mpf(b234.numerator) / b234.denominator - m234) < mp.mpf(10) ** -25
        and abs(mp.mpf(b256.numerator) / b256.denominator - m256) < mp.mpf(10) ** -25,
        f"n=234: {mp.nstr(m234, 18)}, n=256: {mp.nstr(m256, 18)}")
R.check("every real-time implementation of 234 uses has nominal work above 132.109 Delta", b234 > Fraction(132109, 1000),
        f"certified lower bound {float(b234):.9f}")
R.check("at 256 uses the real-time bound is 144.53 Delta (certified >= 144.53)", Fraction(14453, 100) <= b256 < Fraction(14454, 100),
        f"{float(b256):.9f}")
xs = np.linspace(0.55, 0.75, 2001)
best = max(float(rt_bound_mp(234, Fraction(xv).limit_denominator(10 ** 6))) for xv in xs[::20])
R.check("x = 16/25 is within 1e-3 Delta of the best input for this bound at n = 234", best - float(b234) < 1e-3,
        f"best on a grid {best:.6f}")

# ---------------------------------------------------------------------------------------------------- 3. batch
T_TILES = 10 ** 12                  # formation failure 1/T


def batch(n, eps=EPS):
    w = 0
    while 2 ** (w + n) < 3 ** n:    # 2^w >= (3/2)^n
        w += 1
    cap = (eps - Fraction(1, T_TILES)) ** 2
    r = 0
    while 8 * 2 ** (r + 1) * Fraction(5, 6) ** n <= cap:
        r += 1
    p = 8 * 2 ** r * Fraction(5, 6) ** n
    _, dhi = sqrt_bounds(p, 40)
    return w, r, w - r, Fraction(1, T_TILES) + dhi, p <= cap


w, r, nom, err, okcap = batch(234)
R.check("n = 234: w = 137 is the least integer with 2^w >= (3/2)^234, so 234 pure qubits cost 137 Delta",
        w == 137 and 2 ** (137 + 234) >= 3 ** 234 > 2 ** (136 + 234))
R.check("n = 234: the largest admissible refund uses 32 = 2^5 positions (a five-qubit register) and returns 5 Delta",
        r == 5 and okcap and 2 ** r == 32)
R.check("n = 234: nominal work 137 - 5 = 132 Delta, below the real-time bound 132.109 Delta", nom == 132 and nom < b234)
R.check("n = 234: error below 8.71e-9", err < Fraction(871, 10 ** 11), f"error <= {float(err):.10e}")
w6, r6, nom6, err6, okcap6 = batch(256)
R.check("n = 256: w = 150, refund 11 Delta, nominal 139 Delta, saving above 5.5 Delta",
        (w6, r6, nom6) == (150, 11, 139) and okcap6 and b256 - nom6 > Fraction(55, 10) and err6 <= EPS,
        f"saving >= {float(b256 - nom6):.6f}")
R.check("the real-time rate log2(3/2) = 0.585 Delta per use (the batch rate 0.154 is checked in check_reset.py); "
        "n log2(3/2) exceeds the batch nominal work at both sizes",
        round(math.log2(1.5), 3) == 0.585 and 234 * math.log2(1.5) > 132 and 256 * math.log2(1.5) > 139)

# ---------------------------------------------------------------------------------------------------- 4. structure
k = lambda *v: sp.Matrix(v)
bplus = (k(0, 1, 0, 0) + k(0, 0, 1, 0)) / s2              # basis |O M>: 00, 01, 10, 11
P1 = k(1, 0, 0, 0) * k(1, 0, 0, 0).T + bplus * bplus.T
gam = sp.diag(sp.Rational(2, 3), sp.Rational(1, 3))
Xm = sp.kronecker_product(sp.eye(2), gam) * P1
TrM = sp.Matrix(2, 2, lambda a, c: sp.simplify(sum(Xm[2 * a + m, 2 * c + m] for m in range(2))))
HOM = sp.diag(0, 1, 1, 2)
Ur = sp.Matrix([[1, 0, 0, 0], [0, 1 / s2, 1 / s2, 0], [0, -1 / s2, 1 / s2, 0], [0, 0, 0, 1]])   # |input env>
out_support = sp.simplify(Ur * sp.diag(1, 0, 1, 0) * Ur.T)        # image of inputs with a ground environment
R.check("P1 is the support projector of output and environment after one use, commutes with the energy, and "
        "Tr_M[(I x gamma) P1] = diag(5/6, 1/3), so a wrong position is accepted with probability <= (5/6)^n",
        sp.simplify(out_support - P1) == sp.zeros(4) and sp.simplify(P1 * HOM - HOM * P1) == sp.zeros(4)
        and TrM == sp.diag(sp.Rational(5, 6), sp.Rational(1, 3)))
worst = 1e9
for _ in range(300):
    d, L = int(rng.integers(2, 6)), int(rng.integers(2, 5))
    Lam = []
    for _ in range(L):
        A = random_density(d, rng, rank=int(rng.integers(1, d + 1)))
        A = A / np.linalg.eigvalsh(A).max() * rng.uniform(0.3, 1)
        Lam.append(A)
    S = sum(Lam)
    w_, v_ = np.linalg.eigh(S)
    inv = (v_ * np.array([1 / math.sqrt(x) if x > 1e-12 else 0 for x in w_])) @ v_.conj().T
    for j in range(L):
        Om = inv @ Lam[j] @ inv
        G = 2 * (np.eye(d) - Lam[j]) + 4 * (S - Lam[j]) - (np.eye(d) - Om)
        worst = min(worst, np.linalg.eigvalsh((G + G.conj().T) / 2).min())
R.check("Hayashi-Nagaoka: I - Omega_j <= 2(I - Lambda_j) + 4 sum_{l != j} Lambda_l (300 random families)", worst > -1e-10,
        f"smallest eigenvalue {worst:.2e}")
R.close()
