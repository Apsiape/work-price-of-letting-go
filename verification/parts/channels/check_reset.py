"""Reset and partial reset (Theorem 4.2(b), Figure 4, paragraph "A finite example" and Table 9).

Checks:
  1. amplitude damping: the Kraus operators are trace preserving; the complementary channel is amplitude damping with
     probability 1 - p (exact, symbolic p), invertible as a linear map exactly when p > 0; the natural dilation
     |1>|0> -> sqrt(1-p)|1>|0> + sqrt(p)|0>|1> implements the channel, conserves energy for equal gaps and leaves the
     output entangled with the environment for 0 < p < 1;
  2. S(Phi^c(rho)) <= h(p x) with equality on diagonal inputs (random inputs, many with small coherence), and the
     energy term -beta Delta p x / ln 2;
  3. the real-time formula max_{0<=y<=p}[h(y) - beta Delta y/ln 2] exceeds the batch capacity for 0 < p < 1 at every
     temperature tested, with gap at least I(O:E) at the batch-optimal input (and I(O:E) = h(px) + h((1-p)x) - h(x),
     computed from the dilation), the two agree at p = 1, and the batch maximum is attained on a diagonal input;
  4. max_y [h(y) - c y] is attained at y = 1/(1 + e^{beta Delta}) with value log2(1 + e^{-beta Delta}) (sympy), so the
     real-time cost equals the full-reset cost exactly when p >= 1/(1 + e^{beta Delta}); the batch cost stays below it
     for p < 1 and increases with p; the curves of Figure 4 meet only at p = 0 and p = 1;
  5. the numbers 0.585, 0.154 (0.153640) at p = 1/2, beta Delta = ln 2;
  6. the finite device: the conserving rotation implements damping with p = 1/2; for every row of Table 9 the
     preparation fails exactly on an upper tail (checked shell by shell with exact integers), the exact failure
     probability, the qubit count and the per-use work; the printed error bounds are compared with the exact tails
     rounded up;
  7. the family R = n^2: at n = 1000 an explicit w = n log2(3/2) + O(sqrt(ln n)) from Hoeffding's inequality has
     exact error at most n^-2, and the Hoeffding-sufficient excess over n log2(3/2) stays O(sqrt(ln n)) up to n = 10^6.
"""
from fractions import Fraction
import math

import mpmath as mp
import numpy as np
import sympy as sp
from scipy.optimize import minimize, minimize_scalar

from qtools import Report, complementary, dm, entropy, h2, kraus_apply, mutual_info, ptrace, random_density

R = Report("Reset and partial reset")
rng = np.random.default_rng(20261012)

# ---------------------------------------------------------------------------------------------------- 1. structure
p, x = sp.symbols("p x", positive=True)
K0 = sp.Matrix([[1, 0], [0, sp.sqrt(1 - p)]])
K1 = sp.Matrix([[0, sp.sqrt(p)], [0, 0]])
R.check("Kraus operators |0><0| + sqrt(1-p)|1><1| and sqrt(p)|0><1| are trace preserving (symbolic p)",
        sp.simplify(K0.T * K0 + K1.T * K1 - sp.eye(2)) == sp.zeros(2))
r00, r11 = sp.symbols("r00 r11")
r01 = sp.Symbol("r01")
rho = sp.Matrix([[r00, r01], [sp.conjugate(r01), r11]])
Ks = [K0, K1]
comp = sp.Matrix(2, 2, lambda i, j: sp.simplify((Ks[i] * rho * Ks[j].T).trace()))   # real Kraus operators
ad1mp = sp.Matrix([[r00 + (1 - p) * r11, sp.sqrt(p) * r01], [sp.sqrt(p) * sp.conjugate(r01), p * r11]])
R.check("complementary channel = amplitude damping with probability 1 - p (excited population p x, coherence sqrt(p))",
        sp.simplify(comp - ad1mp) == sp.zeros(2))
# superoperator of the complement on the basis (E00, E01, E10, E11)
cols = []
for (i, j) in [(0, 0), (0, 1), (1, 0), (1, 1)]:
    e = sp.zeros(2)
    e[i, j] = 1
    out = sp.Matrix(2, 2, lambda a, b: (Ks[a] * e * Ks[b].T).trace())
    cols.append([out[0, 0], out[0, 1], out[1, 0], out[1, 1]])
Ssup = sp.Matrix(cols).T
detS = sp.factor(sp.simplify(Ssup.det()))
R.check("the complement is invertible as a linear map exactly when p > 0 (determinant p^2)", sp.simplify(detS - p ** 2) == 0,
        f"det = {detS}")

ok = True
for pv in (0.1, 0.5, 0.9):
    s = math.sqrt(1 - pv)
    U = np.zeros((4, 4))                               # basis |system env>: 00, 01, 10, 11
    U[0, 0] = 1
    U[:, 2] = [0, math.sqrt(pv), s, 0]                 # |10> -> sqrt(1-p)|10> + sqrt(p)|01>
    U[:, 1] = [0, s, -math.sqrt(pv), 0]
    U[3, 3] = 1
    Hse = np.diag([0, 1, 1, 2])
    Kd = [np.array([[1, 0], [0, s]]), np.array([[0, math.sqrt(pv)], [0, 0]])]
    for _ in range(20):
        r = random_density(2, rng)
        out = U @ np.kron(r, dm([1, 0])) @ U.T
        ok &= np.allclose(ptrace(out, [2, 2], [0]), kraus_apply(Kd, r), atol=1e-13)
        ok &= np.allclose(ptrace(out, [2, 2], [1]), complementary(Kd, r), atol=1e-13)
    ok &= np.allclose(U.T @ U, np.eye(4)) and np.allclose(U @ Hse, Hse @ U)
    psi = U[:, 2]
    schmidt = np.linalg.svd(psi.reshape(2, 2), compute_uv=False)
    ok &= abs(schmidt[0] ** 2 - max(pv, 1 - pv)) < 1e-12 and schmidt[1] > 1e-6
R.check("the natural dilation implements damping, its environment output is the complement, it conserves energy, and on "
        "input |1> the output is entangled with the environment (Schmidt rank 2) for 0 < p < 1", bool(ok))

# ---------------------------------------------------------------------------------------------------- 2. s_rho
worst, near = 1e9, 0
for _ in range(3000):
    pv = rng.uniform(0.01, 0.99)
    s = math.sqrt(1 - pv)
    Kd = [np.array([[1, 0], [0, s]]), np.array([[0, math.sqrt(pv)], [0, 0]])]
    r = random_density(2, rng)
    shrink = rng.choice([1.0, 0.1, 0.01, 0.001])
    r = np.diag(np.diag(r)) + shrink * (r - np.diag(np.diag(r)))
    xx = r[1, 1].real
    gap = h2(pv * xx) - entropy(complementary(Kd, r))
    worst = min(worst, gap)
    near += gap < 1e-4
ok_diag = all(abs(entropy(complementary([np.array([[1, 0], [0, math.sqrt(1 - pv)]]), np.array([[0, math.sqrt(pv)], [0, 0]])],
                                         np.diag([1 - xx, xx]))) - h2(pv * xx)) < 1e-12
              for pv in (0.2, 0.5, 0.8) for xx in (0.1, 0.4, 0.9))
R.check("S(Phi^c(rho)) <= h(p x), with equality on diagonal inputs (3000 random inputs)", worst > -1e-12 and near >= 500 and ok_diag,
        f"{near} within 1e-4 of equality, smallest slack {worst:.2e}")
ok = True
for _ in range(200):
    pv, bD = rng.uniform(0, 1), rng.uniform(0, 4)
    s = math.sqrt(1 - pv)
    Kd = [np.array([[1, 0], [0, s]]), np.array([[0, math.sqrt(pv)], [0, 0]])]
    r = random_density(2, rng)
    H = np.diag([0, bD])                               # beta H
    eterm = np.trace(H @ (kraus_apply(Kd, r) - r)).real / math.log(2)
    ok &= abs(eterm + bD * pv * r[1, 1].real / math.log(2)) < 1e-12
R.check("the energy term is -beta Delta p x / ln 2 for every input", bool(ok))


# ---------------------------------------------------------------------------------------------------- 3. formulas
def h_np(v):
    v = np.clip(v, 1e-300, 1)
    w = np.clip(1 - v, 1e-300, 1)
    return -(v * np.log2(v) + w * np.log2(w)) * ((v > 0) & (v < 1))


def t_rt(pv, c):
    """max_{0<=y<=p} [h(y) - c y]; the maximand is concave with unconstrained maximizer 1/(1+2^c)."""
    ystar = 1 / (1 + 2 ** c)
    y = min(pv, ystar)
    return h2(y) - c * y


def t_batch(pv, c):
    f = lambda xx: -(h2(xx) - h2((1 - pv) * xx) - c * pv * xx)
    grid = np.linspace(0, 1, 4001)
    vals = h_np(grid) - h_np((1 - pv) * grid) - c * pv * grid
    i = int(np.argmax(vals))
    lo, hi = grid[max(i - 1, 0)], grid[min(i + 1, len(grid) - 1)]
    res = minimize_scalar(f, bounds=(lo, hi), method="bounded", options={"xatol": 1e-13})
    return -res.fun, res.x


ok_gap, ok_full, ok_mi, n_cases = True, True, True, 0
min_gap = 1e9
for bD in (0.0, 0.3, math.log(2), 1.0, 3.0, 6.0):
    c = bD / math.log(2)
    for pv in np.linspace(0.02, 0.98, 49):
        rt = t_rt(pv, c)
        bt, xs = t_batch(pv, c)
        I_OE = h2(pv * xs) + h2((1 - pv) * xs) - h2(xs)
        ok_gap &= rt - bt >= I_OE - 1e-9 and I_OE > 0 and xs > 0
        min_gap = min(min_gap, rt - bt)
        n_cases += 1
    bt1, _ = t_batch(1.0, c)
    ok_full &= abs(t_rt(1.0, c) - bt1) < 1e-9
# I(O:E) from the dilation equals h(px) + h((1-p)x) - h(x)
for _ in range(50):
    pv, xx = rng.uniform(0.05, 0.95, 2)
    s = math.sqrt(1 - pv)
    U = np.zeros((4, 4))
    U[0, 0] = 1
    U[:, 2] = [0, math.sqrt(pv), s, 0]
    U[:, 1] = [0, s, -math.sqrt(pv), 0]
    U[3, 3] = 1
    out = U @ np.kron(np.diag([1 - xx, xx]), dm([1, 0])) @ U.T
    ok_mi &= abs(mutual_info(out, [2, 2], [0], [1]) - (h2(pv * xx) + h2((1 - pv) * xx) - h2(xx))) < 1e-10
R.check("T_rt > T_cap for 0 < p < 1 at every tested temperature, with gap >= I(O:E) > 0 at the batch-optimal x* > 0",
        bool(ok_gap), f"{n_cases} cases, smallest gap {min_gap:.2e}")
R.check("at the diagonal input the output-environment mutual information is h(px) + h((1-p)x) - h(x)", bool(ok_mi))
R.check("at p = 1 the two costs agree, both max_x [h(x) - beta Delta x / ln 2]", bool(ok_full))

# batch maximum attained on a diagonal input (time covariance), full Bloch ball
def bloch(v):
    return 0.5 * np.array([[1 + v[2], v[0] - 1j * v[1]], [v[0] + 1j * v[1], 1 - v[2]]])


ok = True
for pv, bD in [(0.5, math.log(2)), (0.3, 1.0), (0.8, 0.2), (0.6, 3.0)]:
    s = math.sqrt(1 - pv)
    Kd = [np.array([[1, 0], [0, s]]), np.array([[0, math.sqrt(pv)], [0, 0]])]
    H = np.diag([0, bD])

    def neg(v):
        nv = np.linalg.norm(v)
        if nv > 1:
            v = v / nv
        r = bloch(v)
        o = kraus_apply(Kd, r)
        return -(entropy(r) - entropy(o) + np.trace(H @ (o - r)).real / math.log(2))

    best = max(-minimize(neg, rng.uniform(-0.6, 0.6, 3), method="Nelder-Mead",
                         options={"xatol": 1e-10, "fatol": 1e-13, "maxiter": 6000}).fun for _ in range(15))
    ok &= best <= t_batch(pv, bD / math.log(2))[0] + 1e-8
R.check("the batch maximum over the whole Bloch ball equals the maximum over diagonal inputs", bool(ok))

# ---------------------------------------------------------------------------------------------------- 4. full reset
y, c = sp.symbols("y c", positive=True)
F = -y * sp.log(y, 2) - (1 - y) * sp.log(1 - y, 2) - c * y / sp.log(2)          # c = beta Delta
ystar = 1 / (1 + sp.exp(c))
R.check("d/dy [h(y) - beta Delta y/ln 2] vanishes at y = 1/(1 + e^{beta Delta}) and the value is log2(1 + e^{-beta Delta})",
        sp.simplify(sp.diff(F, y).subs(y, ystar)) == 0
        and sp.simplify(sp.expand_log(F.subs(y, ystar) - sp.log(1 + sp.exp(-c), 2), force=True)) == 0
        and sp.simplify(sp.diff(F, y, 2)) .subs({y: sp.Rational(1, 3), c: 1}) < 0)
ok_sat, ok_below, ok_incr = True, True, True
for bD in (0.0, 0.5, 1.0, 3.0):
    cc = bD / math.log(2)
    full = math.log2(1 + math.exp(-bD))
    pthr = 1 / (1 + math.exp(bD))
    ps = np.linspace(0, 1, 201)
    rts = [t_rt(pv, cc) for pv in ps]
    bts = [t_batch(pv, cc)[0] for pv in ps]
    ok_sat &= all(abs(rv - full) < 1e-12 for pv, rv in zip(ps, rts) if pv >= pthr)
    ok_sat &= all(rv < full - 1e-12 for pv, rv in zip(ps, rts) if pv < pthr - 1e-9)
    ok_below &= all(bv < full - 1e-9 for pv, bv in zip(ps, bts) if pv < 1) and abs(bts[-1] - full) < 1e-9
    ok_incr &= all(b2 > b1 for b1, b2 in zip(bts, bts[1:]))
    ok_below &= all(rv >= bv - 1e-12 for rv, bv in zip(rts, bts)) and all(rv - bv > 1e-6 for rv, bv in zip(rts[1:-1], bts[1:-1]))
R.check("the real-time cost equals the full-reset cost log2(1 + e^{-beta Delta}) exactly when p >= 1/(1 + e^{beta Delta})",
        bool(ok_sat))
R.check("the batch cost increases with p and reaches the full-reset cost only at p = 1", bool(ok_incr and ok_below))
R.check("Figure 4 (beta Delta = 0, 1, 3 and others): real time above batch, the curves meet only at p = 0 and p = 1",
        bool(ok_below))

# ---------------------------------------------------------------------------------------------------- 5. numbers
rt = t_rt(0.5, 1.0)
bt, xb = t_batch(0.5, 1.0)
R.check("p = 1/2, beta Delta = ln 2: real time log2(3/2) = 0.585 Delta, batch 0.153640 = 0.154 Delta",
        abs(rt - math.log2(1.5)) < 1e-12 and round(rt, 3) == 0.585 and round(bt, 6) == 0.153640 and round(bt, 3) == 0.154,
        f"{rt:.6f}, {bt:.6f} at x* = {xb:.4f}")

# ---------------------------------------------------------------------------------------------------- 6. finite device
s2 = sp.sqrt(2)
Urot = sp.Matrix([[1, 0, 0, 0], [0, 1 / s2, 1 / s2, 0], [0, -1 / s2, 1 / s2, 0], [0, 0, 0, 1]])   # |input memory>
Hcm = sp.diag(0, 1, 1, 2)
Kr = [sp.Matrix(2, 2, lambda o, i: Urot[2 * o + m, 2 * i]) for m in range(2)]
R.check("the conserving rotation |10> -> (|10> + |01>)/sqrt2 is unitary, conserves energy and implements damping "
        "with p = 1/2 on a ground-state memory",
        sp.simplify(Urot.T * Urot - sp.eye(4)) == sp.zeros(4) and sp.simplify(Urot * Hcm - Hcm * Urot) == sp.zeros(4)
        and sp.simplify(Kr[0] - sp.diag(1, 1 / s2)) == sp.zeros(2) and sp.simplify(Kr[1] - sp.Matrix([[0, 1 / s2], [0, 0]])) == sp.zeros(2))


def factory(Rr, n, w):
    """Walk the shells k = 0..R+n of the pool with exact integers. Returns (first bad shell, whether the bad set is an
    upper tail, exact failure probability P[Bin(R+n, 1/3) >= first bad shell])."""
    S = Rr + n
    cS = 1                                    # C(S, k)
    cR = math.comb(Rr, w) if w <= Rr else 0   # C(R, k + w)
    first_bad, upper = None, True
    pw = 1 << S                               # 2^(S - k)
    num = 0
    for k in range(S + 1):
        bad = cR < cS
        if bad and first_bad is None:
            first_bad = k
        if first_bad is not None:
            upper &= bad
            num += cS * pw
        if k < S:
            cS = cS * (S - k) // (k + 1)
            kk = k + w
            cR = cR * (Rr - kk) // (kk + 1) if kk < Rr else 0
            pw >>= 1
    return first_bad, upper, Fraction(num, 3 ** S)


TABLE = [  # (reservoir R, qubits, work w, per use, error at most) as printed in Table 9
    (2000, 2208, 118, "1.18", "0.00999"),
    (10000, 10208, 70, "0.70", "0.00548"),
    (50000, 50208, 63, "0.63", "0.00156"),
]
n = 100
counter = math.ceil(math.log2(n + 2))
for Rr, qubits, w, per_use, err in TABLE:
    kb, upper, f = factory(Rr, n, w)
    exp10 = math.floor(math.log10(float(f)))          # rounded up to three significant figures
    q = Fraction(1, 10 ** (2 - exp10))
    rounded_up = math.ceil(f / q) * q
    R.check(f"R = {Rr}, w = {w}: the preparation fails exactly on the upper tail k >= {kb} of Bin(R+n, 1/3)", upper and kb is not None)
    R.check(f"R = {Rr}: qubits R + 2n + {counter} + 1 = {qubits}, per use {per_use} Delta",
            Rr + 2 * n + counter + 1 == qubits and f"{w / n:.2f}" == per_use)
    R.check(f"R = {Rr}, w = {w}: exact failure probability is at most the printed {err}", f <= Fraction(err),
            f"exact {float(f):.12f}, rounded up {float(rounded_up):.3g}")

# ---------------------------------------------------------------------------------------------------- 7. the family
def hoeffding_w(nn):
    """Least w for which the shell k_max = floor((R+n)/3 + sqrt((R+n) ln n)) is good, R = n^2 (log-gamma, 60 digits);
    every shell up to k_max is then good, and Hoeffding bounds the failure by exp(-2 d^2/(R+n)) = n^-2."""
    mp.mp.dps = 60
    Rr = nn * nn
    S = Rr + nn
    kmax = int(mp.floor(mp.mpf(S) / 3 + mp.sqrt(S * mp.log(nn))))
    lc = lambda a, b: mp.loggamma(a + 1) - mp.loggamma(b + 1) - mp.loggamma(a - b + 1)
    target = lc(S, kmax)
    w = int(nn * math.log2(1.5))
    while lc(Rr, kmax + w) < target:
        w += 1
    return w, kmax


def tail_upper(Rr, n, w):
    """First bad shell by bisection (the bad set is an upper tail: Lean, FiniteDevice.bad_succ) and a rigorous upper
    bound on P[Bin(R+n, 1/3) >= it]: exact partial sum plus a geometric bound on the remainder, since the term ratio
    (S-k)/(2(k+1)) decreases in k."""
    S = Rr + n
    bad = lambda k: (math.comb(Rr, k + w) if k + w <= Rr else 0) < math.comb(S, k)
    lo, hi = 0, S
    if bad(0):
        hi = 0
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (lo, mid) if bad(mid) else (mid, hi)
    k = hi
    term = math.comb(S, k) << (S - k)
    num = 0
    while True:
        num += term
        a, b = S - k, 2 * (k + 1)
        if a < b and term * a * 10 ** 40 <= num * (b - a):       # remainder <= term a/(b-a) <= 1e-40 of the sum
            return k, Fraction(num, 3 ** S), Fraction(num + term * a // (b - a) + 1, 3 ** S)
        term = term * a // b
        k += 1


nn = 1000
w1000, kmax = hoeffding_w(nn)
assert math.comb(nn * nn, kmax + w1000) >= math.comb(nn * nn + nn, kmax)
kb, f_lo, f_hi = tail_upper(nn * nn, nn, w1000)
R.check("n = 1000, R = n^2: an explicit w = n log2(3/2) + O(sqrt(ln n)) gives exact error at most n^-2",
        kb > kmax and f_hi <= Fraction(1, nn * nn),
        f"w = {w1000} = n log2(3/2) + {w1000 - nn * math.log2(1.5):.1f}, error <= {float(f_hi):.2e}")
ratios = []
for nn in (1000, 3000, 10000, 30000, 100000, 300000, 1000000):
    wv, _ = hoeffding_w(nn)
    ratios.append((wv - nn * math.log2(1.5)) / math.sqrt(math.log(nn)))
R.check("the Hoeffding-sufficient excess over n log2(3/2), divided by sqrt(ln n), stays bounded for n = 10^3 .. 10^6",
        max(ratios) < 15 and max(ratios) / min(ratios) < 1.5, ", ".join(f"{r_:.2f}" for r_ in ratios))
R.close()
