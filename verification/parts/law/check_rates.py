"""Rates quoted in the keystone (Sections "What waiting buys" and "Returning a clock", Table "corollaries").

Checks:
  1. amplitude damping, p = 1/2, beta E = ln 2: the real-time optimum sits at decay mass y = 1/3 (input excited
     population 2/3), where the least mutual information is m = h2(1/3) = 0.918 bits; coherent inputs do not raise the
     batch rate 0.153640;
  2. X-dephasing on H = E|1><1|: thermodynamic capacity beta^{-1} ln cosh(beta E/2), below E/2, with
     E/2 - capacity = beta^{-1} ln(2/(1 + e^{-beta E}));
  3. the qutrit pair: the two stated equations have a positive solution t = 1.02099, z = 0.16236 giving
     c = ln(1+z) + (1/2) ln(3/2)(t-1) = 0.15471030022, and c equals the maximum of the three-variable objective.
"""
import math

import mpmath as mp
import numpy as np
from scipy.optimize import minimize

from qtools import Report, h2

R = Report("Rates quoted in the keystone")
rng = np.random.default_rng(5)


def vn(rho):
    w = np.linalg.eigvalsh(rho)
    w = w[w > 1e-15]
    return float(-np.sum(w * np.log(w)))


def relent(r, s):
    w, v = np.linalg.eigh(s)
    logs = v @ np.diag(np.log(w)) @ v.conj().T
    return float(-vn(r) - np.trace(r @ logs).real)


def bloch(x, y, z):
    return 0.5 * np.array([[1 + z, x - 1j * y], [x + 1j * y, 1 - z]])


# 1. amplitude damping
p = 0.5
y = np.linspace(0, p, 200001)
val = np.array([h2(t) for t in y]) - y          # h(y) - beta E y / ln 2 with beta E = ln 2
R.check("real-time optimum at decay mass y = 1/3, value log2(3/2)", abs(y[np.argmax(val)] - 1 / 3) < 1e-5
        and abs(val.max() - math.log2(1.5)) < 1e-9)
x = 2 / 3
m = h2(p * x) - (h2(x) - h2((1 - p) * x))
R.check("at that input the least mutual information is m = h2(1/3) = 0.918 bits", abs(m - h2(1 / 3)) < 1e-12 and round(m, 3) == 0.918,
        f"{m:.6f}")
gam = np.diag([2 / 3, 1 / 3])
K0, K1 = np.array([[1, 0], [0, math.sqrt(1 - p)]]), np.array([[0, math.sqrt(p)], [0, 0]])
AD = lambda r: K0 @ r @ K0.T + K1 @ r @ K1.T
best = -1e9
for _ in range(20000):
    v = rng.standard_normal(3)
    v *= rng.uniform(0, 1) ** (1 / 3) / np.linalg.norm(v)
    r = bloch(*v)
    best = max(best, relent(AD(r), gam) - relent(r, gam))
R.check("coherent inputs do not raise the batch rate above 0.153640 E", best / math.log(2) <= 0.153640 + 1e-6,
        f"best sampled {best / math.log(2):.6f}")

# 2. X-dephasing
ok = True
for bE in (0.3, math.log(2), 1.0, 2.5):
    gx = np.diag([1, math.exp(-bE)]) / (1 + math.exp(-bE))
    PX = lambda r: 0.5 * (r + np.array([[0, 1], [1, 0]]) @ r @ np.array([[0, 1], [1, 0]]))
    obj = lambda v: -(relent(PX(bloch(*v)), gx) - relent(bloch(*v), gx))
    res = min((minimize(obj, rng.uniform(-0.5, 0.5, 3), constraints=[{"type": "ineq", "fun": lambda v: 0.999999 - v @ v}])
               for _ in range(12)), key=lambda r_: r_.fun)
    cap = -res.fun                                   # in units of kT (beta = 1)
    ok &= abs(cap - math.log(math.cosh(bE / 2))) < 1e-5 and cap < bE / 2
    ok &= abs(bE / 2 - math.log(math.cosh(bE / 2)) - math.log(2 / (1 + math.exp(-bE)))) < 1e-12
R.check("X-dephasing capacity is beta^{-1} ln cosh(beta E/2) < E/2, and E/2 - capacity = beta^{-1} ln(2/(1+e^{-beta E}))", bool(ok))

# 3. the qutrit pair
mp.mp.dps = 40
f1 = lambda t, z: 12 * z ** 2 * (1 + z) * mp.mpf(1.5) ** (t - 1) - z - t ** 2 / 5
f2 = lambda t, z: (1 + z) ** 5 - 3 * mp.mpf(0.8) ** 4 * (mp.mpf(1) / 5 + z / t ** 2) * mp.mpf(1.5) ** (4 + mp.mpf(5) / 2 * (1 / t - t))
t, z = mp.findroot([f1, f2], (mp.mpf("1.02"), mp.mpf("0.16")))
c = mp.log(1 + z) + mp.log(mp.mpf(1.5)) / 2 * (t - 1)
R.check("the equations give t = 1.02099, z = 0.16236 and c = 0.15471030022",
        mp.nstr(t, 6) == "1.02099" and mp.nstr(z, 5) == "0.16236" and mp.nstr(c, 11) == "0.15471030022",
        f"t={mp.nstr(t, 8)}, z={mp.nstr(z, 8)}, c={mp.nstr(c, 15)}")
a, b = math.log(1.5), math.log(3)
H = lambda *ps: -sum(q * math.log(q) for q in ps if q > 0)


def objective(v):
    pp, qq = v
    rr = 1 - pp - qq
    if min(pp, qq, rr) <= 0:
        return 1e9
    return -(-a / 2 * pp + (3 * a / 10 + b / 5) * qq - b / 2 * rr + a * math.sqrt(pp * qq)
             + H(pp, qq, rr) - H(pp + rr / 2, 4 * qq / 5, qq / 5 + rr / 2))


res = min((minimize(objective, rng.dirichlet(np.ones(3))[:2], method="Nelder-Mead",
                    options={"xatol": 1e-13, "fatol": 1e-15, "maxiter": 20000}) for _ in range(20)), key=lambda r_: r_.fun)
R.check("c is the maximum of the three-variable objective for B(N)/kT", abs(-res.fun - float(c)) < 1e-9,
        f"direct maximum {-res.fun:.12f}")
pp, qq = res.x
R.check("the maximizer gives t = sqrt(q/p) and z = r/(2p) as in the equations",
        abs(math.sqrt(qq / pp) - float(t)) < 1e-4 and abs((1 - pp - qq) / (2 * pp) - float(z)) < 1e-4)
R.close()
