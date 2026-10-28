"""Zero error and extreme channels (Proposition "At zero error, waiting saves nothing for extreme channels",
Appendix "Zero error and extreme channels").

Checks:
  1. Choi's criterion, exactly: the products A_i^* A_j of the minimal Kraus operators are linearly independent for
     Werner-Holevo (9 products) and for amplitude damping exactly when p != 0 (symbolic p); for tensor powers
     (damping n = 2, 3; Werner-Holevo n = 2) they stay independent, so Phi^{(x)n} is extreme; equivalently
     X -> V^*(I x X)V is injective;
  2. exact dilations with a mixed bath whose branches have orthogonal ranges raise the device entropy by exactly
     S(Phi^c(rho)) on every input, for damping and Werner-Holevo, whatever the bath spectrum; for a non-extreme channel
     (qubit dephasing) a mixed bath does strictly better, so extremality is needed;
  3. a_beta = T_rt: for damping, max over all inputs (coherent included) of S(Phi^c(rho)) + beta/ln2 Tr H(Phi(rho) - rho)
     equals max_{0<=y<=p}[h(y) - beta Delta y/ln 2] (grid of p and beta Delta); for Werner-Holevo a_beta = log2 3;
     at p = 1/2, beta Delta = ln 2 the zero-error rate log2(3/2) = 0.585 Delta, against the batch capacity 0.154 Delta;
  4. entangled inputs give no more: for two uses, random entangled inputs never exceed 2 a_beta.
"""
import itertools
import math

import numpy as np
import sympy as sp
from scipy.optimize import minimize

from qtools import (Report, complementary, entropy, h2, kraus_apply, random_density, random_unitary, stinespring)

R = Report("Zero error and extreme channels")
rng = np.random.default_rng(20261015)


def products_rank_exact(K):
    rows = []
    for A in K:
        for B in K:
            rows.append(list((A.T * B).reshape(1, A.shape[1] ** 2)))      # real Kraus operators here
    return sp.Matrix(rows).rank()


# ---------------------------------------------------------------------------------------------------- 1. extremality
WHs = []
for (i, j) in [(1, 2), (2, 0), (0, 1)]:
    Kk = sp.zeros(3, 3)
    Kk[i, j], Kk[j, i] = 1, -1
    WHs.append(Kk / sp.sqrt(2))
p = sp.symbols("p", positive=True)
ADs = [sp.Matrix([[1, 0], [0, sp.sqrt(1 - p)]]), sp.Matrix([[0, sp.sqrt(p)], [0, 0]])]
prods = [list((A.T * B).reshape(1, 4)) for A in ADs for B in ADs]
detAD = sp.factor(sp.simplify(sp.Matrix(prods).det()))
R.check("Werner-Holevo: the 9 products A_i^* A_j are linearly independent (exact), so W is extreme",
        products_rank_exact(WHs) == 9)
R.check("amplitude damping: the 4 products are linearly independent exactly when p != 0 (determinant = p^2)",
        sp.simplify(detAD - p ** 2) == 0, f"det = {detAD}")


def products_rank_num(K):
    M = np.array([(A.conj().T @ B).reshape(-1) for A in K for B in K])
    return np.linalg.matrix_rank(M, tol=1e-10)


ADn = lambda pv: [np.array([[1, 0], [0, math.sqrt(1 - pv)]]), np.array([[0, math.sqrt(pv)], [0, 0]])]
WHn = [np.array(Kk.evalf(), dtype=float) for Kk in WHs]
tens = lambda K, n: [np.array(1.0).reshape(1, 1)] if n == 0 else [np.kron(a, b) for a in K for b in tens(K, n - 1)]
ok = all(products_rank_num(tens(ADn(pv), n)) == 4 ** n for pv in (0.1, 0.5, 0.9) for n in (1, 2, 3))
ok &= products_rank_num(tens(WHn, 2)) == 81
R.check("tensor powers stay extreme: damping n = 2, 3 (rank 16, 64) and Werner-Holevo n = 2 (rank 81)", bool(ok))
ok = True
for K in (ADn(0.3), WHn):
    V = stinespring(K)
    d, r = K[0].shape[0], len(K)
    cols = []
    for a in range(r):
        for b in range(r):
            Xm = np.zeros((r, r))
            Xm[a, b] = 1
            cols.append((V.conj().T @ np.kron(np.eye(d), Xm) @ V).reshape(-1))
    ok &= np.linalg.matrix_rank(np.array(cols).T, tol=1e-10) == r * r
R.check("X -> V^*(I x X)V is injective for both channels", bool(ok))


# ---------------------------------------------------------------------------------------------------- 2. dilations
def mixed_dilation_rise(K, m, rho, rng):
    """Device entropy rise for a dilation whose bath starts in diag(lambda_1..lambda_m) and whose branch a is
    (I x T_a) V with isometries T_a of orthogonal ranges."""
    V = stinespring(K)
    d, r = K[0].shape[0], len(K)
    De = m * r + int(rng.integers(0, 3))
    Wb = random_unitary(De, rng)
    T = [Wb[:, a * r:(a + 1) * r] for a in range(m)]
    lam = rng.dirichlet(np.ones(m) * rng.uniform(0.2, 3))
    out_dev = np.zeros((De, De), dtype=complex)
    out_sys = np.zeros((d, d), dtype=complex)
    for a in range(m):
        Ua = np.kron(np.eye(d), T[a]) @ V
        st = Ua @ rho @ Ua.conj().T
        t4 = st.reshape(d, De, d, De)
        out_dev += lam[a] * np.einsum("iaib->ab", t4)
        out_sys += lam[a] * np.einsum("aibi->ab", t4)
    return entropy(out_dev) - entropy(np.diag(lam)), out_sys


worst, ok_ch = 0.0, True
for trial in range(300):
    K = ADn(rng.uniform(0.05, 0.95)) if trial % 2 == 0 else WHn
    d = K[0].shape[0]
    rho = random_density(d, rng)
    rise, out = mixed_dilation_rise(K, int(rng.integers(1, 5)), rho, rng)
    worst = max(worst, abs(rise - entropy(complementary(K, rho))))
    ok_ch &= np.allclose(out, kraus_apply(K, rho), atol=1e-12)
R.check("mixed-bath exact dilations raise the device entropy by exactly S(Phi^c(rho)) (300 random dilations and inputs)",
        worst < 1e-9 and ok_ch, f"max deviation {worst:.1e}")
# non-extreme: dephasing (I and Z with weights 1/2) run from a flat bath bit raises the bath entropy by 0
deph = [np.eye(2) / math.sqrt(2), np.diag([1, -1]) / math.sqrt(2)]
rho = np.array([[0.5, 0.4], [0.4, 0.5]])
U = np.kron(np.diag([1, 0]), np.eye(2)) + np.kron(np.diag([0, 1]), np.diag([1, -1]))     # bath bit controls Z
out = U @ np.kron(np.eye(2) / 2, rho) @ U.T
rise = entropy(np.einsum("aibi->ab", out.reshape(2, 2, 2, 2))) - 1
R.check("for a non-extreme channel (dephasing) a flat bath does better than S(Phi^c(rho)): extremality is needed",
        abs(rise) < 1e-12 and entropy(complementary(deph, rho)) > 0.5, f"rise {rise:.1e} vs S(Phi^c) "
        f"{entropy(complementary(deph, rho)):.3f}")


# ---------------------------------------------------------------------------------------------------- 3. a_beta
def bloch(v):
    return 0.5 * np.array([[1 + v[2], v[0] - 1j * v[1]], [v[0] + 1j * v[1], 1 - v[2]]])


def a_beta_damping(pv, bD):
    K = ADn(pv)
    H = np.diag([0, bD])

    def neg(v):
        nv = np.linalg.norm(v)
        r = bloch(v / nv if nv > 1 else v)
        return -(entropy(complementary(K, r)) + np.trace(H @ (kraus_apply(K, r) - r)).real / math.log(2))

    return max(-minimize(neg, rng.uniform(-0.7, 0.7, 3), method="Nelder-Mead",
                         options={"xatol": 1e-11, "fatol": 1e-14, "maxiter": 8000}).fun for _ in range(12))


def t_rt(pv, bD):
    c = bD / math.log(2)
    y = min(pv, 1 / (1 + 2 ** c))
    return h2(y) - c * y


dev = max(abs(a_beta_damping(pv, bD) - t_rt(pv, bD)) for pv in (0.2, 0.5, 0.8, 1.0) for bD in (0.0, math.log(2), 2.0))
R.check("damping: a_beta (all inputs, coherent included) equals the real-time rate max_{y<=p}[h(y) - beta Delta y/ln2]",
        dev < 1e-7, f"max deviation {dev:.1e}")
R.check("Werner-Holevo: a_beta = max S(W(rho)) = log2 3, attained at I/3",
        abs(entropy(kraus_apply(WHn, np.eye(3) / 3)) - math.log2(3)) < 1e-12
        and max(entropy(kraus_apply(WHn, random_density(3, rng))) for _ in range(2000)) <= math.log2(3) + 1e-12)
R.check("p = 1/2, beta Delta = ln 2: zero-error rate log2(3/2) = 0.585 Delta for batch and real time alike",
        abs(a_beta_damping(0.5, math.log(2)) - math.log2(1.5)) < 1e-8)

# ---------------------------------------------------------------------------------------------------- 4. two uses
K2 = tens(ADn(0.5), 2)
H2 = np.kron(np.diag([0, math.log(2)]), np.eye(2)) + np.kron(np.eye(2), np.diag([0, math.log(2)]))
best = -1e9
for _ in range(3000):
    rho = random_density(4, rng, rank=int(rng.integers(1, 5)))
    val = entropy(complementary(K2, rho)) + np.trace(H2 @ (kraus_apply(K2, rho) - rho)).real / math.log(2)
    best = max(best, val)
prod = np.kron(np.diag([1 / 3, 2 / 3]), np.diag([1 / 3, 2 / 3]))
at_prod = entropy(complementary(K2, prod)) + np.trace(H2 @ (kraus_apply(K2, prod) - prod)).real / math.log(2)
R.check("two uses: entangled inputs never exceed 2 a_beta, attained by the product of optimal inputs",
        best <= 2 * math.log2(1.5) + 1e-9 and abs(at_prod - 2 * math.log2(1.5)) < 1e-12, f"best random {best:.6f}")
R.close()
