"""The Werner-Holevo channel (Theorems 4.2(c) and G.3, Appendix G.4, "The Werner-Holevo support test", and the numbers of Appendix G.7).

Checks:
  1. exact identities (sympy, integers after scaling by sqrt2): V|i> = sum_jk eps_ijk |j>|k>/sqrt2 is an isometry with
     VV^* = P_- (the antisymmetric projector); tracing out either factor gives W(rho) = (Tr rho I - rho^T)/2, so W is
     its own complement; the Choi state is P_-/3; W^{-1}(Y) = Tr(Y) I - 2 Y^T inverts W and fixes I/3;
  2. ||W^{-1}||_diamond <= 9 (SDP value, and the two pieces Tr(.)I and the transpose have diamond norm 3 each);
  3. the exact real-time device that applies V with one pure qutrit per round raises the device entropy by exactly
     log2 3 per round on Bell-pair inputs and triples its rank every round (n = 1, 2, 3); W^{(x)2} is invertible;
  4. the support test (Proposition in Appendix G) on 600 random real-time rounds of perturbed implementations with
     random initial device states: the gentle-measurement step, ||sigma - J_W x beta_F||_1 <= 20 sqrt(delta), and
     S(QO|F) >= log2 3 - g_9(min{1, 10 sqrt(delta)}) and >= 0, with many rounds in the informative range;
  5. delta -> [log2 3 - g_9(min{1, 10 sqrt delta})]_+ is convex on [0, 1] (so the averaged form follows by Jensen);
  6. the numbers: the bound is informative only for delta below about 2e-4, within ten percent of log2 3 only near
     delta = 1e-6; at error n^-2 the bound is n log2 3 - O(log n); the batch free energy 6 log2 n + O(1).
"""
import itertools
import math

import numpy as np
import sympy as sp

from qtools import (Report, choi_of_map, cond_entropy, diamond_norm_herm, dm, entropy, g_afw, near_unitary, ptrace,
                    random_density, random_unitary, trace_norm)

R = Report("Werner-Holevo channel")
rng = np.random.default_rng(20261014)
LOG3 = math.log2(3)

# ---------------------------------------------------------------------------------------------------- 1. exact
eps3 = lambda i, j, k: sp.LeviCivita(i, j, k)
V2 = sp.zeros(9, 3)                                  # sqrt2 V, rows |j k>
for i, j, k in itertools.product(range(3), repeat=3):
    V2[3 * j + k, i] = eps3(i, j, k)
SWAP = sp.zeros(9, 9)
for a, b in itertools.product(range(3), repeat=2):
    SWAP[3 * b + a, 3 * a + b] = 1
Pminus = (sp.eye(9) - SWAP) / 2
R.check("sqrt2 V has integer entries eps_ijk, (sqrt2 V)^T (sqrt2 V) = 2 I and V V^* = P_-",
        V2.T * V2 == 2 * sp.eye(3) and V2 * V2.T / 2 == Pminus)


def trO(Mx):       # trace out the first factor of C^3 (x) C^3
    return sp.Matrix(3, 3, lambda b, d: sum(Mx[3 * a + b, 3 * a + d] for a in range(3)))


def trE(Mx):
    return sp.Matrix(3, 3, lambda a, c: sum(Mx[3 * a + b, 3 * c + b] for b in range(3)))


def W(Yv):
    return (Yv.trace() * sp.eye(3) - Yv.T) / 2


def Winv(Yv):
    return Yv.trace() * sp.eye(3) - 2 * Yv.T


Eij = lambda i, j: sp.Matrix(3, 3, lambda a, b: 1 if (a, b) == (i, j) else 0)
ok_comp = all(trE(V2 * Eij(i, j) * V2.T / 2) == W(Eij(i, j)) and trO(V2 * Eij(i, j) * V2.T / 2) == W(Eij(i, j))
              for i in range(3) for j in range(3))
R.check("tracing out either output factor of V gives W(rho) = (Tr rho I - rho^T)/2: W is its own complement", ok_comp)
choi = sp.zeros(9, 9)
for i in range(3):
    for j in range(3):
        choi += sp.kronecker_product(Eij(i, j), W(Eij(i, j))) / 3
R.check("the Choi state (id x W)(Omega) is the normalized antisymmetric projector P_-/3", choi == Pminus / 3)
R.check("W^{-1}(Y) = Tr(Y) I - 2 Y^T inverts W, and W^{-1}(I/3) = I/3",
        all(Winv(W(Eij(i, j))) == Eij(i, j) and W(Winv(Eij(i, j))) == Eij(i, j) for i in range(3) for j in range(3))
        and Winv(sp.eye(3) / 3) == sp.eye(3) / 3)
Kraus = []
for (i, j) in [(1, 2), (2, 0), (0, 1)]:
    Kk = np.zeros((3, 3))
    Kk[i, j], Kk[j, i] = 1 / math.sqrt(2), -1 / math.sqrt(2)
    Kraus.append(Kk)
Wn = lambda r: (np.trace(r) * np.eye(3) - r.T) / 2
R.check("Kraus form (|i><j| - |j><i|)/sqrt2 gives the same channel",
        all(np.allclose(sum(Kk @ r @ Kk.T for Kk in Kraus), Wn(r)) for r in (random_density(3, rng) for _ in range(20))))

# ---------------------------------------------------------------------------------------------------- 2. norms
Winv_n = lambda Yv: np.trace(Yv) * np.eye(3) - 2 * Yv.T
dn = diamond_norm_herm(choi_of_map(Winv_n, 3), 3, 3)
dtr = diamond_norm_herm(choi_of_map(lambda Yv: np.trace(Yv) * np.eye(3), 3), 3, 3)
dT = diamond_norm_herm(choi_of_map(lambda Yv: Yv.T, 3), 3, 3)
R.check("||W^{-1}||_diamond <= 3 + 2*3 = 9 (Tr(.)I and the transpose each have diamond norm 3)",
        dn <= 9 + 1e-6 and abs(dtr - 3) < 1e-6 and abs(dT - 3) < 1e-6, f"SDP value {dn:.6f}")

# ---------------------------------------------------------------------------------------------------- 3. exact device
Ufull = np.zeros((9, 9))                    # S (x) E_in -> O (x) E_out, with |i>|0> -> V|i>
Vn = np.array(V2.evalf(), dtype=float) / math.sqrt(2)
cols = {3 * i: Vn[:, i] for i in range(3)}
basis = [cols[c] for c in sorted(cols)]
comp = np.linalg.svd(np.eye(9) - sum(np.outer(b, b) for b in basis))[0][:, :6]
Ufull[:, [0, 3, 6]] = Vn
Ufull[:, [1, 2, 4, 5, 7, 8]] = comp
ok = np.allclose(Ufull.T @ Ufull, np.eye(9))
phi = sum(np.kron(np.eye(3)[i], np.eye(3)[i]) for i in range(3)) / math.sqrt(3)
for n in (1, 2, 3):
    state = np.array([1.0])
    dims = []
    for t in range(n):                       # append Q_t, S_t, E_t (E_t pure |0>)
        state = np.kron(np.kron(state, phi), np.eye(3)[0])
        dims += [3, 3, 3]
    # apply the round unitary on (S_t, E_t) for every t
    psi = state.reshape(dims)
    for t in range(n):
        a = 3 * t + 1
        psi = np.tensordot(Ufull.reshape(3, 3, 3, 3), psi, axes=([2, 3], [a, a + 1]))
        psi = np.moveaxis(psi, [0, 1], [a, a + 1])
    vec = psi.reshape(-1)
    devE = [3 * t + 2 for t in range(n)]
    rho_dev = ptrace(np.outer(vec, vec.conj()), dims, devE)
    rank = int(np.sum(np.linalg.eigvalsh(rho_dev) > 1e-10))
    ok &= abs(entropy(rho_dev) - n * LOG3) < 1e-9 and rank == 3 ** n
R.check("the exact device (V with one pure qutrit per round) adds exactly log2 3 bits per round on Bell inputs and its "
        "rank triples every round (n = 1, 2, 3)", bool(ok))
Wsup = np.zeros((9, 9))
for i in range(3):
    for j in range(3):
        e = np.zeros((3, 3))
        e[i, j] = 1
        Wsup[:, 3 * i + j] = Wn(e).reshape(-1)
R.check("W and W^{(x)2} are invertible linear maps", np.linalg.matrix_rank(Wsup) == 9
        and np.linalg.matrix_rank(np.kron(Wsup, Wsup)) == 81)

# ---------------------------------------------------------------------------------------------------- 4. support test
Pm = np.array(Pminus.evalf(), dtype=float)
JW = Pm / 3
worst_ent, worst_tn, worst_gentle, informative, nonneg = 1e9, 1e9, 1e9, 0, True
for trial in range(600):
    dM = 2
    dD = 3 * dM                                # device: environment qutrit E and a memory qubit M
    rD = random_density(dD, rng)
    if rng.random() < 0.5:                     # mostly pure environment, as in the exact device
        rD = np.kron(dm(np.eye(3)[0]), random_density(dM, rng))
    w_, v_ = np.linalg.eigh(rD)
    w_ = np.clip(w_, 0, None)
    purD = sum(math.sqrt(w_[i]) * np.kron(v_[:, i], np.eye(dD)[i]) for i in range(dD))      # D (x) F
    eps = 10 ** rng.uniform(-5, -0.5)
    U = near_unitary(np.kron(Ufull, np.eye(dM)), eps, rng)                                   # on S E M
    if rng.random() < 0.2:
        U = random_unitary(9 * dM, rng)
    # global vector on Q S D F with Q S maximally entangled
    vec = np.kron(phi, purD)                    # (Q, S, E, M, F)
    dims = [3, 3, 3, dM, dD]
    psi = vec.reshape(3, 3 * 3 * dM, dD)
    psi = np.einsum("ab,qbf->qaf", U, psi).reshape(-1)
    rho = np.outer(psi, psi.conj())
    sQOF = ptrace(rho, dims, [0, 1, 4])
    sQO = ptrace(rho, dims, [0, 1])
    delta = max(0.0, 1 - float(np.trace(Pm @ sQO).real))
    betaF = ptrace(sQOF, [3, 3, dD], [2])
    # gentle measurement
    Pf = np.kron(Pm, np.eye(dD))
    s1 = Pf @ sQOF @ Pf
    s1 /= np.trace(s1).real
    worst_gentle = min(worst_gentle, 2 * math.sqrt(delta) - trace_norm(sQOF - s1))
    worst_tn = min(worst_tn, 20 * math.sqrt(delta) - trace_norm(sQOF - np.kron(JW, betaF)))
    Scond = cond_entropy(sQOF, [3, 3, dD], [0, 1])
    bound = LOG3 - g_afw(9, min(1.0, 10 * math.sqrt(delta)))
    worst_ent = min(worst_ent, Scond - bound)
    nonneg &= Scond >= -1e-9
    informative += bound > 0
R.check("gentle measurement: ||sigma - sigma'||_1 <= 2 sqrt(delta) (600 random rounds)", worst_gentle > -1e-9,
        f"smallest slack {worst_gentle:.2e}")
R.check("||sigma - J_W x beta_F||_1 <= 20 sqrt(delta)", worst_tn > -1e-9, f"smallest slack {worst_tn:.2e}")
R.check("S(QO|F) >= log2 3 - g_9(min{1, 10 sqrt delta}) and S(QO|F) >= 0, with many rounds where the bound is positive",
        worst_ent > -1e-9 and nonneg and informative >= 150, f"{informative} informative rounds, smallest slack {worst_ent:.3e}")

# ---------------------------------------------------------------------------------------------------- 5. convexity
f = lambda d: max(0.0, LOG3 - g_afw(9, min(1.0, 10 * math.sqrt(d))))
grid = np.concatenate([np.linspace(0, 1e-3, 20001)[1:], np.linspace(1e-3, 1, 2001)])
ok = True
for a in (np.linspace(1e-9, 3e-4, 3001), np.geomspace(1e-12, 1, 3001)):
    vals = [f(d) for d in a]
    for i in range(1, len(a) - 1):          # convexity on a non-uniform grid: slopes non-decreasing
        s1 = (vals[i] - vals[i - 1]) / (a[i] - a[i - 1])
        s2 = (vals[i + 1] - vals[i]) / (a[i + 1] - a[i])
        ok &= s2 >= s1 - 1e-9 * max(1, abs(s1))
t = sp.symbols("t", positive=True)
g9 = 2 * t * sp.log(9, 2) + (1 + t) * sp.log(1 + t, 2) - t * sp.log(t, 2)
d2 = sp.simplify(sp.diff(g9, t, 2))
R.check("delta -> [log2 3 - g_9(min{1, 10 sqrt delta})]_+ is convex (g_9 concave increasing: g_9'' = -1/(t(1+t) ln 2))",
        ok and sp.simplify(d2 + 1 / (t * (1 + t) * sp.log(2))) == 0
        and all(abs(float(g9.subs(t, tv)) - g_afw(9, tv)) < 1e-12 for tv in (1e-6, 0.01, 0.3, 1.0)))

# ---------------------------------------------------------------------------------------------------- 6. numbers
def root(fun, lo, hi):
    for _ in range(200):
        mid = math.sqrt(lo * hi)
        lo, hi = (mid, hi) if fun(mid) > 0 else (lo, mid)
    return lo


d_inf = root(lambda d: LOG3 - g_afw(9, 10 * math.sqrt(d)), 1e-8, 1e-2)
d_10 = root(lambda d: 0.1 * LOG3 - g_afw(9, 10 * math.sqrt(d)), 1e-10, 1e-3)
R.check("the bound is informative only for delta below about 2e-4", 1.5e-4 < d_inf < 2.5e-4, f"threshold {d_inf:.3e}")
R.check("it is within ten percent of log2 3 only near delta = 1e-6", 0.5e-6 < d_10 < 2e-6
        and LOG3 - g_afw(9, 10 * math.sqrt(1e-6)) >= 0.9 * LOG3, f"threshold {d_10:.3e}")
ratios = [n * g_afw(9, min(1.0, 10 / n)) / math.log2(n) for n in (10 ** 3, 10 ** 4, 10 ** 6, 10 ** 9, 10 ** 12)]
R.check("at error n^-2 the real-time bound is n log2 3 - O(log n): n g_9(10/n)/log2 n stays bounded",
        max(ratios) < 25 and ratios[-1] < ratios[0], ", ".join(f"{r_:.2f}" for r_ in ratios))
nn = sp.symbols("n", positive=True)
c0 = sp.symbols("c0")
batch_free = 2 * sp.log(nn ** 2, 2) + 2 * sp.log(nn + 1, 2) + c0
R.check("batch: log2(m/k) <= 2 log2(1/eps) + 2 log2(n+1) + O(1) at eps = n^-2 is 6 log2 n + O(1)",
        all(float((batch_free - 6 * sp.log(nn, 2) - c0).subs(nn, v)) <= 2 + 1e-12 for v in (1, 2, 10, 10 ** 6))
        and sp.limit(batch_free - 6 * sp.log(nn, 2) - c0, nn, sp.oo) == 0)
R.check("log2 3 bits of free energy per use is k_B T ln 3", abs(LOG3 * math.log(2) - math.log(3)) < 1e-15)
R.close()
