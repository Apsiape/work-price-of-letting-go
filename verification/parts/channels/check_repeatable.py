"""Repeatable channels beyond mixtures of unitaries (Section 12, "Repeated use with memory"; Appendix G,
"Relation to prior work").

A Schur channel rho -> M o rho with M_ij = tr(u_j^* u_i), for unitaries u_i on a finite memory with normalized trace
tr, is implemented by U = sum_i |i><i| (x) u_i with the memory in its maximally mixed state pi, and
Tr_S U(rho (x) pi)U^* = sum_i rho_ii u_i pi u_i^* = pi for every input. One memory therefore serves every later use
without reset, which is repeatability in the sense of Rybar and Ziman. The checks below establish this for two
six-level examples with a qubit memory, show that neither channel is a mixture of unitaries, and show that the
repeated outputs are correlated, so that the repeated device does not meet the real-time error of this paper.

Checks:
  1. the qubit example (u = X, Y, Z, (X+Y)/sqrt2, (X+Z)/sqrt2, (Y+Z)/sqrt2), in exact arithmetic: each u_i is unitary;
     M is the Gram matrix V V^T of six unit vectors in R^3 (rows of V: e1, e2, e3, (e1+e2)/sqrt2, (e1+e3)/sqrt2,
     (e2+e3)/sqrt2), with unit diagonal and rank 3; U is unitary; on every matrix unit |i><j| the carrier output is
     M_ij |i><j| and the memory output is delta_ij pi, so the memory marginal returns for every input;
  2. it is not a mixture of unitaries, by both arguments of the text: (a) a mixture fixing every basis state uses
     diagonal unitaries diag(z) with z in ran M = ran V; for z = V c, |z_4|^2, |z_5|^2, |z_6|^2 equal
     1 + Re(c_a conj(c_b)) when |c_1| = |c_2| = |c_3| = 1 (exact identity), so all six moduli equal one only if the
     3 x 3 real Gram matrix of c_1, c_2, c_3 in R^2 is the identity, which has rank 3 > 2; and a search over a grid
     of the phases, refined locally, finds no vector closer than 0.239 in its worst entry; (b) the criterion of Haagerup and Musat [Cor. 2.5(b)]: the real diagonal Kraus
     operators a_k = diag(V e_k) satisfy sum a_k^2 = I, and the six products a_k a_l (k <= l) are linearly independent;
  3. Haagerup and Musat, Example 3.3, in exact arithmetic: their matrix B (beta = 1/sqrt5) equals x1 x1^* + x2 x2^* +
     x3 x3^* as they write it; B is real with unit diagonal and rank 3, the Gram matrix of the six diagonals of the
     icosahedron, so u_i = v_i . (X, Y, Z) gives the same qubit-memory dilation; the memory marginal returns; the
     products a_k a_l of its real diagonal Kraus operators are linearly independent, as their proof requires;
  4. repetition: three uses of one device with no reset, on random fresh inputs, half of them entangled with a
     reference (pure-state simulation, with the memory purified);
     every use's output, with its reference, equals (Phi (x) id) of its input to 1e-12, and the memory stays
     maximally mixed and uncorrelated with the current reference, for both examples; on halves of maximally entangled
     pairs the device's entropy does not grow (the accumulation lemma's increment is zero), unlike the log2 3 per
     use of the Werner-Holevo channel (check_werner.py);
  5. correlation: on two uniform superpositions the joint output of two uses differs from that of Phi (x) Phi. For
     Example 3.3 the trace distance is 0.5556 (5/9 to 1e-12; quoted as about 0.56 in Section 12); for the qubit
     example the joint output has the entry 1/36 at |11><22| (exact), where Phi (x) Phi has 0, and the trace
     distance is 0.5233;
  6. built-in control: with a memory state diag(0.8, 0.2) in place of pi the memory marginal depends on the input and
     the second use implements a different channel, so the tracial state is what makes the device repeatable.
"""
import itertools
import math

import numpy as np
import sympy as sp
from scipy.optimize import minimize

from qtools import Report, entropy, trace_norm

R = Report("Repeatable channels beyond mixtures of unitaries")
rng = np.random.default_rng(20261026)

# ---------------------------------------------------------------------------------------------- exact objects
sX = sp.Matrix([[0, 1], [1, 0]])
sY = sp.Matrix([[0, -sp.I], [sp.I, 0]])
sZ = sp.Matrix([[1, 0], [0, -1]])
r2 = sp.sqrt(2)
PAULI = (sX, sY, sZ)


def pauli_dot(v):
    return sum((c * P for c, P in zip(v, PAULI)), sp.zeros(2, 2))


def unit(k, n=6):
    e = sp.zeros(n, 1)
    e[k] = 1
    return e


def schur_dilation_exact(us):
    """Exact checks of U = sum_i |i><i| (x) u_i with the memory in pi = I/2, on every matrix unit."""
    d = len(us)
    pi = sp.eye(2) / 2
    U = sp.zeros(2 * d, 2 * d)
    for i, u in enumerate(us):
        U[2 * i:2 * i + 2, 2 * i:2 * i + 2] = u
    unitary = sp.simplify(U * U.H - sp.eye(2 * d)) == sp.zeros(2 * d, 2 * d)
    M = sp.Matrix(d, d, lambda i, j: sp.nsimplify(sp.simplify((us[j].H * us[i]).trace() / 2)))
    carrier_ok, memory_ok = True, True
    for i, j in itertools.product(range(d), repeat=2):
        Eij = unit(i, d) * unit(j, d).T
        out = U * sp.kronecker_product(Eij, pi) * U.H                 # S (x) memory, memory index fastest
        trM = sp.Matrix(d, d, lambda a, b: out[2 * a, 2 * b] + out[2 * a + 1, 2 * b + 1])
        trS = sp.Matrix(2, 2, lambda a, b: sum(out[2 * k + a, 2 * k + b] for k in range(d)))
        carrier_ok &= sp.simplify(trM - M[i, j] * Eij) == sp.zeros(d, d)
        memory_ok &= sp.simplify(trS - (pi if i == j else sp.zeros(2, 2))) == sp.zeros(2, 2)
    return U, M, unitary, carrier_ok, memory_ok


def kraus_products_rank(Vr):
    """Rank of {a_k a_l : k <= l} for the real diagonal Kraus operators a_k = diag(column k of Vr)."""
    cols = [Vr[:, k] for k in range(Vr.shape[1])]
    prods = [sp.matrix_multiply_elementwise(cols[k], cols[l]) for k in range(len(cols)) for l in range(k, len(cols))]
    sum_sq = sum((sp.matrix_multiply_elementwise(c, c) for c in cols), sp.zeros(Vr.shape[0], 1))
    return sp.Matrix.hstack(*prods).rank(simplify=True), sp.simplify(sum_sq - sp.ones(Vr.shape[0], 1))


# ---------------------------------------------------------------------------------------------- 1. qubit example
Vq = sp.Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1], [1 / r2, 1 / r2, 0], [1 / r2, 0, 1 / r2], [0, 1 / r2, 1 / r2]])
uq = [pauli_dot(Vq.row(i)) for i in range(6)]
Uq, Mq, unit_q, car_q, mem_q = schur_dilation_exact(uq)
R.check("qubit example: the six u_i are unitary and U = sum_i |i><i| (x) u_i is unitary",
        all(sp.simplify(u * u.H) == sp.eye(2) for u in uq) and unit_q)
R.check("qubit example: M_ij = tr(u_j^* u_i) = (V V^T)_ij, unit diagonal, rank 3 (exact)",
        sp.simplify(Mq - Vq * Vq.T) == sp.zeros(6, 6) and all(Mq[i, i] == 1 for i in range(6)) and Mq.rank() == 3)
R.check("qubit example: on every matrix unit the carrier output is M o rho and the memory returns to I/2 (exact)",
        car_q and mem_q)

# ---------------------------------------------------------------------------------------------- 2. not mixed unitary
x = sp.symbols("x1:4", real=True)
y = sp.symbols("y1:4", real=True)
c = [x[k] + sp.I * y[k] for k in range(3)]
z = [sum(Vq[i, k] * c[k] for k in range(3)) for i in range(6)]
ok_id = True
for i, (a, b) in zip(range(3, 6), [(0, 1), (0, 2), (1, 2)]):
    mod2 = sp.expand(z[i] * sp.conjugate(z[i]))
    target = sp.expand((c[a] * sp.conjugate(c[a]) + c[b] * sp.conjugate(c[b])) / 2
                       + sp.re(c[a] * sp.conjugate(c[b])))
    ok_id &= sp.simplify(mod2 - target) == 0
G_forced = sp.eye(3)            # Re(c_a conj c_b) = delta_ab is forced; c_a in R^2 gives Gram rank <= 2
R.check("qubit example, (a): for z = V c, |z_(a,b)|^2 = (|c_a|^2 + |c_b|^2)/2 + Re(c_a conj c_b), so unit moduli "
        "force a 3 x 3 Gram matrix of three vectors in R^2 to be I_3, of rank 3 > 2",
        ok_id and z[0] == c[0] and z[1] == c[1] and z[2] == c[2] and G_forced.rank() == 3)
Vn = np.array(Vq.evalf(), dtype=float)
grid = np.linspace(0, 2 * math.pi, 1441)                         # the global phase is irrelevant: fix c_1 = 1
P2, P3 = np.meshgrid(grid, grid, indexing="ij")
cs = np.stack([np.ones_like(P2), np.exp(1j * P2), np.exp(1j * P3)], -1)
defect = np.max(np.abs(np.abs(cs @ Vn.T) - 1), axis=-1)
k0 = np.unravel_index(np.argmin(defect), defect.shape)
refine = minimize(lambda t: float(np.max(np.abs(np.abs(Vn @ np.array([1, np.exp(1j * t[0]), np.exp(1j * t[1])]))
                                                 - 1))), [grid[k0[0]], grid[k0[1]]], method="Nelder-Mead",
                  options={"xatol": 1e-10, "fatol": 1e-12})
best = min(float(defect.min()), float(refine.fun))
R.check("qubit example, (a): no phase vector lies in ran M: over a 1441 x 1441 grid of the two relative phases, "
        "refined locally, every z = V c with |c_a| = 1 has an entry whose modulus differs from 1 by at least 0.239",
        best > 0.239, f"smallest largest defect {best:.4f}")
rk, sq = kraus_products_rank(Vq)
R.check("qubit example, (b): sum_k a_k^2 = I and the six products a_k a_l (k <= l) are linearly independent, so "
        "[Haagerup-Musat, Cor. 2.5(b)] excludes a mixture of unitaries", rk == 6 and sq == sp.zeros(6, 1))

# ---------------------------------------------------------------------------------------------- 3. Example 3.3
beta = 1 / sp.sqrt(5)
w = sp.exp(2 * sp.pi * sp.I / 5)
x1 = sp.Matrix([1] + [beta] * 5)
x2 = sp.sqrt(sp.Rational(2, 5)) * sp.Matrix([0] + [w ** k for k in range(5)])
x3 = x2.conjugate()
B = sp.Matrix(6, 6, lambda i, j: 1 if i == j else (beta if 0 in (i, j)
                                                   else (beta if (i - j) % 5 in (1, 4) else -beta)))
dec = sp.simplify(sp.expand_complex(x1 * x1.H + x2 * x2.H + x3 * x3.H - B))
R.check("Example 3.3: B = x1 x1^* + x2 x2^* + x3 x3^* (beta = 1/sqrt5, x3 = conj x2) as Haagerup and Musat write it",
        dec == sp.zeros(6, 6))
Vh = sp.Matrix([[1, 0, 0]] + [[beta, 2 * beta * sp.cos(2 * sp.pi * k / 5), 2 * beta * sp.sin(2 * sp.pi * k / 5)]
                              for k in range(5)])
gram = sp.simplify(Vh * Vh.T - B)
R.check("Example 3.3: B is real with unit diagonal and rank 3, the Gram matrix of six unit vectors in R^3 with "
        "|<v_i, v_j>| = 1/sqrt5 (the diagonals of the icosahedron)",
        gram == sp.zeros(6, 6) and B.rank(simplify=True) == 3 and all(B[i, i] == 1 for i in range(6))
        and all(abs(B[i, j]) == beta for i in range(6) for j in range(6) if i != j))
uh = [sp.simplify(pauli_dot(Vh.row(i))) for i in range(6)]
Uh, Mh, unit_h, car_h, mem_h = schur_dilation_exact(uh)
R.check("Example 3.3: u_i = v_i . (X, Y, Z) are unitary, tr(u_j^* u_i) = B_ij, and the qubit memory returns to I/2 "
        "on every matrix unit while the carrier output is B o rho (exact)",
        unit_h and sp.simplify(Mh - B) == sp.zeros(6, 6) and car_h and mem_h)
rk_h, sq_h = kraus_products_rank(Vh)
R.check("Example 3.3: sum_k a_k^2 = I and {a_k a_l : k <= l} is linearly independent, the hypothesis of "
        "[Haagerup-Musat, Cor. 2.5(b)]", rk_h == 6 and sq_h == sp.zeros(6, 1))

# ---------------------------------------------------------------------------------------------- 4. repetition
# Pure-state simulation. Axes of the global vector: [S_n, R_n, ..., S_1, R_1, M, F], where F purifies the memory M.
NUM = {"qubit": (np.array(Uq.evalf(), dtype=complex), np.array(Mq.evalf(), dtype=float)),
       "Example 3.3": (np.array(Uh.evalf(), dtype=complex), np.array(B.evalf(), dtype=float))}
PI_VEC = np.eye(2).reshape(2, 2) / math.sqrt(2)                   # purification of I/2 on (M, F)


def run_uses(U, psis, mem):
    """One device, no reset: each psi (an array of shape (6, d_ref)) is a fresh input on its carrier and reference;
    U acts on the carrier and the memory. Returns the global vector as an array with the axes listed above."""
    state = mem
    for psi in psis:
        state = np.tensordot(psi, state, axes=0)
        m = state.ndim - 2
        st = np.moveaxis(state, m, 1)
        shape = st.shape
        st = (U @ st.reshape(12, -1)).reshape(shape)
        state = np.moveaxis(st, 1, m)
    return state


def marginal(state, keep):
    v = np.moveaxis(state, keep, list(range(len(keep))))
    dk = int(np.prod(v.shape[:len(keep)]))
    v = v.reshape(dk, -1)
    return v @ v.conj().T


def schur(M, rho_SR, dref):
    """(Phi (x) id)(rho) for Phi(rho) = M o rho on the first factor."""
    T = rho_SR.reshape(6, dref, 6, dref) * M[:, None, :, None]
    return T.reshape(6 * dref, 6 * dref)


def random_input():
    dref = int(rng.choice([1, 6]))
    psi = rng.normal(size=(6, dref)) + 1j * rng.normal(size=(6, dref))
    return psi / np.linalg.norm(psi), dref


worst = 0.0
for name, (U, M) in NUM.items():
    for trial in range(8):
        ins = [random_input() for _ in range(3)]
        fin = run_uses(U, [psi for psi, _ in ins], PI_VEC)
        for k, (psi, dref) in enumerate(ins):
            pos = 2 * (len(ins) - 1 - k)
            rho = psi.reshape(-1, 1) @ psi.reshape(1, -1).conj()
            worst = max(worst, float(np.max(np.abs(marginal(fin, [pos, pos + 1]) - schur(M, rho, dref)))))
        mem_axis = fin.ndim - 2
        worst = max(worst, float(np.max(np.abs(marginal(fin, [mem_axis]) - np.eye(2) / 2))))
        if ins[-1][1] > 1:                                         # memory and the reference of the last use
            mr = marginal(fin, [1, mem_axis])
            worst = max(worst, float(np.max(np.abs(mr - np.kron(marginal(fin, [1]), np.eye(2) / 2)))))
R.check("three uses of one device, no reset, random fresh inputs, half of them entangled with a reference: every use "
        "outputs (Phi (x) id) of its input, and the memory stays I/2 and uncorrelated with the current reference "
        "(both examples)", worst < 1e-12, f"largest deviation {worst:.1e}")
bell = np.eye(6) / math.sqrt(6)                                    # |Phi_6> on S (x) R
ent_ok = True
for name, (U, M) in NUM.items():
    for n in (1, 2, 3):
        fin = run_uses(U, [bell] * n, PI_VEC)
        ent_ok &= abs(entropy(marginal(fin, [fin.ndim - 2])) - 1.0) < 1e-10
R.check("on halves of maximally entangled pairs the device (one qubit) keeps entropy exactly 1 bit after 1, 2 and 3 "
        "uses: the accumulation increment is zero, where Werner-Holevo needs log2 3 per use", ent_ok)

# ---------------------------------------------------------------------------------------------- 5. correlation
plus = np.ones((6, 1)) / math.sqrt(6)
td = {}
for name, (U, M) in NUM.items():
    fin = run_uses(U, [plus, plus], PI_VEC)                       # axes [S2, R2, S1, R1, M, F]
    joint = marginal(fin, [2, 0])                                  # (O1, O2)
    one = M * (plus @ plus.T)
    td[name] = trace_norm(joint - np.kron(one, one)) / 2
    if name == "qubit":
        exact = sp.nsimplify((uq[0] * uq[0] * sp.eye(2) / 2 * uq[1].H * uq[1].H).trace() / 36)
        ok5 = (exact == sp.Rational(1, 36) and abs(joint[0, 1 * 6 + 1] - 1 / 36) < 1e-13
               and Mq[0, 1] == 0 and abs(np.kron(one, one)[0, 7]) < 1e-15)
R.check("qubit example: two uses on |+_6>|+_6> give the entry 1/36 at |11><22| (exact), where Phi (x) Phi has 0", ok5)
R.check("two uses on |+_6>|+_6>: the joint output is at trace distance 0.5556 = 5/9 (to 1e-12) from Phi (x) Phi for "
        "Example 3.3 (quoted as about 0.56) and 0.5233 for the qubit example",
        abs(td["Example 3.3"] - 5 / 9) < 1e-12 and round(td["Example 3.3"], 2) == 0.56
        and abs(td["qubit"] - 0.52327) < 5e-5,
        f"Example 3.3 {td['Example 3.3']:.12f}, qubit {td['qubit']:.5f}")

# ---------------------------------------------------------------------------------------------- 6. control
XI_VEC = np.diag([math.sqrt(0.8), math.sqrt(0.2)])                 # purification of diag(0.8, 0.2)
U, M = NUM["qubit"]
mem_dep = 0.0
for k in range(6):
    fin = run_uses(U, [np.eye(6)[:, [k]]], XI_VEC)
    mem_dep = max(mem_dep, float(np.max(np.abs(marginal(fin, [2]) - np.diag([0.8, 0.2])))))
after = [marginal(run_uses(U, [np.eye(6)[:, [k]], plus], XI_VEC), [0]) for k in (0, 2)]
diff = trace_norm(after[0] - after[1]) / 2
R.check("control: with the memory in diag(0.8, 0.2) instead of I/2 the memory marginal depends on the input and the "
        "second use acts differently after different first inputs", mem_dep > 0.5 and diff > 0.05,
        f"memory shift {mem_dep:.2f}, second-use difference {diff:.3f}")
R.close()
