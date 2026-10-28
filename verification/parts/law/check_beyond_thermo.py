"""Order beyond thermodynamics (Section "Beyond thermodynamics" and Appendix "Coherence and thermodynamic numbers").

Checks:
  1. the release-step identity C_r(MB) - C_r(M) = S(Z_B|Z_M) - S(B|M) on random states;
  2. the release lemma: a Bell pair answers both questions exactly with -S(B|M) = 1, and the robust bound
     -S(B|M) >= 1 - g(sqrt(eps)(1 + 2/sin 2theta)) holds on noisy states, for several tilts theta;
  3. -S(B|M) <= log2 dim M, and S(B|J) >= 0 for a classical J;
  4. the tilted coherence task: the flagged ensemble has relative entropy of coherence h2(sin^2 theta), and the
     surcharge 1 - h2(sin^2 theta) is 0.399 at theta = pi/8;
  5. the CNOT process equals "dephase A in the X basis, then apply Z_B^{x_A}", is a uniform mixture of two incoherent
     unitaries, and an early-release circuit using one |+> implements it exactly;
  6. the order-price matrix has rank two, and the crossing pair rules out an ordering of tasks under one direction of
     communication (the CNOT process, first slot at the party that answers, is one-way LOCC without entanglement).
     The order prices themselves are entered from the manuscript, except 0.399, which check 4 recomputes: the one-ebit
     price of the BB84 task and the coherence lower bound of the CNOT process are proved there (Section 11 and
     Appendix C) and are not checked here; this check computes the rank, the one-way protocol and the comparison;
  7. the delay law: one more step of delay saves exactly #{i : l_i = b + 1}.
"""
import math

import numpy as np

from qtools import HAD, I2, X, Z, Report, apply, dm, embed, entropy, h2, ket, ptrace, random_density, random_unitary

R = Report("Order beyond thermodynamics")
rng = np.random.default_rng(31)


def dephase(rho):
    return np.diag(np.diag(rho))


def Cr(rho):
    return entropy(dephase(rho)) - entropy(rho)


def cond(rho, dims, a):
    """S(A|rest) for the subsystem index a."""
    rest = [i for i in range(len(dims)) if i != a]
    return entropy(rho) - entropy(ptrace(rho, dims, rest))


# 1. release step
worst = 0.0
for _ in range(300):
    dM = int(rng.integers(2, 4))
    rho = random_density(2 * dM, rng)                      # sites (M, B)
    lhs = Cr(rho) - Cr(ptrace(rho, [dM, 2], [0]))
    dz = dephase(rho)
    rhs = (entropy(dz) - entropy(ptrace(dz, [dM, 2], [0]))) - cond(rho, [dM, 2], 1)
    worst = max(worst, abs(lhs - rhs))
R.check("C_r(MB) - C_r(M) = S(Z_B|Z_M) - S(B|M) (300 random states)", worst < 1e-10, f"{worst:.1e}")


# 2. release lemma
def basis(theta):
    return [np.array([math.cos(theta), math.sin(theta)]), np.array([-math.sin(theta), math.cos(theta)])]


def mismatch(rho_BM, dM, vecs):
    """Least probability that an answer computed from M disagrees with B measured in the basis `vecs`."""
    parts = [ptrace(np.kron(dm(v), np.eye(dM)) @ rho_BM, [2, dM], [1]) for v in vecs]
    diff = parts[0] - parts[1]
    return 0.5 * (1 - float(np.sum(np.abs(np.linalg.eigvalsh((diff + diff.conj().T) / 2)))))


def g(dd):
    return 2 * dd + (1 + dd) * h2(dd / (1 + dd))


phi = (ket((0, 0)) + ket((1, 1))) / math.sqrt(2)
ok_exact = True
for theta in (math.pi / 8, math.pi / 6, math.pi / 4, 0.3):
    rho = dm(phi)
    for vecs in (basis(0.0), basis(theta)):
        ok_exact &= mismatch(rho, 2, vecs) < 1e-12
    ok_exact &= abs(-cond(rho, [2, 2], 0) - 1) < 1e-12
R.check("a Bell pair answers both questions exactly, with -S(B|M) = 1, for every tilt", ok_exact)
worst, informative = 1e9, 0
for _ in range(3000):
    theta = rng.choice([math.pi / 8, math.pi / 6, math.pi / 4, 0.4])
    dM = int(rng.choice([2, 3]))
    lam = rng.uniform(0, 0.03)
    base = np.zeros(2 * dM, dtype=complex)
    base[0], base[dM + 1] = 1 / math.sqrt(2), 1 / math.sqrt(2)          # Bell pair inside B x M
    u = np.kron(I2, random_unitary(dM, rng)) if dM == 2 and rng.random() < 0.2 else np.eye(2 * dM)
    rho = (1 - lam) * apply(u, dm(base)) + lam * random_density(2 * dM, rng)
    eps = max(mismatch(rho, dM, basis(0.0)), mismatch(rho, dM, basis(theta)))
    dd = math.sqrt(eps) * (1 + 2 / math.sin(2 * theta))
    if dd < 1:
        informative += 1
        worst = min(worst, -cond(rho, [2, dM], 0) - (1 - g(dd)))
R.check("-S(B|M) >= 1 - g(sqrt(eps)(1 + 2/sin 2theta)) on noisy states", worst > -1e-10 and informative > 500,
        f"{informative} informative cases, smallest slack {worst:.3e}")

# 3. dimension cap and classical memory
ok3 = True
for _ in range(300):
    dM = int(rng.integers(2, 4))
    rho = random_density(2 * dM, rng)
    ok3 &= -cond(rho, [2, dM], 0) <= math.log2(dM) + 1e-10
    p = rng.dirichlet(np.ones(dM))
    cq = sum(p[j] * np.kron(random_density(2, rng), dm(np.eye(dM)[j])) for j in range(dM))
    ok3 &= cond(cq, [2, dM], 0) >= -1e-10
R.check("-S(B|M) <= log2 dim M, and S(B|J) >= 0 for classical J", bool(ok3))

# 4. tilted coherence task
okc = True
for theta in (math.pi / 8, 0.2, 0.5, math.pi / 4):
    u = basis(theta)
    ens = sum(0.5 * np.kron(dm(ket((a,))), dm(u[a])) for a in (0, 1))
    okc &= abs(Cr(ens) - h2(math.sin(theta) ** 2)) < 1e-12
R.check("the flagged tilted ensemble has relative entropy of coherence h2(sin^2 theta)", okc)
R.check("the coherence surcharge 1 - h2(sin^2(pi/8)) is 0.399", round(1 - h2(math.sin(math.pi / 8) ** 2), 3) == 0.399,
        f"{1 - h2(math.sin(math.pi / 8) ** 2):.5f}")

# 5. CNOT process; sites (A, B), CNOT from B to A
CN_BA = np.eye(4, dtype=complex)[[0, 3, 2, 1]]                    # control B (second), target A (first)
Pp, Pm = dm(np.array([1, 1]) / math.sqrt(2)), dm(np.array([1, -1]) / math.sqrt(2))


def process(rho):
    out = apply(CN_BA, rho)
    return 0.5 * (out + apply(np.kron(X, I2), out))              # dephase A in the X basis


def described(rho):
    return apply(np.kron(Pp, I2), rho) + apply(np.kron(Pm, Z), rho)


def choi(ch):
    out = np.zeros((16, 16), dtype=complex)
    for i in range(4):
        for j in range(4):
            e = np.zeros((4, 4), dtype=complex)
            e[i, j] = 1
            out += np.kron(e, ch(e))
    return out


R.check("CNOT then X-dephasing of A equals: dephase A in the X basis, then apply Z_B^{x_A}",
        np.allclose(choi(process), choi(described)))
U1, U2 = CN_BA, np.kron(X, I2) @ CN_BA
incoherent = all(np.count_nonzero(np.abs(u) > 1e-12) == 4 and np.allclose(np.abs(u)[np.abs(u) > 1e-12], 1) for u in (U1, U2))
R.check("it is the uniform mixture of two incoherent (permutation) unitaries",
        incoherent and np.allclose(choi(process), choi(lambda r: 0.5 * apply(U1, r) + 0.5 * apply(U2, r))))
# early release with one |+>: sites (A, B, K); step 1 on A, K: CNOT K->A; step 2 on B, K: CNOT B->K
CN = np.eye(4, dtype=complex)[[0, 1, 3, 2]]
d3 = [2, 2, 2]
plus = np.array([1, 1]) / math.sqrt(2)


def early(rho):
    full = np.kron(rho, dm(plus))
    out = apply(embed(CN, [1, 2], d3) @ embed(CN, [2, 0], d3), full)
    return ptrace(out, d3, [0, 1])


R.check("an early-release circuit using one |+> implements the CNOT process exactly", np.allclose(choi(early), choi(process)))

# 6. order-price matrix
M = np.array([[1.0, 1.0], [0.0, 1 - h2(math.sin(math.pi / 8) ** 2)]])    # rows: entanglement, coherence; cols: BB84, tilted
R.check("the 2x2 order-price matrix (BB84, tilted) x (entanglement, coherence) has rank two (entries from the text; 0.399 recomputed)",
        np.linalg.matrix_rank(M) == 2)
# Entanglement theory of Table 6: one-way communication from the party that answers to the party that releases.
# The CNOT process with its first slot at the party that answers and its second at the party that releases is the
# instrument sum_x (P_x (x) Z^x) . (P_x (x) Z^x) of check 5: the first party measures A in the X basis, which is the
# required dephasing, and sends x_A in the allowed direction; the second applies Z^{x_A}. No entanglement is used, in
# either schedule, so its entanglement order price is 0; BB84 costs one ebit in that theory (Table 6).
one_way = np.allclose(choi(process), choi(lambda r: sum(apply(np.kron(Px, np.linalg.matrix_power(Z, x)), r)
                                                       for x, Px in enumerate((Pp, Pm)))))
bb84, cnot_proc = (1, 0), (0, 1)              # (entanglement, coherence) order prices, entered from the text
R.check("BB84 and the CNOT process cross, with the order prices (1, 0) and (0, 1) taken from the text: the CNOT process "
        "is one-way LOCC from the answering to the releasing party, without entanglement", one_way and bb84[0] > cnot_proc[0] and bb84[1] < cnot_proc[1])

# 7. delay law
ok7 = True
for _ in range(500):
    ls = rng.integers(0, 10, int(rng.integers(1, 20)))
    for b in range(0, 10):
        cost = lambda bb: int(np.sum(ls > bb))
        ok7 &= cost(b) - cost(b + 1) == int(np.sum(ls == b + 1))
R.check("one more step of delay saves exactly #{i : l_i = b + 1}", bool(ok7))
R.close()
