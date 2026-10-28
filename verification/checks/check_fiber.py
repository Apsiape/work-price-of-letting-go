#!/usr/bin/env python3
"""check_fiber.py -- the fiber law for a released past (Theorem 7.1, Appendix I), as proved.

  1. Dephasing is necessary and free (Lemma I.1). For X a singleton and g(y) = y, a device that
     permutes without dephasing the question carrier sends |+><+| to itself, while the target
     outputs I/2: trace distance 1/2. With a phase coin drawn from the zero-Hamiltonian reservoir
     the output is exact, also for inputs entangled with a reference, and the coin's marginal is
     unchanged.
  2. The real-time device of Lemma I.2 for g = AND, one episode, both carriers entangled with
     references: the observer's final state equals the target's exactly, and the entropy the device
     adds is at most log2 F' = log2 3.
  3. Orthogonal purifications need not have orthogonal marginals (two Bell states), which is why
     Lemma I.4 (with the remark after it) argues by distinguishability under a common continuation and trace-distance
     contractivity instead.
  4. The pairwise-fidelity bound on the pretty-good measurement used in Lemma I.7,
     P_err <= sum_{c != c'} sqrt(p_c p_c') F(rho_c, rho_c'), on random ensembles.
  5. The information-flow identity of Lemma I.6,
     I(H:B') = I(H:B) + H(IN|B) - I(H:C'|B'),  and  S(B'|H) >= S(B|H) - S(C'|H),
     on random classical-quantum states and random unitaries.
  6. The robust lower bound of Lemma I.7 for g = AND on two episodes: for the exact device and for
     devices whose four gates are perturbed, S(B_f) - S(tau) >= n [log2 F' - delta(eps)], with eps
     the largest error over the deterministic observers and the steering observer, which are the only
     observers the proof uses.
  7. Why the proof needs the deterministic observers: a device that is correct only against the
     steering observer pays H(Y) = 0.918 bits per episode for AND, below log2 3.
With --perturb, items 1 and 7 assert the two invalid shortcuts (no dephasing; steering observer alone)
and the script must FAIL.

Usage: python3 check_fiber.py [--perturb]
"""
import sys, math, itertools, warnings
warnings.filterwarnings("ignore")
import numpy as np
from scipy.linalg import expm, sqrtm

PERTURB = '--perturb' in sys.argv
rng = np.random.default_rng(20261016)
passed = failed = 0
def check(name, ok, info=''):
    global passed, failed
    passed += bool(ok); failed += (not ok)
    print(('  ok    ' if ok else '  FAIL  ') + name + (f'  [{info}]' if info else ''))

def H2(p):
    return 0.0 if p <= 0 or p >= 1 else -p * math.log2(p) - (1 - p) * math.log2(1 - p)
def S(rho):
    w = np.linalg.eigvalsh((rho + rho.conj().T) / 2); w = w[w > 1e-13]
    return float(-np.sum(w * np.log2(w)))
def tdist(a, b):
    return 0.5 * float(np.sum(np.abs(np.linalg.eigvalsh((a - b + (a - b).conj().T) / 2))))
def ket(d, i):
    v = np.zeros(d, complex); v[i] = 1; return v
def ptrace_vec(psi, dims, keep):
    """reduced density matrix of a pure state on the subsystems in keep"""
    n = len(dims); t = psi.reshape(dims)
    perm = list(keep) + [i for i in range(n) if i not in keep]
    t = np.transpose(t, perm)
    dk = int(np.prod([dims[i] for i in keep])); t = t.reshape(dk, -1)
    return t @ t.conj().T
def apply(psi, dims, U, sites):
    """apply unitary U to the subsystems in sites (in that order)"""
    n = len(dims); t = psi.reshape(dims)
    rest = [i for i in range(n) if i not in sites]
    t = np.transpose(t, list(sites) + rest)
    ds = int(np.prod([dims[i] for i in sites])); sh = t.shape
    t = (U @ t.reshape(ds, -1)).reshape(sh)
    inv = np.argsort(list(sites) + rest)
    return np.transpose(t, inv).reshape(-1)
def perm_unitary(mapping, d):
    U = np.zeros((d, d), complex)
    for a, b in mapping.items(): U[b, a] = 1
    assert np.allclose(U.conj().T @ U, np.eye(d)); return U
def cphase(d):
    """controlled phase carrier (d) x coin (d): |y>|k> -> w^{yk} |y>|k>"""
    w = np.exp(2j * np.pi / d)
    return np.diag([w ** (y * k) for y in range(d) for k in range(d)])

# ---------------------------------------------------------------- 1. dephasing
plus = np.ones(2) / np.sqrt(2)
rho_plus = np.outer(plus, plus.conj())
target = np.eye(2) / 2
undephased_out = rho_plus                       # the permutation for g(y) = y is the identity on P2
gap = tdist(undephased_out, target)
if PERTURB:
    check('(invalid shortcut) a permutation without dephasing implements the classical task', gap < 1e-12, f'trace distance {gap:.3f}')
else:
    check('without dephasing the question carrier, |+><+| is sent to itself, at trace distance 1/2 from the target I/2', abs(gap - 0.5) < 1e-12, f'{gap:.3f}')
# with a coin from the reservoir: P2 (2) x coin K (2) x coin purifier F (2) x reference R (2)
bell = (np.kron(ket(2, 0), ket(2, 0)) + np.kron(ket(2, 1), ket(2, 1))) / np.sqrt(2)
dims = [2, 2, 2, 2]                              # R, P2, K, F
psi = np.kron(bell, bell)                        # (R,P2) Bell, (K,F) Bell = maximally mixed coin
psi = apply(psi, dims, cphase(2), [1, 2])
out = ptrace_vec(psi, dims, [0, 1])
tgt = sum(0.5 * np.kron(np.outer(ket(2, y), ket(2, y)), np.outer(ket(2, y), ket(2, y))) for y in range(2))
check('with a reservoir phase coin the output is exact, also for an input entangled with a reference', tdist(out, tgt) < 1e-12, f'{tdist(out, tgt):.1e}')
coin = ptrace_vec(psi, dims, [2])
check("the coin's marginal is unchanged (maximally mixed), so dephasing adds no entropy to the device", tdist(coin, np.eye(2) / 2) < 1e-12)

# ---------------------------------------------------------------- 2. the real-time device for AND, one episode, entangled observer
g = lambda x, y: x & y
K, Fp = 2, 3
fiber = {0: [(0, 0), (0, 1), (1, 0)], 1: [(1, 1)]}
iota = {pr: i for z, prs in fiber.items() for i, pr in enumerate(prs)}
# injection (c,y) -> (idx, z) on M(3) x P2(2), extended to a permutation
inj = {(c, y): (iota[(c, y)], g(c, y)) for c in range(2) for y in range(2)}
dom = [(m, y) for m in range(3) for y in range(2)]
used = set(inj.values()); free_t = [t for t in dom if t not in used]
full = dict(inj); free_s = [s for s in dom if s not in inj]
for s, t in zip(free_s, free_t): full[s] = t
U2 = perm_unitary({m * 2 + y: full[(m, y)][0] * 2 + full[(m, y)][1] for (m, y) in dom}, 6)
# U1 on P1(2) x M(3): (x, 0) -> (x, c(x) = x); a permutation of the 6 levels
U1 = np.zeros((6, 6), complex)
for x in range(2):
    for m in range(3):
        mm = {0: x, x: 0}.get(m, m) if x else m
        U1[x * 3 + mm, x * 3 + m] = 1
assert np.allclose(U1.conj().T @ U1, np.eye(6))
# systems: R1 P1 R2 P2 M K1 F1 K2 F2
dims = [2, 2, 2, 2, 3, 2, 2, 2, 2]
psi = np.kron(np.kron(bell, bell), np.kron(ket(3, 0), np.kron(bell, bell)))
psi = apply(psi, dims, cphase(2), [1, 5])        # dephase P1 with coin K1
psi = apply(psi, dims, U1, [1, 4])               # copy the class into M
psi = apply(psi, dims, cphase(2), [3, 7])        # dephase P2 with coin K2
psi = apply(psi, dims, U2, [4, 3])               # (c, y) -> (index, answer) on M, P2
obs = ptrace_vec(psi, dims, [0, 1, 2, 3])
tgt = np.zeros((16, 16), complex)
for x in range(2):
    for y in range(2):
        v = np.kron(np.kron(ket(2, x), ket(2, x)), np.kron(ket(2, y), ket(2, g(x, y))))
        tgt += 0.25 * np.outer(v, v.conj())
check('Lemma I.2 device for g = AND reproduces the target exactly against an entangled observer', tdist(obs, tgt) < 1e-12, f'{tdist(obs, tgt):.1e}')
Dfin = ptrace_vec(psi, dims, [4, 5, 7]); Dini = 0.0 + 2.0     # M pure, two coins maximally mixed
added = S(Dfin) - Dini
check('the entropy the device adds is at most log2 F\' = log2 3', added <= math.log2(3) + 1e-9, f'{added:.4f} bits')

# ---------------------------------------------------------------- 3. orthogonal purifications, identical marginals
b0 = (np.kron(ket(2, 0), ket(2, 0)) + np.kron(ket(2, 1), ket(2, 1))) / np.sqrt(2)
b1 = (np.kron(ket(2, 0), ket(2, 0)) - np.kron(ket(2, 1), ket(2, 1))) / np.sqrt(2)
m0, m1 = ptrace_vec(b0, [2, 2], [0]), ptrace_vec(b1, [2, 2], [0])
check('two orthogonal Bell states have identical marginals: orthogonal purifications do not give orthogonal marginals',
      abs(np.vdot(b0, b1)) < 1e-12 and tdist(m0, m1) < 1e-12)

# ---------------------------------------------------------------- 4. pairwise-fidelity bound on the pretty-good measurement
def rand_state(d, r):
    A = rng.normal(size=(d, r)) + 1j * rng.normal(size=(d, r)); R = A @ A.conj().T; return R / np.trace(R).real
def fid(a, b):
    return float(np.sum(np.linalg.svd(sqrtm(a) @ sqrtm(b), compute_uv=False)).real)
def isqrt(Sm):
    w, v = np.linalg.eigh(Sm); w = np.array([x ** -0.5 if x > 1e-12 else 0.0 for x in w]); return v @ np.diag(w) @ v.conj().T
worst = -1.0
for _ in range(800):
    Kc, d = int(rng.integers(2, 5)), int(rng.integers(2, 5))
    rh = [rand_state(d, int(rng.integers(1, d + 1))) for _ in range(Kc)]
    p = rng.dirichlet(np.ones(Kc)); Sm = sum(pi * r for pi, r in zip(p, rh)); Si = isqrt(Sm)
    perr = 1 - sum(pi * np.trace(Si @ (pi * r) @ Si @ r).real for pi, r in zip(p, rh))
    rhs = sum(np.sqrt(p[i] * p[j]) * fid(rh[i], rh[j]) for i in range(Kc) for j in range(Kc) if i != j)
    worst = max(worst, perr - rhs)
check('pretty-good-measurement error <= sum over pairs sqrt(p p\') F, on 800 random ensembles', worst <= 1e-9, f'max excess {worst:.2e}')

# ---------------------------------------------------------------- 5. information-flow identity
def cq(probs, states):
    return [(p, s) for p, s in zip(probs, states)]
def S_cond_given_H(ens):
    return sum(p * S(s) for p, s in ens)
def S_avg(ens):
    return S(sum(p * s for p, s in ens))
def I_H(ens):
    return S_avg(ens) - S_cond_given_H(ens)
ok_id = ok_ineq = True; maxdev = 0.0
for _ in range(40):
    nh, dB, dC = 3, 3, 2
    p = rng.dirichlet(np.ones(nh))
    omegas = [rand_state(dB, int(rng.integers(1, dB + 1))) for _ in range(nh)]
    ins = [int(rng.integers(0, dC)) for _ in range(nh)]
    Wm = sqrtm(np.eye(dB * dC))
    A = rng.normal(size=(dB * dC,) * 2) + 1j * rng.normal(size=(dB * dC,) * 2); Wm = np.linalg.qr(A)[0]
    joint_in = [np.kron(o, np.outer(ket(dC, i), ket(dC, i))) for o, i in zip(omegas, ins)]
    joint_out = [Wm @ j @ Wm.conj().T for j in joint_in]
    def red(rho, keep):           # keep 0 = B, 1 = C
        r = rho.reshape(dB, dC, dB, dC)
        return np.einsum('ijkj->ik', r) if keep == 0 else np.einsum('ijil->jl', r)
    B0 = [(pp, o) for pp, o in zip(p, omegas)]
    B1 = [(pp, red(j, 0)) for pp, j in zip(p, joint_out)]
    # H(IN|B): classical input label given B
    rho_BIN = sum(pp * np.kron(o, np.outer(ket(dC, i), ket(dC, i))) for pp, o, i in zip(p, omegas, ins))
    H_IN_given_B = S(rho_BIN) - S(sum(pp * o for pp, o in zip(p, omegas)))
    # I(H:C'|B') = S(C'B'|...)... computed as I(H:B'C') - I(H:B')
    BC1 = [(pp, j) for pp, j in zip(p, joint_out)]
    I_C_given_B1 = I_H(BC1) - I_H(B1)
    lhs = I_H(B1); rhs = I_H(B0) + H_IN_given_B - I_C_given_B1
    maxdev = max(maxdev, abs(lhs - rhs))
    C1 = [(pp, red(j, 1)) for pp, j in zip(p, joint_out)]
    if S_cond_given_H(B1) < S_cond_given_H(B0) - S_cond_given_H(C1) - 1e-9: ok_ineq = False
check('information-flow identity I(H:B\') = I(H:B) + H(IN|B) - I(H:C\'|B\') on 40 random instances', maxdev < 1e-9, f'max deviation {maxdev:.1e}')
check('entropy given the history decreases by at most the released carrier\'s entropy', ok_ineq)

# ---------------------------------------------------------------- 6. robust lower bound, g = AND, n = 2
def run_device(gates, hist):
    """gates = [(U1,U2), (U1,U2)] on B = M1(3) M2(3); hist = ((x1,y1),(x2,y2)); returns global pure state on M1 M2 P1 Q1 P2 Q2"""
    dims = [3, 3, 2, 2, 2, 2]
    psi = np.kron(np.kron(ket(3, 0), ket(3, 0)), np.kron(np.kron(ket(2, hist[0][0]), ket(2, hist[0][1])), np.kron(ket(2, hist[1][0]), ket(2, hist[1][1]))))
    for i in range(2):
        U1i, U2i = gates[i]
        psi = apply(psi, dims, U1i, [2 + 2 * i, i])           # P1 of episode i with M_i ... gate acts on (P1, M_i)
        psi = apply(psi, dims, U2i, [i, 3 + 2 * i])           # gate on (M_i, P2)
    return psi, dims
def errors_and_entropy(gates):
    hists = list(itertools.product(itertools.product(range(2), range(2)), repeat=2))
    errs = {}
    for h in hists:
        psi, dims = run_device(gates, h)
        rho = ptrace_vec(psi, dims, [2, 3, 4, 5])
        t = np.kron(np.kron(ket(2, h[0][0]), ket(2, g(*h[0]))), np.kron(ket(2, h[1][0]), ket(2, g(*h[1]))))
        errs[h] = tdist(rho, np.outer(t, t.conj()))
    steer = [h for h in hists if all(pr in fiber[0] for pr in h)]
    Bf = sum(ptrace_vec(*run_device(gates, h), [0, 1]) for h in steer) / len(steer)
    eps_steer = sum(errs[h] for h in steer) / len(steer)
    return errs, eps_steer, S(Bf)
def delta(eps, Kc=2, d1=2, d2=2):
    f = lambda t, d: t * math.log2(d - 1) + H2(t) if d > 1 else 0.0
    pe = 2 * (Kc - 1) * math.sqrt(eps)
    return H2(pe) + pe * math.log2(max(Kc - 1, 1)) + 3 * f(eps, d1) + 3 * f(eps, d2), pe
exact = [(U1, U2), (U1, U2)]
errs, es, SB = errors_and_entropy(exact)
check('exact device: zero error on all 16 deterministic observers, and S(B_f) - S(tau) = 2 log2 3 for the steering observer',
      max(errs.values()) < 1e-12 and abs(SB - 2 * math.log2(3)) < 1e-9, f'{SB:.4f} bits')
ok_rb = True; rows = []
for strength in [1e-3, 3e-3, 1e-2, 2e-2]:
    for _ in range(3):
        gates = []
        for i in range(2):
            G1 = rng.normal(size=(6, 6)) + 1j * rng.normal(size=(6, 6)); G1 = (G1 + G1.conj().T) / 2
            G2 = rng.normal(size=(6, 6)) + 1j * rng.normal(size=(6, 6)); G2 = (G2 + G2.conj().T) / 2
            gates.append((U1 @ expm(1j * strength * G1), U2 @ expm(1j * strength * G2)))
        errs, es, SB = errors_and_entropy(gates)
        eps = max(max(errs.values()), es)
        d, pe = delta(eps)
        if pe > 0.5: continue
        bound = 2 * (math.log2(3) - d)
        rows.append((strength, eps, SB, bound))
        if SB < bound - 1e-9: ok_rb = False
check('robust lower bound S(B_f) - S(tau) >= n [log2 F\' - delta(eps)] on perturbed devices', ok_rb and len(rows) >= 6,
      '; '.join(f'eps={e:.1e}: {s:.3f} >= {b:.3f}' for _, e, s, b in rows[:4]))

# ---------------------------------------------------------------- 7. the steering observer alone does not force log2 F'
# device correct only on steering histories: no record at P1; at P2 swap the question into M_i and emit |0>
SW = np.zeros((6, 6), complex)                    # on M(3) x P2(2): (0, y) -> (y, 0); extend to a permutation
mapping = {(0, 0): (0, 0), (0, 1): (1, 0), (1, 0): (0, 1), (1, 1): (1, 1), (2, 0): (2, 0), (2, 1): (2, 1)}
for (m, y), (m2, y2) in mapping.items(): SW[m2 * 2 + y2, m * 2 + y] = 1
lazy = [(np.eye(6), SW), (np.eye(6), SW)]
errs, es, SB = errors_and_entropy(lazy)
worst_det = max(errs.values())
if PERTURB:
    d, _ = delta(es)
    check('(invalid shortcut) the steering observer alone forces n log2 F\'', SB >= 2 * (math.log2(3) - d) - 1e-9,
          f'S = {SB:.3f} vs {2 * math.log2(3):.3f}; steering error {es:.1e}')
else:
    check('a device correct only for the steering observer pays H(Y) = 0.918 bits per episode, below log2 3, and fails a distinguishing observer',
          es < 1e-12 and abs(SB - 2 * (-(2 / 3) * math.log2(2 / 3) - (1 / 3) * math.log2(1 / 3))) < 1e-9 and worst_det > 0.99,
          f'S = {SB:.3f} bits for two episodes; worst deterministic error {worst_det:.2f}')

print()
if PERTURB:
    if failed == 0: print('NEGATIVE CONTROL DID NOT FIRE'); sys.exit(1)
    print(f'negative control fired as required ({failed} check(s) failed under --perturb)'); sys.exit(0)
if failed: print(f'{failed} check(s) failed.'); sys.exit(1)
print('All checks passed.')
