#!/usr/bin/env python3
"""check_span_criterion.py -- the span criterion of Theorem 4.3 is sufficient, not necessary.

B(Phi) = max over pairs (rho, sigma) with Psi(rho) = Psi(sigma) of  Tr(rho D) + kT ln2 [S(sigma) - S(Phi(sigma))],
capacity = max over rho of  Tr(rho D) + kT ln2 [S(rho) - S(Phi(rho))],  with D = Phi^*(H) - H.

  1. Hadamard gate on a qubit of gap E (kT = 1, bits -> nats handled consistently): Kraus products span {I},
     D is NOT in that span, and yet B = capacity = E/sqrt(2): the entropy term vanishes for a unitary, so both
     maxima are lambda_max(D). This is the counterexample to "B = capacity exactly when D in span".
  2. X-dephasing on the same qubit: D = (E/2) Z is not in span{I, X}, and B = E/2 > capacity strictly
     (capacity computed by a fine grid over the Bloch sphere; B from the pair rho = |0><0|, sigma = I/2, which the
     complementary channel cannot tell apart, together with the upper bound B <= max Tr(rho D) + max entropy term).
  3. complete dephasing in the energy basis (classical, balanced: D = 0 lies in the span of the diagonal
     projectors): B = capacity, by the general sufficiency statement and by direct computation.
With --perturb the script asserts the false equivalence (unbalanced => strict excess) and must FAIL on item 1.

Usage: python3 check_span_criterion.py [--perturb]
"""
import sys
import numpy as np

PERTURB = '--perturb' in sys.argv
passed = failed = 0
def check(name, ok, info=''):
    global passed, failed
    passed += ok; failed += (not ok)
    print(('  ok    ' if ok else '  FAIL  ') + name + (f'  [{info}]' if info else ''))

kT = 1.0; E = 1.0
H = np.diag([0.0, E])
X = np.array([[0, 1], [1, 0]], dtype=complex); Z = np.diag([1.0, -1.0]).astype(complex); I2 = np.eye(2, dtype=complex)

def entropy_nats(rho):
    w = np.linalg.eigvalsh((rho + rho.conj().T) / 2); w = w[w > 1e-13]
    return float(-np.sum(w * np.log(w)))

def apply(kraus, rho):
    return sum(K @ rho @ K.conj().T for K in kraus)

def D_of(kraus):
    return sum(K.conj().T @ H @ K for K in kraus) - H

def in_span(M, basis, tol=1e-9):
    A = np.column_stack([b.reshape(-1) for b in basis])
    coef, res, rank, sv = np.linalg.lstsq(A, M.reshape(-1), rcond=None)
    return np.linalg.norm(A @ coef - M.reshape(-1)) < tol

def bloch_states(n=200):
    out = []
    for t in np.linspace(0, np.pi, n):
        for p in np.linspace(0, 2 * np.pi, n, endpoint=False):
            r = np.array([np.sin(t) * np.cos(p), np.sin(t) * np.sin(p), np.cos(t)])
            for s in (1.0, 0.75, 0.5, 0.25, 0.0):
                out.append((I2 + s * (r[0] * X + r[1] * 1j * X @ Z + r[2] * Z)) / 2)  # 1j*X*Z = Y up to sign; fine
    return out

STATES = bloch_states(60)

def capacity(kraus):
    D = D_of(kraus)
    return max(np.real(np.trace(rho @ D)) + kT * (entropy_nats(rho) - entropy_nats(apply(kraus, rho))) for rho in STATES)

# 1. Hadamard
Hd = np.array([[1, 1], [1, -1]], dtype=complex) / np.sqrt(2)
kr = [Hd]
D = D_of(kr)
products = [kr[0].conj().T @ kr[0]]
lam = np.linalg.eigvalsh(D)[-1]
cap = capacity(kr)
B_had = lam                      # entropy term is zero for every sigma, so B = max_rho Tr rho D = lambda_max(D)
check('Hadamard: Kraus products span {I} and D is not in that span', (not in_span(D, products)) and in_span(I2, products))
check('Hadamard: capacity = lambda_max(D) = E/sqrt2 (grid)', abs(cap - E / np.sqrt(2)) < 1e-3, f'{cap:.5f} vs {E/np.sqrt(2):.5f}')
check('Hadamard: B = lambda_max(D) = capacity although D is outside the span', abs(B_had - E / np.sqrt(2)) < 1e-12 and abs(B_had - cap) < 1e-3)
if PERTURB:
    cap_exact = lam   # for a unitary the entropy term vanishes identically, so the capacity is exactly lambda_max(D)
    check('[perturb] unbalanced channel must have B > capacity', B_had - cap_exact > 1e-9, f'B - capacity = {B_had-cap_exact:.2e}')

# 2. X-dephasing
kr = [I2 / np.sqrt(2), X / np.sqrt(2)]
D = D_of(kr)
products = [a.conj().T @ b for a in kr for b in kr]
check('X-dephasing: D = (E/2) Z lies outside span{I, X}', np.allclose(D, (E / 2) * Z) and not in_span(D, products))
cap = capacity(kr)
# complementary channel: Psi(rho)_{ij} = Tr(K_i rho K_j^dagger)
def comp(rho): return np.array([[np.trace(a @ rho @ b.conj().T) for b in kr] for a in kr])
rho0 = np.diag([1.0, 0.0]).astype(complex); sig = I2 / 2
pair_ok = np.allclose(comp(rho0), comp(sig))
B_lower = np.real(np.trace(rho0 @ D)) + kT * (entropy_nats(sig) - entropy_nats(apply(kr, sig)))
B_upper = np.linalg.eigvalsh(D)[-1] + kT * max(entropy_nats(r) - entropy_nats(apply(kr, r)) for r in STATES)
check('X-dephasing: the pair rho = |0><0|, sigma = I/2 is indistinguishable to the environment', pair_ok)
check('X-dephasing: B = E/2 (lower bound from that pair meets the upper bound)', abs(B_lower - E / 2) < 1e-12 and abs(B_upper - E / 2) < 1e-6, f'{B_lower:.5f} <= B <= {B_upper:.5f}')
check('X-dephasing: B exceeds the capacity strictly', E / 2 - cap > 0.05, f'capacity {cap:.5f}, B {E/2:.5f}')

# 3. energy-basis dephasing (balanced)
P0, P1 = np.diag([1.0, 0.0]).astype(complex), np.diag([0.0, 1.0]).astype(complex)
kr = [P0, P1]
D = D_of(kr); products = [a.conj().T @ b for a in kr for b in kr]
check('energy-basis dephasing: D = 0 lies in the span of the Kraus products (balanced)', in_span(D, products))
cap = capacity(kr)
# B <= max Tr rho D + max entropy term = 0 + 0 (unital, D = 0); and B >= capacity: so B = capacity = 0
B_upper = np.linalg.eigvalsh(D)[-1] + kT * max(entropy_nats(r) - entropy_nats(apply(kr, r)) for r in STATES)
check('energy-basis dephasing: B = capacity (= 0)', abs(cap) < 1e-9 and abs(B_upper) < 1e-9, f'capacity {cap:.2e}, B upper {B_upper:.2e}')

print()
if PERTURB:
    if failed == 0: print('NEGATIVE CONTROL DID NOT FIRE'); sys.exit(1)
    print(f'negative control fired as required ({failed} check(s) failed under --perturb)'); sys.exit(0)
if failed: print(f'{failed} check(s) failed.'); sys.exit(1)
print('All checks passed.')
