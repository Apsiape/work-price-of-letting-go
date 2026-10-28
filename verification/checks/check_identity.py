#!/usr/bin/env python3
"""check_identity.py -- the whole-block identity (Lemma "Whole-block identity", Section 3).

For a device D = C W R that starts in alpha_C (x) |w><w| (x) gamma_R, independent of the observer's
carriers P and purifier Q, and evolves by unitaries that conserve the total energy, the lemma states

  -dE_W - dE_C + (dS_C + S(W_f))/beta = E_t + (A + D(rho_Rf || gamma_R) + I(C:W:R)_f)/beta ,

with A = S(D_f) - S(D_i) the entropy gained by the device, E_t the energy handed to the carriers and
I(C:W:R)_f the final total correlation of the device's parts (entropies in nats).

The script draws random small systems, random Gibbs reservoirs, random observer states, and random
energy-conserving unitaries (block-diagonal in the total-energy eigenbasis), and checks the identity
to 1e-9, first for a single arrival-and-release step and then for two schedules with two visits: a
sequential one in which the observer chooses the second input after the first output is released (an
adaptive observer whose inputs are entangled across visits), and an overlapping one in which the second
carrier is released before the first. In the two-visit runs the controller starts mixed and the
controller and reservoir are purified by an inert register F, and the script checks S(D_i) = S(F) and
global purity, A = S(Z|F) with Z everything the observer holds at the end, which is the step that turns
the identity into the lower bound of the law. With --perturb it replaces the energy-conserving unitaries
by generic ones and requires the identity to FAIL, which it must, since the only physical input to the
lemma is energy conservation.

Usage: python3 check_identity.py [--perturb]
"""
import sys
import numpy as np
from numpy.linalg import eigh

rng = np.random.default_rng(20261013)
PERTURB = '--perturb' in sys.argv

def haar(n):
    z = (rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))

def entropy(rho):
    w = np.linalg.eigvalsh((rho + rho.conj().T) / 2)
    w = w[w > 1e-13]
    return float(-np.sum(w * np.log(w)))

def rel_entropy(rho, sigma):
    ws, vs = eigh(sigma)
    logsig = vs @ np.diag(np.log(ws)) @ vs.conj().T
    wr, vr = eigh(rho)
    wr = np.clip(wr, 0, None)
    logrho = vr @ np.diag(np.log(np.where(wr > 1e-13, wr, 1.0))) @ vr.conj().T
    return float(np.real(np.trace(rho @ (logrho - logsig))))

def ptrace(rho, dims, keep):
    """Partial trace keeping the subsystems in `keep` (indices into dims)."""
    n = len(dims)
    rho = rho.reshape(dims + dims)
    trace_out = [i for i in range(n) if i not in keep]
    for k, i in enumerate(sorted(trace_out, reverse=True)):
        # trace over axis i and i+n (current)
        rho = np.trace(rho, axis1=i, axis2=i + rho.ndim // 2)
    d = int(np.prod([dims[i] for i in keep]))
    return rho.reshape(d, d)

def random_state(n):
    a = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    r = a @ a.conj().T
    return r / np.trace(r)

def conserving_unitary(H):
    """A random unitary that commutes with H: Haar-random on each eigenspace."""
    w, v = eigh(H)
    U = np.zeros_like(v, dtype=complex)
    i = 0
    while i < len(w):
        j = i
        while j < len(w) and abs(w[j] - w[i]) < 1e-9:
            j += 1
        U[i:j, i:j] = haar(j - i)
        i = j
    return v @ U @ v.conj().T

passed, failed = 0, 0
def check(name, ok, info=''):
    global passed, failed
    if ok: passed += 1
    else: failed += 1
    print(('  ok    ' if ok else '  FAIL  ') + name + (f'  [{info}]' if info else ''))

beta = 1.3
max_dev = 0.0
for trial in range(12):
    dC, dW, dR, dP, dQ = 2, 3, 2, 2, 2          # controller, battery, reservoir, carrier, observer purifier
    # Hamiltonians with integer levels so that energy-conserving unitaries have nontrivial blocks
    hC = rng.integers(0, 3, size=dC).astype(float)
    hW = np.arange(dW, dtype=float)
    hR = rng.integers(0, 3, size=dR).astype(float)
    hP = rng.integers(0, 3, size=dP).astype(float)
    HC, HW, HR, HP = (np.diag(h) for h in (hC, hW, hR, hP))
    gammaR = np.diag(np.exp(-beta * hR)); gammaR /= np.trace(gammaR)
    alphaC = random_state(dC)
    w_idx = rng.integers(0, dW)
    battery = np.zeros((dW, dW)); battery[w_idx, w_idx] = 1.0
    # observer: carrier P entangled with a purifier Q, independent of the device
    psi = rng.normal(size=dP * dQ) + 1j * rng.normal(size=dP * dQ); psi /= np.linalg.norm(psi)
    obs = np.outer(psi, psi.conj())
    dims = [dC, dW, dR, dP, dQ]
    rho0 = np.kron(np.kron(np.kron(alphaC, battery), gammaR), obs)
    # total Hamiltonian on C W R P (Q carries no energy)
    I = np.eye
    Htot = (np.kron(np.kron(np.kron(HC, I(dW)), I(dR)), I(dP)) + np.kron(np.kron(np.kron(I(dC), HW), I(dR)), I(dP))
            + np.kron(np.kron(np.kron(I(dC), I(dW)), HR), I(dP)) + np.kron(np.kron(np.kron(I(dC), I(dW)), I(dR)), HP))
    U4 = haar(dC * dW * dR * dP) if PERTURB else conserving_unitary(Htot)
    U = np.kron(U4, I(dQ))
    rho1 = U @ rho0 @ U.conj().T
    # marginals
    D0 = ptrace(rho0, dims, [0, 1, 2]); D1 = ptrace(rho1, dims, [0, 1, 2])
    C0, C1 = ptrace(rho0, dims, [0]), ptrace(rho1, dims, [0])
    W0, W1 = ptrace(rho0, dims, [1]), ptrace(rho1, dims, [1])
    R0, R1 = ptrace(rho0, dims, [2]), ptrace(rho1, dims, [2])
    P0, P1 = ptrace(rho0, dims, [3]), ptrace(rho1, dims, [3])
    E = lambda rho, H: float(np.real(np.trace(rho @ H)))
    dEC, dEW, dER = E(C1, HC) - E(C0, HC), E(W1, HW) - E(W0, HW), E(R1, HR) - E(R0, HR)
    Et = E(P1, HP) - E(P0, HP)
    dSC = entropy(C1) - entropy(C0)
    SWf = entropy(W1)
    A = entropy(D1) - entropy(D0)
    Dr = rel_entropy(R1, gammaR)
    Itot = entropy(C1) + entropy(W1) + entropy(R1) - entropy(D1)
    lhs = -dEW - dEC + (dSC + SWf) / beta
    rhs = Et + (A + Dr + Itot) / beta
    dev = abs(lhs - rhs)
    max_dev = max(max_dev, dev)
    conservation = abs(dEC + dEW + dER + Et)
    if trial == 0:
        check('energy conservation dE_C + dE_W + dE_R + E_t = 0 for a conserving unitary', conservation < 1e-9, f'{conservation:.1e}')
    if trial < 3:
        check(f'whole-block identity on random device {trial+1}', dev < 1e-9, f'deviation {dev:.1e}')

check('whole-block identity on 12 random devices, deviation below 1e-9', max_dev < 1e-9, f'max {max_dev:.1e}')

# global purity: a pure device, Z = everything the observer holds, F trivial: A = S(Z)
dC, dP, dQ = 2, 2, 2
hC = np.array([0., 1.]); hP = np.array([0., 1.])
U2 = conserving_unitary(np.kron(np.diag(hC), np.eye(dP)) + np.kron(np.eye(dC), np.diag(hP)))
psiC = np.array([1.0, 0.0]); rhoC = np.outer(psiC, psiC)
psi = rng.normal(size=dP * dQ) + 1j * rng.normal(size=dP * dQ); psi /= np.linalg.norm(psi)
rho0 = np.kron(rhoC, np.outer(psi, psi.conj()))
U = np.kron(U2, np.eye(dQ))
rho1 = U @ rho0 @ U.conj().T
A = entropy(ptrace(rho1, [dC, dP, dQ], [0])) - 0.0
SZ = entropy(ptrace(rho1, [dC, dP, dQ], [1, 2]))
check('global purity: entropy gained by a pure-start device equals S(Z) of what the observer holds', abs(A - SZ) < 1e-9, f'{A:.6f} vs {SZ:.6f}')

# ---------------------------------------------------------------------------------------------------------------
# Schedules with two visits, a mixed device and its inert purifier F (pure-state simulation of everything).
# Systems: F (purifies C and R), C, W, R, carriers P1 and P2, observer memory Q. The observer starts in a random
# pure state of P1 P2 Q, so its inputs may be entangled with each other and with its memory.
#   sequential:  P1 arrives, U1 on C W R P1, P1 released; the observer acts on P1 P2 Q (it chooses the next input
#                using the released output); P2 arrives, U2 on C W R P2, P2 released;
#   overlapping: P1 and P2 arrive, U on C W R P1 P2, P2 released first, the observer acts on P2 Q,
#                U' on C W R P1, P1 released.
# E_t sums, visit by visit, the carrier's energy at release minus its energy at arrival.
SD = [4, 2, 3, 2, 2, 2, 4]          # F, C, W, R, P1, P2, Q
iF, iC, iW, iR, iP1, iP2, iQ = range(7)


def apply_on(psi, U, sites):
    """Apply the unitary U, acting on the listed subsystems in that order, to the state vector psi."""
    t = psi.reshape(SD)
    k = len(sites)
    Ut = U.reshape([SD[s] for s in sites] * 2)
    t = np.tensordot(Ut, t, axes=(list(range(k, 2 * k)), list(sites)))
    rest = [i for i in range(len(SD)) if i not in sites]
    perm = np.argsort(list(sites) + rest)
    return t.transpose(perm).reshape(-1)


def rdm(psi, keep):
    """Reduced density matrix of the listed subsystems, in increasing order."""
    t = psi.reshape(SD)
    rest = [i for i in range(len(SD)) if i not in keep]
    m = np.tensordot(t, t.conj(), axes=(rest, rest))
    d = int(np.prod([SD[i] for i in keep]))
    return m.reshape(d, d)


def conserving_on(hs):
    """A random unitary on the listed systems that conserves the sum of their diagonal Hamiltonians."""
    H = np.zeros((1, 1))
    for h in hs:
        H = np.kron(H, np.eye(len(h))) + np.kron(np.eye(H.shape[0]), np.diag(h))
    return haar(H.shape[0]) if PERTURB else conserving_unitary(H)


En = lambda rho, h: float(np.real(np.trace(rho @ np.diag(h))))
worst_id = worst_pur = worst_F = 0.0
min_SF = 1e9
for kind in ('sequential', 'overlapping'):
    for trial in range(6):
        hC = rng.integers(0, 3, size=2).astype(float)
        hW = np.arange(3, dtype=float)
        hR = rng.integers(0, 3, size=2).astype(float)
        hP1, hP2 = (rng.integers(0, 3, size=2).astype(float) for _ in range(2))
        gR = np.exp(-beta * hR); gR /= gR.sum()
        # inert purification of alpha_C (x) gamma_R on F (x) C R
        w, v = eigh(np.kron(random_state(2), np.diag(gR)))
        omega = sum(np.sqrt(max(w[k], 0.0)) * np.kron(np.eye(4)[k], v[:, k]) for k in range(4)).reshape(4, 2, 2)
        wv = np.zeros(3); wv[rng.integers(0, 3)] = 1.0                       # sharp battery
        obs = rng.normal(size=16) + 1j * rng.normal(size=16); obs /= np.linalg.norm(obs)
        psi = np.einsum('fcr,w,abq->fcwrabq', omega, wv, obs.reshape(2, 2, 4)).reshape(-1)
        D0, C0, W0 = rdm(psi, [iC, iW, iR]), rdm(psi, [iC]), rdm(psi, [iW])
        SD0, SF0 = entropy(D0), entropy(rdm(psi, [iF]))
        Et = 0.0
        if kind == 'sequential':
            Et -= En(rdm(psi, [iP1]), hP1)
            psi = apply_on(psi, conserving_on([hC, hW, hR, hP1]), [iC, iW, iR, iP1])
            Et += En(rdm(psi, [iP1]), hP1)
            psi = apply_on(psi, haar(16), [iP1, iP2, iQ])                     # the observer's adaptive step
            Et -= En(rdm(psi, [iP2]), hP2)
            psi = apply_on(psi, conserving_on([hC, hW, hR, hP2]), [iC, iW, iR, iP2])
            Et += En(rdm(psi, [iP2]), hP2)
        else:
            Et -= En(rdm(psi, [iP1]), hP1) + En(rdm(psi, [iP2]), hP2)
            psi = apply_on(psi, conserving_on([hC, hW, hR, hP1, hP2]), [iC, iW, iR, iP1, iP2])
            Et += En(rdm(psi, [iP2]), hP2)                                     # P2 leaves first
            psi = apply_on(psi, haar(8), [iP2, iQ])
            psi = apply_on(psi, conserving_on([hC, hW, hR, hP1]), [iC, iW, iR, iP1])
            Et += En(rdm(psi, [iP1]), hP1)
        D1, C1, W1, R1 = rdm(psi, [iC, iW, iR]), rdm(psi, [iC]), rdm(psi, [iW]), rdm(psi, [iR])
        dEC, dEW = En(C1, hC) - En(C0, hC), En(W1, hW) - En(W0, hW)
        A = entropy(D1) - SD0
        lhs = -dEW - dEC + (entropy(C1) - entropy(C0) + entropy(W1)) / beta
        rhs = Et + (A + rel_entropy(R1, np.diag(gR)) + entropy(C1) + entropy(W1) + entropy(R1) - entropy(D1)) / beta
        worst_id = max(worst_id, abs(lhs - rhs))
        worst_F = max(worst_F, abs(SD0 - SF0))
        min_SF = min(min_SF, SF0)
        SZF, SF = entropy(rdm(psi, [iF, iP1, iP2, iQ])), entropy(rdm(psi, [iF]))
        worst_pur = max(worst_pur, abs(A - (SZF - SF)))
check('whole-block identity on two-visit schedules (sequential with an adaptive observer; overlapping, released out '
      'of order), 12 random devices', worst_id < 1e-9, f'max deviation {worst_id:.1e}')
check('a mixed device and its inert purifier: S(D_i) = S(F) > 0', worst_F < 1e-9 and min_SF > 0.1,
      f'{worst_F:.1e}; smallest S(F) {min_SF:.3f}')
check('global purity on those schedules: A = S(Z|F), with Z everything the observer holds', worst_pur < 1e-9,
      f'max deviation {worst_pur:.1e}')

print()
if PERTURB:
    # the negative control must fail
    if failed == 0:
        print('NEGATIVE CONTROL DID NOT FIRE: the identity survived a non-conserving unitary'); sys.exit(1)
    print(f'negative control fired as required ({failed} check(s) failed under --perturb)'); sys.exit(0)
if failed:
    print(f'{failed} check(s) failed.'); sys.exit(1)
print('All checks passed.')
