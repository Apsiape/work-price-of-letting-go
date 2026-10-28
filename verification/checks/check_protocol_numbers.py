#!/usr/bin/env python3
"""check_protocol_numbers.py -- the numbers of the protocol (Section 10), and four main-text numbers that no other
script recomputes: the heat form of the two-qubit certificate (Proposition 9.1(d)), recomputed here a second time
independently of parts/law/check_certificate.py; the correlation term m = 0.197 at the batch optimum (Figure 3); the
trace distance of the embezzling example (Section 2); and the reset of a Gibbs qubit in "Side information" (Section 5).

Section 10 (three-arm feedback-trap protocol):
  1. the early-arm bound 1 - h2(delta) is 0.71 at delta = 5% and 0.92 at delta = 1% (units kT ln 2);
  2. kT ln 2 is about 2.9e-21 J at 300 K;
  3. Hoeffding-Azuma for the episode indicators of disagreement (martingale differences with predictable range 1):
     with 5e4 episodes per arm the estimate of delta is off by 1e-2 or more with probability at most
     2 exp(-2 N t^2) = 9.1e-5, below 1e-3;
  4. heat confidence is separate from error confidence and needs independence (or a covariance analysis), and a
     bound on the spread of every stroke, which is an assumption: Jun et al. (PRL 113, 190601) report a statistical
     error of about 0.10 kT after 60 minutes of cycles, which at their shortest cycle, 0.5 tau_0 = 7.5 s, means a
     per-cycle spread of 0.10 sqrt(3600 / 7.5) = 2.19 kT, about 2.2 kT; if every stroke has spread at most 2.2 kT and
     strokes and episodes are independent, ten strokes have spread sqrt(10) * 2.2 = 6.96 kT and the uncertainty at
     N = 5e4 is 0.0311 kT, below 0.032 kT; ten PERFECTLY CORRELATED strokes have spread 10 * 2.2 = 22 kT and the
     uncertainty is 0.098 kT, near 0.1 kT; independence alone does not bound the spread (ten independent strokes of
     spread 100 kT give 1.41 kT, about 1.4 kT); and a shared offset Q_i = Z survives averaging (variance of the mean
     = Var Z, not Var Z / N);
  5. 5e4 episodes at a 7.5-second stroke take 3.75e5 s = 4.34 days per stroke of an episode, per arm and per duration
     of the sweep: about 43 days for ten strokes, before overhead.
Proposition 9.1(d), heat form (Section 9 and Appendix D):
  6. 0.99 - 0.08 - h2(0.07) - 0.07 log2 3 = 0.433, and 0.99 * 0.433 = 0.429 > 0.42 (a 1% temperature margin);
  7. randomized hidden settings, N = 150,000 episodes fixed in advance (about 50,000 per setting): the
     per-episode estimate Y = (3/4)(1 -+ outcome) lies in [0, 3/2] and has mean (3 - <XX> - <ZZZ> + <ZYY>)/4 = e
     (checked on random states), so one-sided Hoeffding-Azuma keeps the average leakage below the observed 5%
     plus 0.02, below 7%, except with probability exp(-8 N 0.02^2 / 9) < 1e-23, below the quoted 3e-4; and
     known blocks of settings do not certify one state (each block passes while every emitted state leaks 1/2).
Figure 3 (amplitude damping at p = 1/2, beta E = ln 2):
  8. the batch integrand c(x) = h(x) - h(x/2) - x/2 is maximal near x = 0.18, where the correlation term
     m(x) = 2 h(x/2) - h(x) is 0.197.
Section 2 (the embezzling example):
  9. a flat superposition of N = n^2 levels and its shift by n levels have overlap 1 - 1/n, hence trace distance
     sqrt(2/n - 1/n^2), about sqrt(2/n): 0.436, 0.141, 0.045 at n = 10, 100, 1000, computed from the vectors.
Section 10, the interface:
  10. the record-export device (copy a into a blank M before releasing A; B ^= M when B arrives; swap M with a
      supplied blank log L and export L) is a permutation of all 16 basis states of (A, B, M, L) and sends
      (a, b, 0, 0) to (a, a ^ b, 0, a): no heat at degenerate Hamiltonian, M blank, delta = 0;
  11. for a bath that does not start in its Gibbs state, beta Q = Delta S_R + D(rho_f || gamma) - D(rho_i || gamma)
      (nats) on random states, and the initial relative entropy can make beta Q - Delta S_R negative;
  12. joint records: the device that copies b into the blank log L, adds M into B and clears M against B and L is a
      permutation of all 16 basis states of (A, B, M, L) sending (a, b, 0, 0) to (a, a ^ b, 0, b), with M blank and
      delta = 0; on the carriers alone (a, b, 0) -> (a, a ^ b, b) is injective; on fair inputs the exported L carries
      zero information about a by itself, and one full bit jointly with the released a ^ b;
  13. consumed blanks: at degenerate Hamiltonian the permutation (M, Z, R) -> (Z, R, M) of the copy M = a, a supplied
      blank Z and a uniform bath bit R resets M with no heat and returns Z uniform and independent of a; the episode's
      entropy then sits in Z (Delta S_Z = 1 bit), so the reported quantity meets 1 - h2(0) = 1 only when Z is
      counted; and letting a blank bit relax to the maximally mixed state at temperature T returns kT ln 2 of work.
Section 10, timing (Jun, Gavrilov and Bechhoefer, PRL 113, 190601, Eq. (3) and Table I):
  14. tau_0 = (2 x_m)^2 / D with x_m = 2.5 um and D = 1.7 um^2/s is about 15 s; the fit <W>/kT = 0.71 + 1.39 / tau
      (tau in units of tau_0) at their shortest cycle, tau = 0.5 tau_0 = 7.5 s, gives about 3.5 kT, five times kT ln 2.
Section 10, the graded control (a helper R = a ^ N_eta lent to the device and returned unmodified):
  15. exact enumeration on fair a, b and noise N_eta: the outputs stay exact (delta = 0); adding R into the copy leaves
      the bit N_eta, whose tuned reset costs h2(eta); the lower bound 1 - I(a:R) equals h2(eta); h2(eta) is 0, 0.081,
      0.469, 0.811 and 1 at eta = 0, 0.01, 0.1, 0.25 and 0.5; a reset tuned to a fair bit costs
      H(N) + D(N || uniform) = 1 bit at every eta (the mismatch cost).
Section 10, what the held and lent intercepts need:
  16. a held episode whose camera frame L keeps a copy of a: the outputs (a, a ^ b) are exact (delta = 0), and the
      frame cleaned against the held well before release (L ^= A) ends blank at no cost, while after both outputs
      have left it holds one bit that nothing the device still holds predicts, H(L | device) = 1, so its reset
      disposes of one bit however slowly the gates run.
Section 10, the endpoint rule (a reflection-symmetric double well V(x) = E_b (x^2 - 1)^2, E_b = 8 kT):
  17. equilibrium across the barrier makes the bit fair (P(x > 0) = 1/2, so a reset bit would be wrong half the
      time); equilibrium within each well gives the same mean energy in both wells; and with the same symmetric
      potential, a within-well distribution that is not in equilibrium (the canonical one at 1.2 T in one well)
      changes the mean energy by a bit-dependent amount, so symmetry alone does not fix Delta U.
Section 10 and Appendix D, confidence endpoints:
  18. the identity on both carriers keeps no record, needs no heat and has decoded disagreement exactly 1/2 on fresh
      fair inputs; substituting the upper endpoint of the valid interval [0.49, 0.51] would claim 1 - h2(0.51) > 0,
      while delta* = min(delta_U, 1/2) gives 0; for every delta_U the clipped rule is the least value over [0, delta_U]
      of 1 - h2(delta) and of h2(eta) - h2(delta), and, clipped at 3/4, of 1 - h2(e) - e log2 3, whose entropy term
      reaches its maximum 2 at e = 3/4.
Section 10, fresh probes:
  19. if all 10 episodes receive the same fair bit, the exact device that keeps a copy of each a (delta = 0) holds
      1 bit of record in all, against 10 bits for fresh independent inputs, although every input is fair.
Section 10, the loan as a contract (the first well A, the second well B and the copy M, from (a, b, 0)):
  20. a fresh fair bit r returned in place of a leaves the uncomputed copy M = a ^ r uniform, one bit that nothing
      the device still holds predicts (stranded as in the early arm); with a FLIPPED return a ^ 1, on all four inputs:
      the device that computes from the returned well (B ^= A, then M ^= A) ends in (a ^ 1, a ^ b ^ 1, 1), every
      answer wrong and delta = 1; the device that computes from the copy (B ^= M before M ^= A) ends in
      (a ^ 1, a ^ b, 1), every answer right and delta = 0 from the first delivery, but 1 from the final release of A;
      in both M ends in the fixed state 1 (no record of a: I(a:M) = 0, restored by a fixed NOT); the flipped well
      keeps the whole bit a (I(a:A) = 1); and an unused hidden copy of a changes neither delta nor M.
Section 5, side information (a qubit of gap E at beta E = ln 2 in its Gibbs state):
  21. the excited population is 1/3; resetting to the ground state costs the free-energy difference
      ln Z / ln 2 = log2(3/2) = 0.585 bits = h2(1/3) - 1/3, below the entropy alone, h2(1/3) = 0.918; and it is the
      full-reset rate of Theorem 4.2(b) at p = 1, max_y [h2(y) - y], attained at y = 1/3.

With --perturb the early-arm bound 1 - h2(delta) is replaced by the naive 1 - delta, the embezzling distance by 1/n,
and the graded-control cost h2(eta) by the linear interpolation 2 eta between the lent and early arms, the three errors
this script guards against; checks 1, 9 and 15 must then all FAIL, and the control counts as fired only if all do.

Usage: python3 check_protocol_numbers.py [--perturb]
"""
import math
import sys

import numpy as np

PERTURB = '--perturb' in sys.argv
passed = failed = 0
failed_names = []


def check(name, ok, info=''):
    global passed, failed
    passed += bool(ok)
    failed += (not ok)
    if not ok:
        failed_names.append(name)
    print(('  ok    ' if ok else '  FAIL  ') + name + (f'  [{info}]' if info else ''))


def h2(p):
    return 0.0 if p in (0.0, 1.0) else -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def early_arm_bound(delta):
    return 1 - delta if PERTURB else 1 - h2(delta)


K_B = 1.380649e-23          # J/K, exact (SI 2019)

# ---------------------------------------------------------------- Section 10
b5, b1 = early_arm_bound(0.05), early_arm_bound(0.01)
check('early arm: 1 - h2(delta) = 0.71 at delta = 5% and 0.92 at delta = 1%', round(b5, 2) == 0.71 and round(b1, 2) == 0.92,
      f'{b5:.4f}, {b1:.4f}')

kTln2 = K_B * 300 * math.log(2)
check('kT ln 2 at 300 K is about 2.9e-21 J', round(kTln2 / 1e-21, 1) == 2.9, f'{kTln2:.4e} J')

N, t = 50_000, 1e-2
fail = 2 * math.exp(-2 * N * t * t)
check('Hoeffding-Azuma, 5e4 episodes, deviation 1e-2: failure probability below 1e-3', fail < 1e-3, f'{fail:.2e}')

tau0 = 15.0
sig_jun = 0.10 * math.sqrt(3600.0 / (0.5 * tau0))               # 0.10 kT after 60 minutes of 7.5 s cycles
check('Jun et al.: 0.10 kT after 60 minutes of 7.5 s cycles means a per-cycle spread of about 2.2 kT',
      round(sig_jun, 1) == 2.2 and sig_jun <= 2.2, f'{sig_jun:.3f} kT')
SIG = 2.2                                                       # the ASSUMED bound on the spread of every stroke
ind10, cor10 = math.sqrt(10) * SIG, 10 * SIG
check('assuming every stroke has spread at most 2.2 kT, ten INDEPENDENT strokes give an uncertainty below 0.032 kT '
      'at N = 5e4', ind10 / math.sqrt(N) < 0.032, f'ten strokes {ind10:.2f} kT, uncertainty {ind10 / math.sqrt(N):.4f} kT')
check('ten PERFECTLY CORRELATED strokes have ten times the spread: uncertainty near 0.1 kT',
      abs(cor10 / math.sqrt(N) - 0.1) < 0.005, f'ten strokes {cor10:.2f} kT, uncertainty {cor10 / math.sqrt(N):.4f} kT')
big10 = math.sqrt(10) * 100.0 / math.sqrt(N)
check('independence alone does not bound the spread: ten independent strokes of spread 100 kT give 1.4 kT',
      round(big10, 1) == 1.4, f'{big10:.4f} kT')
# a shared offset survives averaging: Q_i = Z for every i, with Z = +-1 equally likely; the mean of the N values is Z
zs = np.array([-1.0, 1.0])
var_mean_shared = float(np.mean(zs ** 2) - np.mean(zs) ** 2)
check('a shared offset Q_i = Z survives averaging: Var(mean) = Var(Z) = 1, not Var(Z) / N',
      var_mean_shared == 1.0, f'Var(mean) = {var_mean_shared}, iid formula {1.0 / N:.1e}')

seconds = N * 0.5 * tau0
days = seconds / 86400
check('5e4 episodes at a 7.5 s stroke: 4.34 days per stroke of an episode, about 43 days for ten strokes, per arm',
      round(days, 2) == 4.34 and round(10 * days) == 43,
      f'{seconds:.3g} s = {days:.3f} days per stroke; ten strokes {10 * days:.1f} days')

# ---------------------------------------------------------------- Proposition 9.1(d), heat form
heat = 0.99 - 0.08 - h2(0.07) - 0.07 * math.log2(3)
check('heat bound 0.99 - 0.08 - h2(0.07) - 0.07 log2 3 = 0.433, and 0.429 > 0.42 after a 1% margin',
      round(heat, 3) == 0.433 and round(0.99 * heat, 3) == 0.429 and 0.99 * heat > 0.42, f'{heat:.4f}, {0.99 * heat:.4f}')
# Randomized hidden settings: in each episode one of (X_A X_B, Z_Q Z_A Z_B, Z_Q Y_A Y_B) is drawn uniformly and
# independently of the device, and Y = (3/4)(1 - c o) with c = +1, +1, -1 and outcome o = +-1.  Its mean is
# (1/3) sum_s (3/4)(1 - c_s <O_s>) = (3 - <XX> - <ZZZ> + <ZYY>)/4 = 1 - Tr(Pi_code rho), the leakage.
I2c, Xc = np.eye(2, dtype=complex), np.array([[0, 1], [1, 0]], dtype=complex)
Yc, Zc = np.array([[0, -1j], [1j, 0]]), np.diag([1.0, -1.0]).astype(complex)


def k3(a, b, c):
    return np.kron(np.kron(a, b), c)                               # order Q, A, B


settings = [(k3(I2c, Xc, Xc), +1), (k3(Zc, Zc, Zc), +1), (k3(Zc, Yc, Yc), -1)]
Pi = (np.eye(8) + settings[0][0]) @ (np.eye(8) + settings[1][0]) / 4
rng7 = np.random.default_rng(20261025)
worst = 0.0
for _ in range(500):
    g = rng7.normal(size=(8, 8)) + 1j * rng7.normal(size=(8, 8))
    rho = g @ g.conj().T
    rho /= np.trace(rho).real
    meanY = sum(0.75 * (1 - c * np.trace(O @ rho).real) for O, c in settings) / 3
    worst = max(worst, abs(meanY - (1 - np.trace(Pi @ rho).real)))
check('randomized settings: the per-episode estimate (3/4)(1 -+ outcome), in [0, 3/2], has mean equal to the leakage '
      '(500 random states)', worst < 1e-12 and np.allclose(Pi @ Pi, Pi), f'largest deviation {worst:.1e}')
Ntot, t7 = 150_000, 0.02
fail7 = math.exp(-2 * Ntot * t7 ** 2 / 1.5 ** 2)                   # one-sided Hoeffding-Azuma, range 3/2
check('150,000 episodes with randomized settings: average leakage below 5% + 0.02 = 7% except with probability '
      'below 1e-23, below the quoted 3e-4', fail7 < 1e-23 and fail7 < 3e-4 and abs(0.05 + t7 - 0.07) < 1e-12,
      f'{fail7:.2e}')
# Known blocks of settings do not certify one state: in each block the device emits an eigenstate of that block's
# observable with the value the code requires, so every block reports zero leakage, yet every emitted state has
# leakage 1/2.  Q is the observer's record of the classical input bit b, and A is emitted before b arrives.
plus, zero = np.array([1, 1]) / math.sqrt(2), np.array([1.0, 0.0])
yplus, yminus = np.array([1, 1j]) / math.sqrt(2), np.array([1, -1j]) / math.sqrt(2)
blocks_ok, leaks = True, []
for bit in (0, 1):
    q = np.eye(2)[bit]
    states = [k3(q, plus, plus),                                     # block X_A X_B: value +1
              k3(q, zero, np.eye(2)[bit]),                           # block Z_Q Z_A Z_B: value +1
              k3(q, yplus, yminus if bit == 0 else yplus)]           # block Z_Q Y_A Y_B: value -1
    for (O, c), psi in zip(settings, states):
        blocks_ok &= abs(np.vdot(psi, O @ psi).real - c) < 1e-12
        leaks.append(1 - np.vdot(psi, Pi @ psi).real)
check('known blocks of settings fail: each block reports zero leakage while every emitted state has leakage 1/2',
      blocks_ok and all(abs(x - 0.5) < 1e-12 for x in leaks), f'{len(leaks)} states, leakage {leaks[0]:.3f}')

# ---------------------------------------------------------------- Figure 3
def hb(x):
    return h2(x)


xs = np.linspace(1e-6, 1 - 1e-6, 200001)
c = np.array([hb(x) - hb(x / 2) - x / 2 for x in xs])
xstar = float(xs[int(np.argmax(c))])
m_star = 2 * hb(xstar / 2) - hb(xstar)
check('Figure 3: batch optimum near x = 0.18, capacity 0.154, m there 0.197',
      round(xstar, 2) == 0.18 and round(float(c.max()), 3) == 0.154 and round(m_star, 3) == 0.197,
      f'x* = {xstar:.4f}, capacity {c.max():.5f}, m = {m_star:.5f}')

# ---------------------------------------------------------------- Section 2, the embezzling example
ok9, rows = True, []
for n in (10, 100, 1000):
    Nlev = n * n
    psi = np.zeros(Nlev + n)
    psi[n:] = 1 / math.sqrt(Nlev)                 # levels n .. n + N - 1
    phi = np.zeros(Nlev + n)
    phi[:Nlev] = 1 / math.sqrt(Nlev)              # the same packet shifted down by n levels
    ov = float(psi @ phi)
    td = math.sqrt(max(0.0, 1 - ov * ov))         # pure states
    claim = 1 / n if PERTURB else math.sqrt(2 / n - 1 / n ** 2)
    ok9 &= abs(ov - (1 - 1 / n)) < 1e-12 and abs(td - claim) < 1e-9
    rows.append(f'n={n}: {td:.3f}')
    energy_handed_over = float(np.sum(np.arange(Nlev + n) * psi ** 2) - np.sum(np.arange(Nlev + n) * phi ** 2))
    ok9 &= abs(energy_handed_over - n) < 1e-6
check('embezzling: overlap 1 - 1/n, trace distance sqrt(2/n - 1/n^2), n quanta handed over', ok9, ', '.join(rows))
check('the distances are 0.436, 0.141 and 0.045, about sqrt(2/n)', rows == ['n=10: 0.436', 'n=100: 0.141', 'n=1000: 0.045'])

# ---------------------------------------------------------------- Section 10, the interface
def export_device(a, b, m, log):
    m ^= a                       # copy a into the blank memory before A is released
    b ^= m                       # when B arrives, add the copy into it
    m, log = log, m              # swap the copy into the supplied blank log, which is exported
    return a, b, m, log


basis = [(a, b, m, l) for a in (0, 1) for b in (0, 1) for m in (0, 1) for l in (0, 1)]
images = {export_device(*v) for v in basis}
on_blank = all(export_device(a, b, 0, 0) == (a, a ^ b, 0, a) for a in (0, 1) for b in (0, 1))
delta_zero = all(export_device(a, b, 0, 0)[0] == export_device(a, b, 0, 0)[1] ^ b for a in (0, 1) for b in (0, 1))
check('record export: a permutation of all 16 basis states, (a,b,0,0) -> (a,a^b,0,a), memory blank, delta = 0',
      len(images) == 16 and on_blank and delta_zero)


def vn(r):
    w = np.linalg.eigvalsh(r)
    w = w[w > 1e-15]
    return float(-np.sum(w * np.log(w)))


def rel(r, sigma):
    w, v = np.linalg.eigh(r)
    logr = v @ np.diag(np.log(np.clip(w, 1e-300, None))) @ v.conj().T
    u, x = np.linalg.eigh(sigma)
    logs = x @ np.diag(np.log(u)) @ x.conj().T
    return float(np.trace(r @ (logr - logs)).real)


rng11 = np.random.default_rng(11)
worst11, negative_seen = 0.0, False
for _ in range(200):
    d = 4
    H = np.diag(np.sort(rng11.uniform(0, 3, d)))
    beta = rng11.uniform(0.2, 2.0)
    gam = np.diag(np.exp(-beta * np.diag(H)))
    gam /= np.trace(gam)
    pair = []
    for _k in range(2):
        g = rng11.normal(size=(d, d)) + 1j * rng11.normal(size=(d, d))
        r = g @ g.conj().T
        pair.append(r / np.trace(r).real)
    ri, rf = pair
    betaQ = beta * float(np.trace(H @ (rf - ri)).real)
    worst11 = max(worst11, abs(betaQ - ((vn(rf) - vn(ri)) + rel(rf, gam) - rel(ri, gam))))
    negative_seen |= betaQ - (vn(rf) - vn(ri)) < 0
check('bath not initially Gibbs: beta Q = Delta S_R + D(rho_f||gamma) - D(rho_i||gamma) on 200 random states, and '
      'beta Q - Delta S_R can be negative', worst11 < 1e-9 and negative_seen, f'largest deviation {worst11:.1e}')

# ---------------------------------------------------------------- Section 10, joint records and consumed blanks
def joint_export_device(a, b, m, log):
    m ^= a                       # copy a into the blank memory before A is released
    log ^= b                     # when B arrives, copy b into the supplied blank log
    b ^= m                       # add the copy into B: B = a ^ b
    m ^= b                       # clear M against B and L: M = a ^ (a ^ b) ^ b = 0
    m ^= log
    return a, b, m, log


def mutual_info(weighted):
    # weighted: list of (x, y, probability)
    pxy, px, py = {}, {}, {}
    for x, y, w in weighted:
        pxy[(x, y)] = pxy.get((x, y), 0.0) + w
        px[x] = px.get(x, 0.0) + w
        py[y] = py.get(y, 0.0) + w
    return sum(w * math.log2(w / (px[x] * py[y])) for (x, y), w in pxy.items() if w > 0)


def entropy_bits(probs):
    return -sum(p * math.log2(p) for p in probs if p > 0)


images12 = {joint_export_device(*v) for v in basis}
on_blank12 = all(joint_export_device(a, b, 0, 0) == (a, a ^ b, 0, b) for a in (0, 1) for b in (0, 1))
carriers = {(a, a ^ b, b) for a in (0, 1) for b in (0, 1)}
outs = [(a, b, joint_export_device(a, b, 0, 0)) for a in (0, 1) for b in (0, 1)]
delta_zero12 = all(o[0] == o[1] ^ b for a, b, o in outs)
i_alone = mutual_info([(a, o[3], 0.25) for a, b, o in outs])            # a against the exported L alone
i_joint = mutual_info([(a, (o[1], o[3]), 0.25) for a, b, o in outs])    # a against (released a ^ b, exported L)
check('joint records: permutation of all 16 states, (a,b,0,0) -> (a,a^b,0,b), M blank, delta = 0; carriers (a,b,0) -> '
      '(a,a^b,b) injective; I(a:L) = 0 alone, 1 bit jointly with a^b',
      len(images12) == 16 and on_blank12 and len(carriers) == 4 and delta_zero12
      and abs(i_alone) < 1e-12 and abs(i_joint - 1) < 1e-12,
      f'I(a:L) = {i_alone:.3f}, I(a:(a^b,L)) = {i_joint:.3f}')


def blank_device(m, z, r):
    return z, r, m               # copy M, supplied blank Z, bath bit R: M <- Z, Z <- R, R <- M


images13 = {blank_device(m, z, r) for m in (0, 1) for z in (0, 1) for r in (0, 1)}
finals = [(a, blank_device(a, 0, r)) for a in (0, 1) for r in (0, 1)]   # M = a, Z blank, R uniform, all fair
m_blank = all(f[0] == 0 for _, f in finals)
i_az = mutual_info([(a, f[1], 0.25) for a, f in finals])
h_z = entropy_bits([sum(0.25 for _, f in finals if f[1] == v) for v in (0, 1)])
h_r_after = entropy_bits([sum(0.25 for _, f in finals if f[2] == v) for v in (0, 1)])
reported_with, reported_without = 0.0 + h_z, 0.0              # the heat is zero at degenerate Hamiltonian
work_from_blank = 1.0 * math.log(2) - 0.0                     # kT [D(|0><0| || I/2) - D(I/2 || I/2)], units of kT
check('consumed blanks: (M,Z,R) -> (Z,R,M) is a permutation; M reset with no heat, Z ends uniform and independent of a, '
      'bath entropy unchanged; 1 - h2(0) = 1 is met only when Delta S_Z = 1 is counted; a blank bit returns kT ln 2',
      len(images13) == 8 and m_blank and abs(i_az) < 1e-12 and abs(h_z - 1) < 1e-12 and abs(h_r_after - 1) < 1e-12
      and reported_with >= early_arm_bound(0.0) - 1e-12 and reported_without < early_arm_bound(0.0)
      and abs(work_from_blank - math.log(2)) < 1e-15,
      f'Delta S_Z = {h_z:.3f} bit, I(a:Z) = {i_az:.3f}')

# ---------------------------------------------------------------- Section 10, timing of Jun et al.
x_m, D_diff = 2.5, 1.7                                        # um, um^2/s
tau0_jun = (2 * x_m) ** 2 / D_diff
w_short = 0.71 + 1.39 / 0.5                                   # Eq. (3) with Table I, full erasure, tau = 0.5 tau_0
check('Jun et al.: tau_0 about 15 s, so the shortest cycle 0.5 tau_0 is about 7.5 s, and it costs about 3.5 kT of work, '
      'five times kT ln 2', round(tau0_jun) in (14, 15) and abs(0.5 * tau0 - 7.5) < 1e-12 and round(w_short, 1) == 3.5
      and round(w_short / math.log(2)) == 5,
      f'tau_0 = {tau0_jun:.1f} s, <W> = {w_short:.2f} kT = {w_short / math.log(2):.2f} kT ln 2')


# ---------------------------------------------------------------- Section 10, the graded control
def graded_cost(eta):
    return 2 * eta if PERTURB else h2(eta)


ok15, rows15 = True, []
for eta in (0.0, 0.01, 0.1, 0.25, 0.5):
    weights = {}
    for a in (0, 1):
        for b in (0, 1):
            for nb in (0, 1):
                w = 0.25 * (eta if nb else 1 - eta)
                if w == 0:
                    continue
                m = a                                         # the copy, made before A leaves
                out1, out2 = a, m ^ b                         # released outputs, the second computed from the copy
                r = a ^ nb                                    # the helper lent by the observer, returned unmodified
                m ^= r                                        # cleanup: add the helper into the copy
                ok15 &= (out1 == out2 ^ b) and m == nb        # exact outputs; the copy is now the noise bit
                weights[(a, r, m)] = weights.get((a, r, m), 0.0) + w
    h_m = entropy_bits([sum(w for (a, r, m), w in weights.items() if m == v) for v in (0, 1)])
    i_ar = mutual_info([(a, r, w) for (a, r, m), w in weights.items()])
    pm = [sum(w for (a, r, m), w in weights.items() if m == v) for v in (0, 1)]
    mismatch = h_m + sum(p * math.log2(p / 0.5) for p in pm if p > 0)   # a reset tuned to a fair bit
    ok15 &= abs(h_m - h2(eta)) < 1e-12 and abs((1 - i_ar) - h2(eta)) < 1e-12 and abs(mismatch - 1) < 1e-12
    rows15.append(round(graded_cost(eta), 3))
ok15 &= rows15 == [0.0, 0.081, 0.469, 0.811, 1.0]
check('graded control: exact outputs, copy plus helper = N_eta, tuned reset h2(eta) = 1 - I(a:R) (the lower bound), '
      'values 0, 0.081, 0.469, 0.811, 1; a reset tuned to a fair bit costs 1 at every eta', ok15,
      ', '.join(f'{v:.3f}' for v in rows15))

# ---------------------------------------------------------------- Section 10, what the held and lent intercepts need
def held_with_frame(a, b, frame):
    frame ^= a                   # the camera records the first well
    b ^= a                       # the held CNOT
    return a, b, frame


rows16, ok16 = [], True
for a in (0, 1):
    for b in (0, 1):
        A, B, L = held_with_frame(a, b, 0)
        ok16 &= (A == a) and (B == a ^ b) and (A == B ^ b)           # exact outputs, delta = 0
        ok16 &= (L ^ A) == 0                                         # cleaned against the held well before release
        rows16.append((a, L))
h_frame_after = entropy_bits([sum(0.25 for _, L in rows16 if L == v) for v in (0, 1)])
check('held arm with a camera frame: outputs exact; cleaned before release the frame ends blank; after both outputs '
      'have left it holds H(L | device) = 1 bit, so its reset disposes of one bit at any speed',
      ok16 and abs(h_frame_after - 1) < 1e-12, f'H(L) after release = {h_frame_after:.3f} bit')

# ---------------------------------------------------------------- Section 10, the endpoint rule
xg = np.linspace(-2.5, 2.5, 400000)                               # symmetric, avoids x = 0
dx = xg[1] - xg[0]
Eb = 8.0
V = Eb * (xg ** 2 - 1) ** 2                                         # in units of kT
right = xg > 0


def gibbs(temp, mask):
    w = np.where(mask, np.exp(-V / temp), 0.0)
    return w / (w.sum() * dx)


glob = gibbs(1.0, np.ones_like(xg, dtype=bool))
p_right = float((glob * dx)[right].sum())
loc0, loc1 = gibbs(1.0, ~right), gibbs(1.0, right)
u0, u1 = float((loc0 * V).sum() * dx), float((loc1 * V).sum() * dx)
hot1 = gibbs(1.2, right)
u1_hot = float((hot1 * V).sum() * dx)
check('endpoint rule: global equilibrium of a symmetric double well makes the bit fair; equilibrium within each well '
      'gives equal mean energies; a non-equilibrated within-well distribution in the same potential does not',
      abs(p_right - 0.5) < 1e-9 and abs(u0 - u1) < 1e-9 and u1_hot - u1 > 0.05,
      f'P(x>0) = {p_right:.6f}; U_0 = {u0:.6f}, U_1 = {u1:.6f} kT; at 1.2 T in one well U = {u1_hot:.4f} kT')

# ---------------------------------------------------------------- Section 10 and Appendix D, confidence endpoints
# The identity on both carriers keeps no record and needs no heat; on fresh fair a, b its first output is a and its
# second b, so the decoded disagreement P[a != b ^ b] is exactly 1/2.
dis18 = sum(0.25 for a in (0, 1) for b in (0, 1) if a != (b ^ b))
lo18, hi18 = 0.49, 0.51
naive18 = 1 - h2(hi18)                                              # the upper endpoint substituted as it stands
interval_min18 = min(1 - h2(d) for d in np.linspace(lo18, hi18, 2001))
clipped18 = 1 - h2(min(hi18, 0.5))                                  # delta* = min(delta_U, 1/2)
ok18 = dis18 == 0.5 and naive18 > 2.8e-4 and abs(interval_min18) < 1e-12 and abs(clipped18) < 1e-12
# The clipped rule is the least value of each bound over [0, delta_U] for every delta_U, for 1 - h2(delta),
# h2(eta) - h2(delta) and the quantum 1 - h2(e) - e log2 3, whose entropy term grows only up to e = 3/4 (value 2).
grid18 = np.linspace(0.0, 1.0, 4001)
f_q = lambda e: h2(e) + e * math.log2(3)
for u in np.linspace(0.0, 1.0, 201):
    pts = [d for d in grid18 if d <= u + 1e-12]
    ok18 &= abs((1 - h2(min(u, 0.5))) - min(1 - h2(d) for d in pts)) < 1e-6
    for eta in (0.01, 0.1, 0.25):
        ok18 &= abs((h2(eta) - h2(min(u, 0.5))) - min(h2(eta) - h2(d) for d in pts)) < 1e-6
    ok18 &= abs((1 - f_q(min(u, 0.75))) - min(1 - f_q(d) for d in pts)) < 1e-6
ok18 &= abs(f_q(0.75) - 2) < 1e-12 and f_q(0.74) < 2 and f_q(0.76) < 2
check('confidence endpoints: for the identity (delta = 1/2, no record) the upper endpoint 0.51 would claim '
      '1 - h2(0.51) > 0; delta* = min(delta_U, 1/2) gives 0, the least value over the interval; the clipped rule is the '
      'minimum over [0, delta_U] for 1 - h2, h2(eta) - h2 and, clipped at 3/4, for 1 - h2(e) - e log2 3', ok18,
      f'naive {naive18:.6e}, interval minimum {interval_min18:.1e}, clipped {clipped18:.1e}')

# ---------------------------------------------------------------- Section 10, fresh probes
# Fair marginals are not enough: if every episode receives the same fair bit A, an exact device that keeps a copy of
# each a_i holds one bit of record in all, not one per episode, although every a_i is fair and delta = 0.
N19 = 10
ok19 = True
for a in (0, 1):
    for b in (0, 1):
        m = a                                                     # copy before the first well leaves
        ok19 &= (a == (m ^ b) ^ b)                                # first output equals second output decoded with b
dist_same = {}
dist_fresh = {}
for A in (0, 1):
    rec = (A,) * N19                                              # the retained copies when a_1 = ... = a_N = A
    dist_same[rec] = dist_same.get(rec, 0.0) + 0.5
for k in range(2 ** N19):
    rec = tuple((k >> i) & 1 for i in range(N19))                 # fresh independent a_i
    dist_fresh[rec] = dist_fresh.get(rec, 0.0) + 2.0 ** -N19
marg_same = [entropy_bits([sum(p for r, p in dist_same.items() if r[i] == v) for v in (0, 1)]) for i in range(N19)]
h_same, h_fresh = entropy_bits(list(dist_same.values())), entropy_bits(list(dist_fresh.values()))
ok19 &= all(abs(x - 1) < 1e-12 for x in marg_same) and abs(h_same - 1) < 1e-12 and abs(h_fresh - N19) < 1e-9
check('fresh probes: with one fair bit repeated in all 10 episodes, the exact copy-keeping device (delta = 0) holds '
      '1 bit of record in all, against 10 bits for fresh independent inputs, though every input is fair', ok19,
      f'joint record entropy {h_same:.3f} bit (repeated) vs {h_fresh:.3f} bits (fresh)')

# ---------------------------------------------------------------- Section 10, the loan as a contract
# A fresh fair bit r returned in place of a: the uncomputed copy M = a ^ r is uniform and independent of what the device
# still holds after release, so its reset disposes of one bit, as in the early arm.
rows20r = [(a, r, a ^ r) for a in (0, 1) for r in (0, 1)]
h_m_fresh = entropy_bits([sum(0.25 for _, _, m in rows20r if m == v) for v in (0, 1)])
ok20 = abs(h_m_fresh - 1) < 1e-12


def lent_flipped(a, b, from_copy, hidden=False):
    A, B, M = a, b, 0
    H = a if hidden else 0              # an unused hidden copy of a, kept elsewhere
    M ^= A                              # copy before lending A
    first_delivery = A
    A ^= 1                              # the observer returns the well flipped
    if from_copy:
        B ^= M                          # compute the answer from the copy ...
        M ^= A                          # ... then uncompute against the returned well
    else:
        B ^= A                          # compute the answer from the returned well ...
        M ^= A                          # ... then uncompute
    delta_first = first_delivery ^ (B ^ b)
    delta_final = A ^ (B ^ b)
    return (A, B, M), delta_first, delta_final, H


for a in (0, 1):
    for b in (0, 1):
        s1, d1, f1, _ = lent_flipped(a, b, from_copy=False)
        s2, d2, f2, _ = lent_flipped(a, b, from_copy=True)
        ok20 &= s1 == (a ^ 1, a ^ b ^ 1, 1) and d1 == 1 and f1 == 0
        ok20 &= s2 == (a ^ 1, a ^ b, 1) and d2 == 0 and f2 == 1
        for fc in (False, True):
            plain, hid = lent_flipped(a, b, fc), lent_flipped(a, b, fc, hidden=True)
            ok20 &= plain[:3] == hid[:3]           # the hidden copy changes neither delta nor M
i_aM = mutual_info([(a, lent_flipped(a, b, True)[0][2], 0.25) for a in (0, 1) for b in (0, 1)])
i_aA = mutual_info([(a, lent_flipped(a, b, True)[0][0], 0.25) for a in (0, 1) for b in (0, 1)])
ok20 &= abs(i_aM) < 1e-12 and abs(i_aA - 1) < 1e-12
check('loan: a fresh bit returned in place of a strands the copy (1 bit); a flipped return leaves M in the fixed state 1 '
      'in both circuits (answer from the returned well: wrong, delta = 1; from the copy: right, delta = 0 from the first '
      'delivery, 1 from the final release); I(a:M) = 0, I(a:A) = 1; a hidden unused copy changes neither', ok20,
      f'H(M) fresh return = {h_m_fresh:.3f} bit, I(a:M) = {i_aM:.3f}, I(a:A) = {i_aA:.3f}')

# ---------------------------------------------------------------- Section 5, side information with a Hamiltonian
q21 = 1 / (1 + math.exp(math.log(2)))                            # excited population at beta E = ln 2
entropy_only = h2(q21)
reset_cost = math.log2(1 + math.exp(-math.log(2)))              # ln Z / ln 2: free-energy difference to the ground state
ys = np.linspace(0.0, 1.0, 30001)
vals = [h2(float(y)) - float(y) for y in ys]                    # Theorem 4.2(b) at p = 1, beta Delta = ln 2
full_reset, ystar = max(vals), float(ys[int(np.argmax(vals))])
check('Section 5: a Gibbs qubit at beta E = ln 2 (excited 1/3) resets for h2(1/3) - 1/3 = log2(3/2) = 0.585 bits, '
      'not the entropy 0.918; this is max_y [h2(y) - y], the full reset of Theorem 4.2(b) at p = 1, attained at y = 1/3',
      abs(q21 - 1 / 3) < 1e-12 and abs(reset_cost - (h2(1 / 3) - 1 / 3)) < 1e-12
      and abs(reset_cost - math.log2(1.5)) < 1e-12 and round(reset_cost, 3) == 0.585 and round(entropy_only, 3) == 0.918
      and abs(full_reset - reset_cost) < 1e-8 and abs(ystar - 1 / 3) < 1e-4,
      f'reset {reset_cost:.6f}, entropy {entropy_only:.6f}, max_y {full_reset:.6f} at y = {ystar:.5f}')

print()
if PERTURB:
    # All three corruptions must be caught: the early-arm bound (check 1), the embezzling distance (check 9) and the
    # graded-control curve (check 15).
    targets = {'early arm': 'the naive bound 1 - delta', 'embezzling: overlap': 'the distance 1/n',
               'graded control': 'the linear cost 2 eta'}
    missed = [what for prefix, what in targets.items() if not any(n.startswith(prefix) for n in failed_names)]
    if missed:
        print('NEGATIVE CONTROL DID NOT FIRE: ' + ' and '.join(missed) + ' accepted')
        sys.exit(1)
    print(f'negative control fired as required (all three targeted checks failed; {failed} check(s) failed under --perturb)')
    sys.exit(0)
if failed:
    print(f'{failed} check(s) failed.')
    sys.exit(1)
print('All checks passed.')
