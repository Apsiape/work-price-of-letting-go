"""The free-energy ledger of a controller that returns only in state (Corollary "A controller returned only in state is
a second battery" and its appendix proof).

Checks:
  1. the payment swap: for many (k, N), the map exchanging |k+j>_L|0> with |j>_L|1> (j = 1..N) and fixing every other
     basis vector of the ladder (levels 1..k+N, spacing omega) times the register W_2 (gap k omega) is a permutation,
     an involution, commutes with the total Hamiltonian, and sends the classical ladder rho_L (x) |0><0| to
     rho_L' (x) |1><1| and the pure ladder psi (x) |0> to phi (x) |1> exactly;
  2. the classical ladder in exact rationals: the uniform mixtures on levels k+1..k+N and 1..N are at trace distance
     exactly k/N (N >= k); the entropy ln N is unchanged and the energy drops by exactly k omega; N = ceil(k/eta) gives
     k/N <= eta and N >= k for eta <= 1; the range (k+N-1) omega is at most (1 + 1/eta)(n[B-w] + omega), with
     0 <= k omega - n[B-w] < omega;
  3. the sine packet of the pure ladder: sum a_j^2 = 1, a_{j-1} + a_{j+1} = 2 cos(theta) a_j with a_0 = a_{N+1} = 0,
     and <psi|J psi> = cos(theta), theta = pi/(N+1), in 40-digit arithmetic;
  4. the shift of the pure ladder: J is isometric on the vectors it acts on, phi = J^k psi,
     ||psi - J psi||^2 = 2 - 2cos(theta) <= theta^2, the trace distance is at most ||phi - psi|| <= k pi/(N+1), and
     N = ceil(k pi/eta) gives at most eta; the ladder stays pure and loses exactly k omega;
  5. the continuity bound of part (b): F(alpha) - F(alpha') <= kT[x K + r_0(x)], K = beta span(H) + ln d, at trace
     distance x, on random and near-extremal pairs, and x ln d + r_0(x) increases with x;
  6. sharpness, worked on X-dephasing with the battery at the capacity: the ladder's own bound from part (b),
     span + kT ln d >= (n Delta - kT r_0(eta))/eta, holds, and its range exceeds (n Delta - kT r_0(eta))/eta by at most
     the factor (1 + eta)(n Delta + omega)/(n Delta - kT r_0(eta)) for the classical ladder, which tends to 1 + eta,
     and (pi + eta)(n Delta + omega)/(n Delta - kT r_0(eta)) for the pure one.
"""
from fractions import Fraction
import math

import mpmath as mp
import numpy as np

from qtools import Report, S, herm, random_density

R = Report("The free-energy ledger of a controller that returns only in state")
rng = np.random.default_rng(20261012)
mp.mp.dps = 40


def sine_packet(N):
    return np.array([math.sqrt(2 / (N + 1)) * math.sin(j * math.pi / (N + 1)) for j in range(1, N + 1)])


def pure_ladder(k, N):
    """psi on levels k+1..k+N and phi on levels 1..N of a ladder with levels 1..k+N (index = level - 1)."""
    a = sine_packet(N)
    psi, phi = np.zeros(k + N), np.zeros(k + N)
    psi[k:k + N] = a
    phi[0:N] = a
    return psi, phi


def r0(x):
    return 0.0 if x == 0 else (1 + x) * math.log(1 + x) - x * math.log(x)


# ---------------------------------------------------------------------------------------------------------------------
# 1. The payment swap
ok1 = True
for k in range(1, 7):
    for N in range(1, 9):
        dimL = k + N
        dim = 2 * dimL
        idx = lambda lev, b: 2 * (lev - 1) + b  # level 1..k+N, register bit b
        perm = list(range(dim))
        for j in range(1, N + 1):
            a_, b_ = idx(k + j, 0), idx(j, 1)
            perm[a_], perm[b_] = b_, a_
        ok1 &= sorted(perm) == list(range(dim))
        ok1 &= all(perm[perm[i]] == i for i in range(dim))
        energy = [lev + (k if b else 0) for lev in range(1, dimL + 1) for b in (0, 1)]  # units of omega, integers
        ok1 &= all(energy[perm[i]] == energy[i] for i in range(dim))
        P = np.zeros((dim, dim))
        for i in range(dim):
            P[perm[i], i] = 1
        psi, phi = pure_ladder(k, N)
        ok1 &= np.max(np.abs(P @ np.kron(psi, [1.0, 0.0]) - np.kron(phi, [0.0, 1.0]))) < 1e-15
        rhoL = np.diag([1.0 / N if k + 1 <= lev <= k + N else 0.0 for lev in range(1, dimL + 1)])
        rhoL2 = np.diag([1.0 / N if 1 <= lev <= N else 0.0 for lev in range(1, dimL + 1)])
        out = P @ np.kron(rhoL, np.diag([1.0, 0.0])) @ P.T
        ok1 &= np.max(np.abs(out - np.kron(rhoL2, np.diag([0.0, 1.0])))) < 1e-15
R.check("payment swap: a permutation and an involution that conserves the total energy (integers) and maps "
        "rho_L (x) |0><0| to rho_L' (x) |1><1| and psi (x) |0> to phi (x) |1>, for k = 1..6 and N = 1..8", bool(ok1))

# ---------------------------------------------------------------------------------------------------------------------
# 2. The classical ladder, exact
ok2 = True
for k in range(1, 40):
    for N in range(k, 200, 7):
        p = {k + j: Fraction(1, N) for j in range(1, N + 1)}
        q = {j: Fraction(1, N) for j in range(1, N + 1)}
        td = sum(abs(p.get(l, 0) - q.get(l, 0)) for l in range(1, k + N + 1)) / 2
        ok2 &= td == Fraction(k, N)
        ok2 &= sum(l * v for l, v in p.items()) - sum(l * v for l, v in q.items()) == k
ok2 &= abs(S(np.eye(13) / 13) - math.log(13)) < 1e-12
for eta in (Fraction(1), Fraction(1, 2), Fraction(1, 10), Fraction(1, 100), Fraction(3, 1000)):
    for k in (1, 3, 17, 100, 1000):
        N = math.ceil(Fraction(k) / eta)
        ok2 &= Fraction(k, N) <= eta and N >= k
for n in (10, 1000, 10 ** 6):
    for gap in (Fraction(1, 10), Fraction(1, 2), Fraction(2)):       # B - w in units of omega
        for eta in (Fraction(1, 2), Fraction(1, 20), Fraction(1, 1000)):
            k = math.ceil(n * gap)
            N = math.ceil(Fraction(k) / eta)
            ok2 &= 0 <= k - n * gap < 1
            ok2 &= (k + N - 1) <= (1 + 1 / eta) * (n * gap + 1)
R.check("classical ladder (exact rationals): trace distance exactly k/N, energy drop exactly k omega, entropy ln N "
        "unchanged; N = ceil(k/eta) gives k/N <= eta and N >= k; range (k+N-1) omega <= (1 + 1/eta)(n[B-w] + omega)", bool(ok2))

# ---------------------------------------------------------------------------------------------------------------------
# 3. The sine packet in 40 digits
ok3, worst3 = True, mp.mpf(0)
for N in (1, 2, 3, 5, 10, 37, 100, 400):
    th = mp.pi / (N + 1)
    a = [mp.mpf(0)] + [mp.sqrt(mp.mpf(2) / (N + 1)) * mp.sin(j * th) for j in range(1, N + 1)] + [mp.sin((N + 1) * th)]
    norm = mp.fsum(x ** 2 for x in a)
    eig = max((abs(a[j - 1] + a[j + 1] - 2 * mp.cos(th) * a[j]) for j in range(1, N + 1)), default=mp.mpf(0))
    shift = mp.fsum(a[j] * a[j + 1] for j in range(1, N))
    worst3 = max(worst3, abs(norm - 1), eig, abs(shift - mp.cos(th)), abs(a[N + 1]))
ok3 &= worst3 < mp.mpf(10) ** -35
R.check("pure ladder, sine packet: sum a_j^2 = 1, a_{j-1} + a_{j+1} = 2cos(theta) a_j with a_0 = a_{N+1} = 0, and "
        "<psi|J psi> = cos(pi/(N+1)), 40 digits, N up to 400", bool(ok3), f"max residual {float(worst3):.1e}")

# ---------------------------------------------------------------------------------------------------------------------
# 4. The shift of the pure ladder
ok4, ratio_max = True, 0.0
for k in (1, 2, 3, 5, 10, 25, 50):
    for N in (1, 2, 5, 10, 50, 200, 1000, 5000):
        psi, phi = pure_ladder(k, N)
        v = psi.copy()
        for i in range(k):
            ok4 &= v[0] == 0.0  # level 1 carries no weight before each lowering
            v = np.concatenate([v[1:], [0.0]])
        ok4 &= np.max(np.abs(v - phi)) < 1e-15
        th = math.pi / (N + 1)
        one = np.linalg.norm(psi - np.concatenate([psi[1:], [0.0]]))
        ok4 &= abs(one ** 2 - (2 - 2 * math.cos(th))) < 1e-12 and one <= th + 1e-15
        dist = math.sqrt(max(0.0, 1 - float(np.dot(phi, psi)) ** 2))
        euclid = float(np.linalg.norm(phi - psi))
        bound = k * math.pi / (N + 1)
        ok4 &= dist <= euclid + 1e-14 and euclid <= k * one + 1e-12 and euclid <= bound + 1e-12
        ratio_max = max(ratio_max, dist / bound)
        levels = np.arange(1, k + N + 1)
        ok4 &= abs(float(np.dot(psi ** 2, levels) - np.dot(phi ** 2, levels)) - k) < 1e-9
for eta in (1.0, 0.5, 0.1, 0.01, 0.001):
    for k in (1, 3, 17, 100, 1000):
        N = math.ceil(k * math.pi / eta)
        ok4 &= k * math.pi / (N + 1) <= eta
R.check("pure ladder, shift: J isometric on the vectors it acts on, phi = J^k psi, ||psi - J psi||^2 = 2 - 2cos(theta) "
        "<= theta^2, T(phi, psi) <= ||phi - psi|| <= k pi/(N+1), N = ceil(k pi/eta) gives at most eta, energy drop k omega",
        bool(ok4), f"exact distance reaches {ratio_max:.3f} of k pi/(N+1)")

# ---------------------------------------------------------------------------------------------------------------------
# 5. The continuity bound of part (b)


def free_energy(rho, H, kT):
    return float(np.real(np.trace(H @ rho))) - kT * S(rho)


ok5, tight = True, 0.0
for trial in range(3000):
    d = int(rng.integers(2, 9))
    H = np.diag(np.sort(rng.normal(size=d)) * rng.uniform(0.1, 5))
    kT = float(rng.uniform(0.05, 3))
    alpha = random_density(d, rng, rank=int(rng.integers(1, d + 1)))
    kind = trial % 3
    if kind == 0:
        alpha2 = random_density(d, rng)
    elif kind == 1:      # small perturbation
        alpha2 = herm((1 - 0.02) * alpha + 0.02 * random_density(d, rng))
    else:                # near-extremal: a pure ground state against a mixture with the maximally mixed state
        v = np.zeros(d); v[0] = 1
        alpha = np.outer(v, v).astype(complex)
        lam = float(rng.uniform(0, 1))
        alpha2 = (1 - lam) * alpha + lam * np.eye(d) / d
        H = np.diag(np.concatenate([[0.0], np.full(d - 1, float(rng.uniform(0.1, 3)))]))
    x = 0.5 * float(np.sum(np.abs(np.linalg.eigvalsh(herm(alpha - alpha2)))))
    span = float(np.max(np.diag(H)) - np.min(np.diag(H)))
    K = span / kT + math.log(d)
    lhs = free_energy(alpha, H, kT) - free_energy(alpha2, H, kT)
    rhs = kT * (x * K + r0(x))
    ok5 &= lhs <= rhs + 1e-10
    if rhs > 0:
        tight = max(tight, lhs / rhs)
xs = np.linspace(1e-9, 1, 2001)
for d in (2, 3, 10, 1000):
    vals = [x * math.log(d) + r0(x) for x in xs]
    ok5 &= all(b >= a for a, b in zip(vals, vals[1:]))
R.check("continuity: F(alpha) - F(alpha') <= kT[x K + r_0(x)] with K = beta span(H) + ln d, on 3000 random and "
        "near-extremal pairs; x ln d + r_0(x) increases with x", bool(ok5), f"largest ratio of the two sides {tight:.3f}")

# ---------------------------------------------------------------------------------------------------------------------
# 6. Sharpness on X-dephasing with the battery at the capacity
ok6, rows = True, []
for E, beta in ((1.0, 1.0), (1.0, math.log(2))):
    kT = 1 / beta
    delta = E / 2 - kT * math.log(math.cosh(beta * E / 2))     # B - C
    for n in (10 ** 3, 10 ** 6):
        for eta in (0.1, 0.01):
            omega = E
            k = math.ceil(n * delta / omega)
            need = (n * delta - kT * r0(eta)) / eta                 # part (b) applied to the ladder: span + kT ln d >= need
            for name, N, factor in (("classical", math.ceil(k / eta), 1 + eta),
                                    ("pure", math.ceil(k * math.pi / eta), math.pi + eta)):
                span = (k + N - 1) * omega
                ok6 &= span + kT * math.log(k + N) >= need
                limit = factor * (n * delta + omega) / (n * delta - kT * r0(eta))
                ok6 &= span / need <= limit
                if n == 10 ** 6 and eta == 0.01:
                    rows.append(f"{name} bE={beta * E:.2f}: range/need {span / need:.5f} (limit {limit:.5f})")
R.check("sharpness (X-dephasing at the capacity): each ladder meets the bound of part (b) applied to itself, within "
        "(1 + eta)(nD + omega)/(nD - kT r_0) for the classical ladder and (pi + eta)(...) for the pure one", bool(ok6),
        "; ".join(rows))

R.close()
