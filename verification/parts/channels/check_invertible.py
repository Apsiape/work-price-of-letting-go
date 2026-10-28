"""Invertible environments (Lemma "Invertible environment", Appendix "Invertible environments").

Checks:
  1. the Alicki-Fannes-Winter bound |S(X|Y)_rho - S(X|Y)_sigma| <= g_{dim X}(t) on 3000 pairs, with Y up to four times
     larger than X;
  2. every unit vector of Q (x) A is (X (x) I)|psi_rho> with ||X||^2 <= 1/lambda_min(rho); pure states with fidelity
     >= 1 - eps are within trace distance sqrt(2 eps);
  3. exact extensions: for amplitude damping (p = 0.3, 0.5, 0.8) every exact real-time round, whatever the device's
     state, has S(QO|F) = S(Phi^c(rho));
  4. approximate extensions from 600 perturbed real-time rounds: with M = ||(Phi^c)^{-1}||_diamond (SDP),
     1/2||sigma_QOF - chi_rho x sigma_F||_1 <= t(eps) = sqrt(2 eps)(1 + M/lambda_min(rho)) and
     S(QO|F) >= S(Phi^c(rho)) - g_{d_Q d_O}(min{1, t(eps)}), with many rounds where the bound is informative.
"""
import math

import numpy as np

from qtools import (Report, choi_of_map, complementary, cond_entropy, diamond_norm_herm, dm, entropy, g_afw, near_unitary,
                    ptrace, random_density, random_unitary, trace_norm)

R = Report("Invertible environments")
rng = np.random.default_rng(20261021)

# ---------------------------------------------------------------------------------------------------- 1. AFW
ok, best = True, 0.0
for trial in range(3000):
    dX = int(rng.integers(2, 4))
    dY = dX * int(rng.integers(1, 5))
    r = random_density(dX * dY, rng, rank=int(rng.integers(1, dX * dY + 1)))
    if trial % 3 == 0:                               # near a maximally entangled state
        phi = sum(np.kron(np.eye(dX)[i], np.eye(dY)[i]) for i in range(dX)) / math.sqrt(dX)
        u = 10 ** rng.uniform(-4, 0)
        r = (1 - u) * dm(phi) + u * np.kron(np.eye(dX) / dX, random_density(dY, rng))
        s = dm(phi)
    else:
        u = 10 ** rng.uniform(-3, 0)
        s = (1 - u) * r + u * random_density(dX * dY, rng)
    t = 0.5 * trace_norm(r - s)
    diff = abs(cond_entropy(r, [dX, dY], [0]) - cond_entropy(s, [dX, dY], [0]))
    bnd = g_afw(dX, min(1.0, t))
    ok &= diff <= bnd + 1e-10
    best = max(best, diff / bnd if bnd > 0 else 0)
R.check("|S(X|Y)_rho - S(X|Y)_sigma| <= g_{dim X}(t) whatever the size of Y (3000 pairs)", ok and best > 0.3,
        f"largest ratio {best:.3f}")

# ---------------------------------------------------------------------------------------------------- 2. vectors
ok = True
for _ in range(300):
    d = int(rng.integers(2, 5))
    rho = random_density(d, rng)
    w, v = np.linalg.eigh(rho)
    psi = sum(math.sqrt(w[i]) * np.kron(v[:, i].conj(), v[:, i]) for i in range(d))      # Q (x) A, Q-marginal rho^T
    target = random_unitary(d * d, rng)[:, 0]
    # solve target = (X x I) psi: X = T rho^{-1/2}-type, with T the reshaped target
    Tm = target.reshape(d, d)
    Pm = psi.reshape(d, d)
    Xm = Tm @ np.linalg.inv(Pm)
    ok &= np.allclose(np.kron(Xm, np.eye(d)) @ psi, target, atol=1e-10)
    ok &= np.linalg.norm(Xm, 2) ** 2 <= 1 / w.min() + 1e-9
    a, b = random_unitary(d, rng)[:, 0], random_unitary(d, rng)[:, 0]
    F = abs(np.vdot(a, b))
    eps = 1 - F
    ok &= 0.5 * trace_norm(dm(a) - dm(b)) <= math.sqrt(2 * eps) + 1e-12
R.check("every unit vector of Q (x) A is (X x I)|psi_rho> with ||X||^2 <= 1/lambda_min(rho); fidelity 1 - eps between "
        "pure states gives trace distance <= sqrt(2 eps)", bool(ok))


# ---------------------------------------------------------------------------------------------------- 3-4. damping
def damping_unitary(p):
    s = math.sqrt(1 - p)
    U = np.zeros((4, 4))
    U[0, 0] = 1
    U[:, 2] = [0, math.sqrt(p), s, 0]
    U[:, 1] = [0, s, -math.sqrt(p), 0]
    U[3, 3] = 1
    return U                                           # on S (x) E, |S E>


def round_state(U_SD, rho, rD, d, dD):
    """Global state after one round: Q (x) O (x) D' (x) F, with Q purifying the input and F purifying the device."""
    w, v = np.linalg.eigh(rho)
    psi = sum(math.sqrt(max(w[i], 0)) * np.kron(v[:, i].conj(), v[:, i]) for i in range(d))      # Q (x) S
    wD, vD = np.linalg.eigh(rD)
    phi = sum(math.sqrt(max(wD[i], 0)) * np.kron(vD[:, i], np.eye(dD)[i]) for i in range(dD))      # D (x) F
    vec = np.kron(psi, phi).reshape(d, d * dD, dD)
    vec = np.einsum("ab,qbf->qaf", U_SD, vec).reshape(-1)
    return np.outer(vec, vec.conj())


ok_exact = True
for p in (0.3, 0.5, 0.8):
    U = damping_unitary(p)
    K = [np.array([[1, 0], [0, math.sqrt(1 - p)]]), np.array([[0, math.sqrt(p)], [0, 0]])]
    for _ in range(40):
        dM = 2
        dD = 2 * dM
        rD = np.kron(dm([1, 0]), random_density(dM, rng))                   # environment qubit ground, memory random
        Ufull = np.kron(U, np.eye(dM))
        rho = random_density(2, rng)
        full = round_state(Ufull, rho, rD, 2, dD)
        sQOF = ptrace(full, [2, 2, dD, dD], [0, 1, 3])
        ok_exact &= abs(cond_entropy(sQOF, [2, 2, dD], [0, 1]) - entropy(complementary(K, rho))) < 1e-9
R.check("exact real-time rounds of amplitude damping (p = 0.3, 0.5, 0.8, random device memories): S(QO|F) = S(Phi^c(rho))",
        bool(ok_exact))

Ms = {}
for p in (0.3, 0.5, 0.8):
    Kc = lambda X, p=p: np.array([[X[0, 0] + (1 - p) * X[1, 1], math.sqrt(p) * X[0, 1]],
                                   [math.sqrt(p) * X[1, 0], p * X[1, 1]]])
    inv = lambda Y, p=p: np.array([[Y[0, 0] - (1 - p) / p * Y[1, 1], Y[0, 1] / math.sqrt(p)],
                                    [Y[1, 0] / math.sqrt(p), Y[1, 1] / p]])
    assert np.allclose(inv(Kc(np.array([[0.3, 0.1j], [-0.1j, 0.7]]))), [[0.3, 0.1j], [-0.1j, 0.7]])
    Ms[p] = diamond_norm_herm(choi_of_map(inv, 2), 2, 2)
ok_t, ok_S = True, True
informative, worst = 0, 1e9
for trial in range(600):
    p = [0.3, 0.5, 0.8][trial % 3]
    U = damping_unitary(p)
    K = [np.array([[1, 0], [0, math.sqrt(1 - p)]]), np.array([[0, math.sqrt(p)], [0, 0]])]
    dM = 2
    dD = 2 * dM
    rD = np.kron(dm([1, 0]), random_density(dM, rng)) if rng.random() < 0.7 else random_density(dD, rng)
    eps_u = 10 ** rng.uniform(-6, -1)
    Ufull = near_unitary(np.kron(U, np.eye(dM)), eps_u, rng)
    rho = random_density(2, rng)
    if rng.random() < 0.5:
        rho = 0.5 * rho + 0.25 * np.eye(2)
    full = round_state(Ufull, rho, rD, 2, dD)
    sQOF = ptrace(full, [2, 2, dD, dD], [0, 1, 3])
    sQO = ptrace(sQOF, [2, 2, dD], [0, 1])
    sF = ptrace(sQOF, [2, 2, dD], [2])
    # ideal chi_rho
    w, v = np.linalg.eigh(rho)
    psi = sum(math.sqrt(w[i]) * np.kron(v[:, i].conj(), v[:, i]) for i in range(2))
    chi = sum(np.kron(np.eye(2), k) @ dm(psi) @ np.kron(np.eye(2), k).conj().T for k in K)
    eps = 0.5 * trace_norm(sQO - chi)
    t = math.sqrt(2 * eps) * (1 + Ms[p] / w.min())
    ok_t &= 0.5 * trace_norm(sQOF - np.kron(chi, sF)) <= t + 1e-9
    bound = entropy(complementary(K, rho)) - g_afw(4, min(1.0, t))
    S = cond_entropy(sQOF, [2, 2, dD], [0, 1])
    ok_S &= S >= bound - 1e-9
    worst = min(worst, S - bound)
    informative += bound > 0
R.check("||(Phi^c)^{-1}||_diamond for damping p = 0.3, 0.5, 0.8 (SDP)", abs(Ms[0.5] - 3) < 1e-6,
        ", ".join(f"p={p}: {m:.4f}" for p, m in Ms.items()))
R.check("1/2||sigma_QOF - chi_rho x sigma_F||_1 <= sqrt(2 eps)(1 + M/lambda_min(rho)) (600 perturbed rounds)", bool(ok_t))
R.check("S(QO|F) >= S(Phi^c(rho)) - g_4(min{1, t(eps)}) on every round, informative on many", ok_S and informative >= 100,
        f"{informative} informative rounds, smallest slack {worst:.3e}")
R.close()
