"""A correlated process with hidden memory (Section 7, "A correlated process").

The process draws a hidden uniform bit b; slot 1 applies U_b (U_0 = I, U_1 = e^{itZ}); slot 2 applies V_b (V_0 = X,
V_1 = Hadamard); both slots carry H = E|1><1|.  Energies are in units of E.

Checks:
  1. the process with a classical copy of b as the side output has S(Z|F) = 0 for every tester, so its score is the
     energy the second slot supplies; the largest energy over testers (SDP) is v_t = (E/2) sqrt(3/2 + cos 2t + sin 2t)
     for 0 < t < pi/8, and (E/2)(1 + 1/sqrt2) for pi/8 <= t <= 7pi/8 (t is defined modulo pi);
  2. the same value from the fidelity-constrained pair program: max (1/2) sum_b Tr D(V_b) rho_b over pairs of states
     with root fidelity ||sqrt(rho_0) sqrt(rho_1)||_1 >= |cos t|;
  3. every tester produces a pair with root fidelity >= |cos t|, and every such pair is produced by an explicit tester
     (Uhlmann purifications, an ancilla of overlap cos t/F, and an isometry matching the Gram matrices);
  4. the relative unitary of the two branches has four distinct eigenphases +-t +-pi/4;
  5. the branchwise worst case (E/2)(1 + 1/sqrt2) exceeds v_t for 0 < t < pi/8;
  6. the state kept on the rare branch (first input kept, half of an EPR pair emitted) is the tester record: the second
     inputs on both branches are recovered from it by the link product with |U_b>><<U_b|;
  7. a positive heat effect D with Tr D Z = v_t - E_main(Z) for every tester exists (SDP); main-branch energy plus the
     rare-branch heat is v_t on random adaptive testers; the effect on the kept state has norm c||D||/delta <= 8E/delta;
  8. the constant chain: delta = N^-3, effect norm 8E N^3, hot gap E N^8 give a heat remainder O(E N^-3) <= O(E/N^2)
     and error N delta = N^-2.
"""
import math

from qtools import HAD, I2, X, Report, dm, herm, ket, random_density, sqrtm_psd  # noqa: I001 (sets warning filters)
import cvxpy as cp
import numpy as np
from combs import Realization, Tester, TesterLP, energy_matrix, link, random_tester, simulate

R = Report("A correlated process with hidden memory")
rng = np.random.default_rng(8)
E = 1.0
H = np.diag([0.0, E]).astype(complex)
Dop = lambda V: V.conj().T @ H @ V - H


def vt(t):
    return E / 2 * math.sqrt(1.5 + math.cos(2 * t) + math.sin(2 * t))


def hidden(t):
    Us = [I2, np.diag([np.exp(1j * t), np.exp(-1j * t)])]
    Vs = [X, HAD]
    c1 = sum(np.kron(Us[b], dm(ket((b,)))) for b in (0, 1))      # (port, bath = b)
    c2 = sum(np.kron(Vs[b], dm(ket((b,)))) for b in (0, 1))
    return Realization.collision([2, 2], I2 / 2, [c1, c2]), Us, Vs


def expected(t):
    tt = t % math.pi
    tt = min(tt, math.pi - tt)
    return vt(tt) if tt < math.pi / 8 else E / 2 * (1 + 1 / math.sqrt(2))


# 1. the energy program over testers -----------------------------------------------------------------------------
lp = TesterLP([2, 2])
ts = [0.05, 0.2, 0.3, math.pi / 8 - 1e-3, math.pi / 8, 0.5, 0.9, 1.3, 2.0, math.pi - 0.3, math.pi - 0.05]
vals = {}
wS = 0.0
for t in ts:
    real, Us, Vs = hidden(t)
    Ge = energy_matrix(real, [H, H])
    _, v = lp.solve(Ge)
    vals[t] = v
    for _ in range(5):
        s = simulate(real, random_tester([2, 2], rng), [H, H])
        wS = max(wS, abs(s["SZF"]))
R.check("with a classical copy of b as the side output, S(Z|F) = 0 for every tester", wS < 1e-12, f"{wS:.1e}")
small = [t for t in ts if t < math.pi / 8]
R.check("the largest second-slot energy over testers is v_t = (E/2) sqrt(3/2 + cos 2t + sin 2t) for 0 < t < pi/8",
        all(abs(vals[t] - vt(t)) < 1e-7 for t in small), ", ".join(f"t={t:.3f}: {vals[t]:.8f}/{vt(t):.8f}" for t in small))
big = [t for t in ts if math.pi / 8 <= t <= 7 * math.pi / 8]
R.check("for pi/8 <= t <= 7pi/8 the value is (E/2)(1 + 1/sqrt2)", all(abs(vals[t] - E / 2 * (1 + 2 ** -0.5)) < 1e-7 for t in big),
        ", ".join(f"{vals[t]:.6f}" for t in big))
wrap = [math.pi - 0.3, math.pi - 0.05]
R.check("t is defined modulo pi: for t = pi - 0.3 and pi - 0.05 the value is v_0.3 and v_0.05, below (E/2)(1 + 1/sqrt2)",
        all(abs(vals[t] - expected(t)) < 1e-7 and vals[t] < E / 2 * (1 + 2 ** -0.5) - 1e-3 for t in wrap),
        "so 'for t > pi/8' holds only up to 7pi/8")

# 2. the fidelity-constrained pair program ----------------------------------------------------------------------
def pair_program(t):
    r0 = cp.Variable((2, 2), hermitian=True)
    r1 = cp.Variable((2, 2), hermitian=True)
    Yv = cp.Variable((2, 2), complex=True)
    cons = [cp.bmat([[r0, Yv], [Yv.H, r1]]) >> 0, cp.real(cp.trace(r0)) == 1, cp.real(cp.trace(r1)) == 1,
            cp.real(cp.trace(Yv)) >= abs(math.cos(t))]
    obj = 0.5 * cp.real(cp.trace(Dop(X) @ r0)) + 0.5 * cp.real(cp.trace(Dop(HAD) @ r1))
    pr = cp.Problem(cp.Maximize(obj), cons)
    pr.solve(solver="CLARABEL")
    return pr.value


R.check("the fidelity-constrained pair program gives the same values at every t",
        all(abs(pair_program(t) - vals[t]) < 1e-6 for t in ts))

# 3. reachable pairs ----------------------------------------------------------------------------------------------
def fid(a, b):
    return float(np.sum(np.linalg.svd(sqrtm_psd(a) @ sqrtm_psd(b), compute_uv=False)))


minF = 1e9
for t in (0.1, 0.3):
    real, Us, Vs = hidden(t)
    for _ in range(40):
        te = random_tester([2, 2], rng, int(rng.integers(1, 4)))
        Zr = te.record()
        # second inputs on each branch: link product of the record with the slot-1 Choi of U_b
        r2 = []
        for b in (0, 1):
            u = np.array([Us[b][j, i] for i in range(2) for j in range(2)])        # |U_b>> on (I_1, O_1)
            Rb = np.outer(u, u.conj())
            r2.append(np.einsum("ab,aibk->ik", Rb, Zr.reshape(4, 2, 4, 2)))
        minF = min(minF, fid(r2[0], r2[1]) - math.cos(t))
R.check("every tester produces second inputs with root fidelity >= cos t (80 random adaptive testers)", minF > -1e-10,
        f"smallest margin {minF:.2e}")


def tester_for_pair(t, rho0, rho1):
    """Explicit tester producing rho0, rho1 as second inputs on the two branches."""
    F = fid(rho0, rho1)
    s0, s1 = sqrtm_psd(rho0), sqrtm_psd(rho1)
    om = np.eye(2).reshape(-1)
    M = s0 @ s1                                                                   # Uhlmann unitary from the polar part
    u, _, vh = np.linalg.svd(M)
    Wu = (u @ vh).conj().T
    phi0 = np.kron(s0, I2) @ om                                                   # purifications on (I_2, p)
    phi1 = np.kron(s1, Wu.T) @ om
    ov = np.vdot(phi0, phi1)
    phi1 = phi1 * np.exp(-1j * np.angle(ov))
    c_ = math.cos(t) / F
    anc0, anc1 = ket((0,)), c_ * ket((0,)) + math.sqrt(max(0.0, 1 - c_ * c_)) * ket((1,))
    targets = [np.kron(phi0, anc0), np.kron(phi1, anc1)]                          # (I_2, p, anc)
    psi = (ket((0, 0)) + ket((1, 1))) / math.sqrt(2)                              # (I_1, R)
    Us = [I2, np.diag([np.exp(1j * t), np.exp(-1j * t)])]
    sources = [np.kron(Us[b], I2) @ psi for b in (0, 1)]                          # (O_1, R)
    # isometry on span(sources) with the right Gram matrix, completed on the complement
    S = np.array(sources).T
    T = np.array(targets).T
    L = T @ np.linalg.pinv(S)
    Q, _ = np.linalg.qr(np.hstack([S, rng.standard_normal((4, 2))]))
    comp_in = Q[:, 2:4]
    Qo, _ = np.linalg.qr(np.hstack([T, rng.standard_normal((8, 6))]))
    L = L + Qo[:, 2:4] @ comp_in.conj().T
    return Tester([2, 2], psi.reshape(2, 2), [L], [2, 4]), L


wr, wi = 0.0, 0.0
for t in (0.1, 0.3):
    real, Us, _ = hidden(t)
    for _ in range(30):
        while True:
            rho0, rho1 = random_density(2, rng), random_density(2, rng)
            if fid(rho0, rho1) >= math.cos(t):
                break
        te, L = tester_for_pair(t, rho0, rho1)
        wi = max(wi, np.abs(L.conj().T @ L - np.eye(4)).max())
        Zr = te.record()
        for b, target in ((0, rho0), (1, rho1)):
            u = np.array([Us[b][j, i] for i in range(2) for j in range(2)])
            r2 = np.einsum("ab,aibk->ik", np.outer(u, u.conj()), Zr.reshape(4, 2, 4, 2))
            wr = max(wr, np.abs(r2 - target).max())
R.check("every pair with root fidelity >= cos t is produced by an explicit tester (60 random pairs)",
        wr < 1e-10 and wi < 1e-10, f"{wr:.1e}, isometry defect {wi:.1e}")

# 4. eigenphases -------------------------------------------------------------------------------------------------
ok4 = True
for t in np.linspace(0.01, math.pi / 8 - 0.01, 30):
    W = np.kron(np.diag([np.exp(1j * t), np.exp(-1j * t)]), HAD @ X)
    ph = np.sort(np.angle(np.linalg.eigvals(W)))
    ok4 &= np.allclose(ph, np.sort([t + math.pi / 4, t - math.pi / 4, -t + math.pi / 4, -t - math.pi / 4]))
    ok4 &= np.min(np.diff(ph)) > 1e-3
R.check("the relative unitary e^{itZ} (x) (Hadamard X) has four distinct eigenphases +-t +-pi/4 for 0 < t < pi/8", ok4)

# 5. branchwise worst case ------------------------------------------------------------------------------------------
bw = 0.5 * (np.linalg.eigvalsh(Dop(X)).max() + np.linalg.eigvalsh(Dop(HAD)).max())
R.check("the branchwise worst case is (E/2)(1 + 1/sqrt2) > v_t for 0 < t < pi/8",
        abs(bw - E / 2 * (1 + 2 ** -0.5)) < 1e-12 and all(vt(t) < bw for t in np.linspace(1e-4, math.pi / 8 - 1e-4, 500)))

# 6-7. the kept state and the heat effect --------------------------------------------------------------------------
t = 0.3
real, Us, Vs = hidden(t)
Ge = energy_matrix(real, [H, H])
v = vt(t)                    # closed form (exact)
c = 2
Lam = herm(v / c * np.eye(8) - Ge)
Wv = cp.Variable((4, 4), hermitian=True)
lam = cp.Variable()
Dv = Lam + cp.kron(Wv, np.eye(2))
prob = cp.Problem(cp.Minimize(lam), [Dv >> 0, lam * np.eye(8) - Dv >> 0, cp.partial_trace(Wv, [2, 2], axis=1) == 0])
try:
    prob.solve(solver="CLARABEL")
except cp.error.SolverError:
    prob.solve(solver="SCS", eps=1e-10, max_iters=200000)
Dm = herm(Lam + np.kron(Wv.value, np.eye(2)))
wE, wd = 0.0, 0.0
delta = 1e-3
for _ in range(40):
    te = random_tester([2, 2], rng, int(rng.integers(1, 4)))
    s = simulate(real, te, [H, H])
    kept = te.record_by_epr() / c                                   # the rare-branch kept state
    heat = float(np.trace((c / delta) * Dm @ kept).real)            # effect (c/delta) D on the kept state
    wE = max(wE, abs(s["energy"] + delta * heat - v))               # rare branch has probability delta
    wd = max(wd, abs(s["energy"] + float(np.trace(Dm @ te.record()).real) - v))
effect_norm = c * np.linalg.eigvalsh(Dm).max()                    # times 1/delta
R.check("a positive heat effect D with Tr D Z = v_t - E_main(Z) exists; main energy plus rare heat is v_t on 40 testers",
        np.linalg.eigvalsh(Dm).min() > -1e-7 and wd < 1e-6 and wE < 1e-6, f"{wd:.1e}, {wE:.1e}")
R.check("the heat effect on the kept state has norm c||D||/delta <= 8E/delta (Tr D = 4 v_t gives 8 v_t/delta <= 6.83E/delta)",
        effect_norm <= 8 * E + 1e-9 and abs(np.trace(Dm).real - 4 * v) < 1e-6,
        f"minimal norm {effect_norm:.4f} E/delta, trace bound {8 * v:.4f} E/delta")
w2 = 0.0
for _ in range(20):
    te = random_tester([2, 2], rng, 2)
    Zr = te.record()
    for b in (0, 1):
        u = np.array([Us[b][j, i] for i in range(2) for j in range(2)])
        r2 = np.einsum("ab,aibk->ik", np.outer(u, u.conj()), (c * te.record_by_epr() / c).reshape(4, 2, 4, 2))
        # direct: run branch b of the process against the tester
        st = te.psi.copy()
        st = np.einsum("oi,it->ot", Us[b], st)
        L = te.Ls[0].reshape(2, te.tdims[1], 2, te.tdims[0])
        st = np.einsum("iuot,ot->iu", L, st)
        w2 = max(w2, np.abs(r2 - st @ st.conj().T).max())
R.check("the kept state (first input kept, EPR half emitted) is the tester record: second inputs recovered on both branches",
        w2 < 1e-12, f"{w2:.1e}")

# 8. constants ------------------------------------------------------------------------------------------------------
ok8 = True
for N in (10, 100, 1000):
    dl = N ** -3.0
    b = 8 * E / dl
    M = E * N ** 8
    hspan = 2 * E + 2 * E                      # span of the touched energies, a fixed multiple of E
    z = 1 / (1 + math.exp(min(700, M)))
    rM = 3 * hspan * b / M + 2 * z * b
    ok8 &= N * rM <= 100 * E * N ** -3 and math.isclose(N * dl, N ** -2.0)
R.check("delta = N^-3, effect 8E N^3, hot gap E N^8: heat remainder N r_M = O(E N^-3) within O(E/N^2), error N delta = N^-2",
        ok8)

# 9. the lift used in Appendix F, Step 2 -----------------------------------------------------------------------------
# For qubits F(rho, rho')^2 = (1 + R.R')/2 with R = (r, sqrt(1 - |r|^2)); the energy is (E/2)(R0.u + R1.w/sqrt2), and
# no pair with angle(R0, R1) <= 2t exceeds v_t, which two pure states attain.
PAULI = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]]), np.array([[1, 0], [0, -1]], complex)]
lift = lambda r: np.append(r, math.sqrt(max(0.0, 1 - r @ r)))
state = lambda r: (I2 + sum(c * P for c, P in zip(r, PAULI))) / 2
ball = lambda: [v * rng.uniform() ** (1 / 3) / np.linalg.norm(v) for v in rng.normal(size=(2, 3))]
wlift = 0.0
for _ in range(300):
    r0, r1 = ball()
    F = np.linalg.svd(sqrtm_psd(state(r0)) @ sqrtm_psd(state(r1)), compute_uv=False).sum()
    wlift = max(wlift, abs(F ** 2 - (1 + lift(r0) @ lift(r1)) / 2))
u4, w4 = np.array([0, 0, 1, 0.0]), np.array([-1, 0, 1, 0.0]) / math.sqrt(2)
worst, wen = -1.0, 0.0
for t in (0.05, 0.2, 0.35):
    for _ in range(20000):
        r0, r1 = ball()
        R0, R1 = lift(r0), lift(r1)
        if R0 @ R1 >= math.cos(2 * t):
            en = np.real(np.trace(state(r0) @ (E * PAULI[2])) + np.trace(state(r1) @ (E / 2 * (PAULI[2] - PAULI[0])))) / 2
            wen = max(wen, abs(en - E / 2 * (R0 @ u4 + R1 @ w4 / math.sqrt(2))))
            worst = max(worst, en - vt(t))
R.check("Appendix F lift: qubit F^2 = (1 + R.R')/2 (300 random pairs), energy (E/2)(R0.u + R1.w/sqrt2), and no mixed pair "
        "within angle 2t beats v_t (60000 samples)", wlift < 1e-10 and wen < 1e-12 and worst < 1e-12,
        f"{wlift:.1e}, {wen:.1e}, {worst:.3f}")
R.close()
