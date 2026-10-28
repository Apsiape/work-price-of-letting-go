"""Without time covariance (Section 6 and Appendix E), part 1: the recorder, the joint tangent, the positive heat
effect and the heat contact, on a random non-covariant two-slot qubit collision.  Natural logarithms and energy units, as
in Appendix E; beta = 1.

Checks:
  1. (E1): every energy-valued score S(Z|F)/beta + E_pay is at most C_0 = 2 ln d/beta + R_H in absolute value, for the
     original and the enlarged collision;
  2. (E4): the rare-branch contacts are full square unitaries, and the enlarged collision is within strategy distance
     delta of the original (SDP);
  3. (E5): on the rare branch, immediately after the last input arrives, the retained state of (A_1, R_1, I_2) is Z_2/c;
  4. (E6): S(omega'_t) - S(tau') = (1 - delta)[S(omega_t) - S(tau)] + delta S(chi_t) for every tester, and g' <= g + delta C_0;
  5. (E7): E'_pay(t) - (Tr omega'_t ln zeta + S(tau'))/beta <= g' for every tester (SDP);
  6. (E8): with q = (1-s) zeta + s I/R, T = -ln q/beta (partition function one), F = D(tau'||q)/beta and w = max_t J(t),
     F + w <= g' + a_s;
  7. (E9): a positive D_hist with Tr D_hist Z = w n(Z) - J(Z) on the tester space exists (SDP), and
     ||D_hist|| <= Tr D_hist = d[w - J(Z_0)] <= d(2 C_0 + a_s);
  8. (E10): the accessible effect D = |1><1|_f (x) I_B (x) (c/delta) D_hist has expectation w - J(t) on every tester, and
     b = ||D|| <= c d (2 C_0 + a_s)/delta;
  9. (E11): the Julia heat contact J_D is unitary on every column; tracing G gives X -> C_D X C_D + F_D X F_D for either
     initial eigenstate; the initialized heat effect is (1 - 2z) D; ||R_M|| <= 3 h b/M + 2 z b; and by full simulation of
     the episode with the contact, the total initialized energy gain is w + <R_M> with |<R_M>| <= r_M for every tester,
     while the ordinary branch (f = 0) is untouched.
"""
import math

from qtools import (P0, P1, Report, dm, embed, entropy_nat, herm, ket, logm_psd, random_density, random_unitary,
                    relent, sqrtm_psd)  # noqa: I001
import cvxpy as cp
import numpy as np

from combs import (Realization, TesterLP, bath_functional, energy_matrix, flat_record, link, maximize_score, omega_map,
                   random_tester, simulate, strategy_distance)

R = Report("Without time covariance: recorder, tangent, heat effect, heat contact")
rng = np.random.default_rng(34)
LN2 = math.log(2)
beta = 1.0
E = 1.0
H = [np.diag([0.0, E]).astype(complex)] * 2
dims = [2, 2]
d, c = 4, 2
R_H = 2 * E
C0 = 2 * math.log(d) / beta + R_H
delta, s = 0.05, 0.02
lp = TesterLP(dims)

dB = 2
tau = random_density(dB, rng)
U1, U2 = random_unitary(2 * dB, rng), random_unitary(2 * dB, rng)
orig = Realization.collision(dims, tau, [U1, U2])

# enlarged source and contacts; bath order (B, f, A_1, R_1); contacts on (port, B, f, A_1, R_1)
phi = np.eye(2).reshape(-1) / math.sqrt(2)
OmK = dm(phi)
piK = np.eye(4) / 4
taup = np.kron(tau, (1 - delta) * np.kron(dm(ket((0,))), piK) + delta * np.kron(dm(ket((1,))), OmK)).astype(complex)
dims5 = [2, dB, 2, 2, 2]
SW = np.eye(4)[[0, 2, 1, 3]].astype(complex)
U1p = embed(U1, [0, 1], dims5) @ embed(P0, [2], dims5) + embed(SW, [0, 3], dims5) @ embed(P1, [2], dims5)
U2p = embed(U2, [0, 1], dims5) @ embed(P0, [2], dims5) + embed(P1, [2], dims5)
enl = Realization.collision(dims, taup, [U1p, U2p])
DBp = 16


def energy_score(real, te):
    s_ = simulate(real, te, H)
    return s_["SZF"] * LN2 / beta + s_["energy"], s_


# 1. (E1) -----------------------------------------------------------------------------------------------------------
w1 = 0.0
for real in (orig, enl):
    for _ in range(25):
        val, _ = energy_score(real, random_tester(dims, rng, int(rng.integers(1, 4))))
        w1 = max(w1, abs(val) / C0)
R.check("(E1): |S(Z|F)/beta + E_pay| <= C_0 = 2 ln d/beta + R_H for the original and the enlarged collision", w1 <= 1,
        f"largest ratio {w1:.3f}")

# 2. (E4) -----------------------------------------------------------------------------------------------------------
uni = max(np.abs(U.conj().T @ U - np.eye(U.shape[0])).max() for U in (U1p, U2p))
dist = strategy_distance(enl.R, orig.R, dims)
R.check("(E4): the rare-branch contacts are full square unitaries and the enlarged process is within delta of the original",
        uni < 1e-12 and dist <= delta + 1e-7, f"distance {dist:.6f} <= delta = {delta}")

# 3. (E5) and 4. (E6) -------------------------------------------------------------------------------------------------
def rare_record(te):
    """State of (A_1, R_1, I_2) on the branch f = 1, just after the second input arrives, divided by delta."""
    st = np.einsum("it,mf->itmf", te.psi, sqrtm_psd(taup))              # (I_1, T_1, B', F)
    U = U1p.reshape(2, DBp, 2, DBp)
    st = np.einsum("omia,itaf->otmf", U, st)
    L = te.Ls[0].reshape(2, te.tdims[1], 2, te.tdims[0])
    st = np.einsum("iuot,otmf->iumf", L, st)                              # (I_2, T_2, B', F)
    st = st.reshape(2, te.tdims[1], dB, 2, 2, 2, DBp)                     # (I_2, T, B, f, A_1, R_1, F)
    br = st[:, :, :, 1, :, :, :]                                          # f = 1
    m = br.transpose(3, 4, 0, 1, 2, 5).reshape(8, -1)                     # (A_1, R_1, I_2) x rest
    return m @ m.conj().T / delta


w3 = w4 = 0.0
for _ in range(20):
    te = random_tester(dims, rng, int(rng.integers(1, 4)))
    Zr = te.record()
    w3 = max(w3, np.abs(rare_record(te) - Zr / c).max())
    so, se = simulate(orig, te, H), simulate(enl, te, H)
    chi = herm(Zr.reshape(4, 2, 4, 2).trace(axis1=1, axis2=3)) / c
    lhs = entropy_nat(se["omega"]) - entropy_nat(taup)
    rhs = (1 - delta) * (entropy_nat(so["omega"]) - entropy_nat(tau)) + delta * entropy_nat(chi)
    w4 = max(w4, abs(lhs - rhs))
R.check("(E5): on the rare branch the retained (A_1, R_1, I_2) state is Z_2/c (20 adaptive testers)", w3 < 1e-12,
        f"{w3:.1e}")
_, g_lo_bits, g_up_bits = maximize_score(orig, H, beta, lp, iters=60)
Zs_e, gp_lo_bits, gp_up_bits = maximize_score(enl, H, beta, lp, iters=80)
g_lo, g_up = g_lo_bits * LN2 / beta, g_up_bits * LN2 / beta
gp_lo, gp_up = gp_lo_bits * LN2 / beta, gp_up_bits * LN2 / beta
R.check("(E6): S(omega'_t) - S(tau') = (1 - delta)[S(omega_t) - S(tau)] + delta S(chi_t), and g' <= g + delta C_0",
        w4 < 1e-12 and gp_up <= g_lo + delta * C0 + 1e-7, f"{w4:.1e}; g in [{g_lo:.6f}, {g_up:.6f}], "
        f"g' in [{gp_lo:.6f}, {gp_up:.6f}], g + delta C_0 = {g_lo + delta * C0:.6f}")

# 5. (E7) -------------------------------------------------------------------------------------------------------------
om, Mt = omega_map(enl)
Ge = energy_matrix(enl, H)
zeta = herm(om(Zs_e))
Lz = -logm_psd(zeta, math.e, floor=1e-300)
G7 = Ge + bath_functional(Mt, Lz) / beta
_, m7 = lp.solve(G7)
lhs7 = m7 - entropy_nat(taup) / beta
R.check("(E7): E'_pay(t) - (Tr omega'_t ln zeta + S(tau'))/beta <= g' for every tester (SDP)", lhs7 <= gp_up + 1e-6,
        f"{lhs7:.7f} <= {gp_up:.7f}")

# 6. (E8) -------------------------------------------------------------------------------------------------------------
q = (1 - s) * zeta + s * np.eye(DBp) / DBp
T = -logm_psd(q, math.e) / beta
Fsrc = relent(taup, q, math.e) / beta
GJ = Ge + bath_functional(Mt, T) - np.trace(T @ taup).real * np.eye(8) / c       # J as a linear functional of Z
Zw, w = lp.solve(GJ)
a_s = -math.log(1 - s) / beta
R.check("(E8): q is faithful with Tr e^{-beta T} = 1, and F + w <= g' + a_s",
        abs(np.trace(q).real - 1) < 1e-12 and np.linalg.eigvalsh(q).min() > 0 and Fsrc + w <= gp_up + a_s + 1e-6,
        f"F + w = {Fsrc + w:.6f}, g' + a_s = {gp_up + a_s:.6f}")

# 7. (E9) -------------------------------------------------------------------------------------------------------------
Lam = herm(w / c * np.eye(8) - GJ)                   # L(Z) = w n(Z) - J(Z) = Tr(Lam Z) on the tester space
Wv = cp.Variable((4, 4), hermitian=True)
Dv = Lam + cp.kron(Wv, np.eye(2))
prob = cp.Problem(cp.Minimize(cp.real(cp.trace(Dv))), [Dv >> 0, cp.partial_trace(Wv, [2, 2], axis=1) == 0])
prob.solve(solver="CLARABEL")
Dh = herm(Lam + np.kron(Wv.value, np.eye(2)))
mineig = np.linalg.eigvalsh(Dh).min()
Dh = Dh - min(mineig, 0) * np.eye(8)                 # remove solver round-off (reported below)
JZ0 = float(np.trace(GJ @ flat_record(dims)).real)
trD = np.trace(Dh).real
lk0 = link(enl, flat_record(dims), H)
score0 = (entropy_nat(lk0["omega"]) - entropy_nat(taup)) / beta + lk0["energy"]
side = JZ0 + Fsrc >= score0 - 1e-9 and score0 >= -C0 and gp_up <= C0
wL = 0.0
for _ in range(20):
    Zr = random_tester(dims, rng, 2).record()
    wL = max(wL, abs(np.trace(Dh @ Zr).real - (w - np.trace(GJ @ Zr).real)))
R.check("(E9): a positive D_hist with Tr D_hist Z = w n(Z) - J(Z) exists; ||D_hist|| <= Tr D_hist = d[w - J(Z_0)] <= d(2C_0 + a_s)",
        mineig > -1e-7 and wL < 1e-6 and abs(trD - d * (w - JZ0)) < 1e-6 and np.linalg.eigvalsh(Dh).max() <= trD + 1e-12
        and trD <= d * (2 * C0 + a_s) and side,
        f"min eigenvalue {mineig:.1e}, Tr = {trD:.4f}, bound {d * (2 * C0 + a_s):.4f}; J(Z_0) + F >= score(Z_0) >= -C_0, g' <= C_0")

# 8. (E10) ------------------------------------------------------------------------------------------------------------
# D on (I_2, B, f, A_1, R_1): |1><1|_f (x) I_B (x) (c/delta) D_hist(A_1, R_1, I_2)
Dt = Dh.reshape(2, 2, 2, 2, 2, 2)                               # (a, r, i ; a', r', i')
Dfull = np.einsum("arixyz,fg,bc->ibfarzcgxy", Dt, P1, np.eye(dB)).reshape(32, 32) * c / delta
b = np.linalg.eigvalsh(herm(Dfull)).max()
w10 = 0.0
for _ in range(20):
    te = random_tester(dims, rng, int(rng.integers(1, 4)))
    st = np.einsum("it,mf->itmf", te.psi, sqrtm_psd(taup))
    st = np.einsum("omia,itaf->otmf", U1p.reshape(2, DBp, 2, DBp), st)
    st = np.einsum("iuot,otmf->iumf", te.Ls[0].reshape(2, te.tdims[1], 2, te.tdims[0]), st)  # (I_2, T, B', F)
    m = st.transpose(0, 2, 1, 3).reshape(32, -1)
    expD = float(np.trace(Dfull @ m @ m.conj().T).real)
    Jt = float(np.trace(GJ @ te.record()).real)
    w10 = max(w10, abs(expD - (w - Jt)))
R.check("(E10): <D> = w - J(t) on every tester (simulation), and b = ||D|| <= c d (2 C_0 + a_s)/delta",
        w10 < 1e-6 and b <= c * d * (2 * C0 + a_s) / delta, f"{w10:.1e}; b = {b:.2f} <= {c * d * (2 * C0 + a_s) / delta:.2f}")

# 9. (E11) ------------------------------------------------------------------------------------------------------------
specT = np.linalg.eigvalsh(herm(T))
hspan = E + (specT.max() - specT.min())
ok11 = True
details = []
for Mfac in (2, 20, 200):
    M = Mfac * b
    z = 1 / (1 + math.exp(min(700, beta * M)))
    Cd = sqrtm_psd(np.eye(32) - Dfull / M)
    Fd = sqrtm_psd(Dfull / M)
    JD = np.kron(Cd, np.diag([1, 0])) + np.kron(-Fd, np.array([[0, 1], [0, 0]])) \
        + np.kron(Fd, np.array([[0, 0], [1, 0]])) + np.kron(Cd, np.diag([0, 1]))          # order (system, G)
    ok11 &= np.abs(JD.conj().T @ JD - np.eye(64)).max() < 1e-10
    X = random_density(32, rng)
    for gstate in (0, 1):
        out = JD @ np.kron(X, dm(ket((gstate,)))) @ JD.conj().T
        red = out.reshape(32, 2, 32, 2).trace(axis1=1, axis2=3)
        ok11 &= np.abs(red - (Cd @ X @ Cd + Fd @ X @ Fd)).max() < 1e-10
    G0 = np.diag([1 - z, z])
    out = JD @ np.kron(X, G0) @ JD.conj().T
    heat = M * (out.reshape(32, 2, 32, 2).trace(axis1=0, axis2=2)[1, 1].real - z)
    ok11 &= abs(heat - (1 - 2 * z) * np.trace(Dfull @ X).real) < 1e-9 * max(1, M)
    Q = U2p.conj().T @ (np.kron(H[1], np.eye(DBp)) + np.kron(np.eye(2), T)) @ U2p
    RM = Cd @ Q @ Cd + Fd @ Q @ Fd - Q - 2 * z * Dfull
    rM = 3 * hspan * b / M + 2 * z * b
    ok11 &= np.linalg.norm(RM, 2) <= rM + 1e-12
    worst = 0.0
    for trial in range(15):
        te = random_tester(dims, rng, int(rng.integers(1, 4)))
        sq = sqrtm_psd(taup)
        sqG = np.diag(np.sqrt([1 - z, z]))
        st = np.einsum("it,mf,gh->itmfgh", te.psi, sq, sqG)                                  # (I_1, T, B', F, G, FG)
        rI1 = np.einsum("it,jt->ij", te.psi, te.psi.conj())
        st = np.einsum("omia,itafgh->otmfgh", U1p.reshape(2, DBp, 2, DBp), st)
        mm = st.reshape(2, -1)
        rO1 = mm @ mm.conj().T
        st = np.einsum("iuot,otmfgh->iumfgh", te.Ls[0].reshape(2, te.tdims[1], 2, te.tdims[0]), st)
        mm = st.reshape(2, -1)
        rI2 = mm @ mm.conj().T
        sh = st.shape
        st = st.transpose(0, 2, 4, 1, 3, 5)                                                  # (I_2, B', G, T, F, FG)
        st = (JD @ st.reshape(64, -1)).reshape(2, DBp, 2, sh[1], sh[3], sh[5])
        st = st.transpose(0, 3, 1, 4, 2, 5)                                                  # (I_2, T, B', F, G, FG)
        st = np.einsum("omia,itafgh->otmfgh", U2p.reshape(2, DBp, 2, DBp), st)
        full = st.reshape(-1)
        dl = [2, sh[1], DBp, DBp, 2, 2]
        rho_all = np.outer(full, full.conj())
        from qtools import ptrace
        rO2 = ptrace(rho_all, dl, [0])
        omp = ptrace(rho_all, dl, [2])
        rG = ptrace(rho_all, dl, [4])
        payload = float(np.trace(H[0] @ (rO1 - rI1) + H[1] @ (rO2 - rI2)).real)
        bath = float(np.trace(T @ (omp - taup)).real)
        hq = M * (rG[1, 1].real - z)
        worst = max(worst, abs(payload + bath + hq - w))
    ok11 &= worst <= rM
    details.append(f"M = {Mfac} b: |gain - w| <= {worst:.2e} vs r_M = {rM:.2e}")
# on f = 0 the contact is the identity
f0 = np.kron(np.kron(np.eye(2), np.eye(dB)), np.kron(P0, np.eye(4)))
R.check("(E11): J_D is unitary; tracing G gives C X C + F X F; heat effect (1 - 2z) D; ||R_M|| <= 3hb/M + 2zb; full "
        "episodes gain w + <R_M> with |<R_M>| <= r_M; on f = 0, D = 0", ok11 and np.abs(Dfull @ f0).max() < 1e-12,
        "; ".join(details))
R.close()
