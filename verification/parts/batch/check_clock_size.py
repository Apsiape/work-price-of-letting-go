"""How large the clock must be (Propositions "Unbalanced channels need a broad clock" and "How large the clock must be",
Table "clocksize", Appendices "Unbalanced channels need a broad clock" and "How large the clock must be").

Checks:
  1. the rotation bound (1/2)||alpha_t - alpha_C||_1 <= sqrt(2|t| s_n/beta) and |e^{ix} - 1|^2 <= 2|x|;
  2. the generator: sum_i A_i^* (d/dt)A_i = -iD along the time orbit;
  3. the code from the fibre: X in ker Psi with Tr XD != 0, Knill-Laflamme conditions for the flagged interpolations,
     and the recovered logical channel has derivative -i[D_L, .] (finite differences); the GHZ phases t_k give orthogonal
     ideal outputs;
  4. the probe steps: Bernoulli fidelity and m-fold products, the choice of m in the reuse step, and the X-dephasing
     constants N = 64, b = p/8192, c = 9p^3 E/(4096 sqrt2), p = 1 - e^{-1/(128 pi^2)} against the proof's chain;
  5. (a): Tr PB = ||B||_1/2, |p''| <= 4h^2 ||M||, the slope and the exact binomial error of the nearest-mean rule;
  6. (b): the constant chain to 9 beta lambda/(1024 sqrt2);
  7. (c): V^*R = 0, R_n^*R_n = sum_i (R^*R)_i, ||V_t - V^(x)n|| <= |t| sqrt(n) kappa, kappa > 0 for non-covariant
     channels, the exact ladder lift (isometry, energy conservation, mean energy of the clock unchanged, vector error
     <= pi^2 kappa sqrt(n)/(2 omega (l+1))), the slab profile, the equidistribution of the Gram coefficients, the seeds;
  8. (d): the logical channel of X-dephasing, (1/2)||Delta_r - id||_diamond = (1-r)/2, 1 - cos^n x <= n x^2/2, the
     lower-bound chain, Stinespring continuity, W_p^* W_q = f I and the eigenphase step on a programmable phase gate,
     the construction's gain, disturbance and constants;
  9. the replacement channel's stock spread beta E sqrt(n/(2 pi)) and the consistency of Table "clocksize".
"""
from fractions import Fraction
import math

import mpmath as mp
import numpy as np
from scipy.linalg import expm
from scipy.stats import binom

from qtools import (Channel, Report, X, Z, choi_of, dag, diamond_half, dm, fidelity, herm, opnorm, powm_h,
                    random_density, random_unitary, trace_norm)

R = Report("How large the clock must be")
rng = np.random.default_rng(20261017)


def spread_of(alpha, eC, beta):
    """s_n of a controller alpha with energies eC (Gibbs state at beta), by the definition."""
    x, a = np.linalg.eigh(herm(alpha))
    g = np.exp(-beta * eC)
    g /= g.sum()
    vals, wts = [], []
    for i in range(len(x)):
        if x[i] <= 1e-14:
            continue
        for j in range(len(eC)):
            w = x[i] * abs(a[j, i]) ** 2
            if w > 1e-16:
                vals.append(math.log(x[i] / g[j]))
                wts.append(w)
    vals, wts = np.array(vals), np.array(wts)
    o = np.argsort(vals)
    c = vals[o][np.searchsorted(np.cumsum(wts[o]), 0.5 * wts.sum())]
    return float(np.sum(wts * np.abs(vals - c)))


# 1. rotation bound
ok1, worst1 = True, 0.0
for trial in range(400):
    d = int(rng.integers(2, 6))
    eC = rng.uniform(0, 4, d)
    beta = rng.uniform(0.2, 3)
    alpha = random_density(d, rng, rank=int(rng.integers(1, d + 1)))
    s = spread_of(alpha, eC, beta)
    for t in 10 ** rng.uniform(-3, 1, 4):
        Ut = np.diag(np.exp(-1j * eC * t))
        lhs = trace_norm(Ut @ alpha @ dag(Ut) - alpha) / 2
        rhs = math.sqrt(2 * t * s / beta)
        ok1 &= lhs <= rhs + 1e-12
        if rhs < 1:
            worst1 = max(worst1, lhs / rhs)
xs = np.linspace(-50, 50, 200001)
ok1 &= bool(np.all(np.abs(np.exp(1j * xs) - 1) ** 2 <= 2 * np.abs(xs) + 1e-12))
R.check("(1/2)||alpha_t - alpha_C||_1 <= sqrt(2|t| s_n/beta) (400 controllers, mixed and pure), and "
        "|e^{ix} - 1|^2 <= 2|x| (also proved in Lean)", ok1, f"largest ratio where the bound is below 1: {worst1:.3f}")

# 2. generator


def random_channel(d, r, rng):
    g = rng.standard_normal((d * r, d)) + 1j * rng.standard_normal((d * r, d))
    q, _ = np.linalg.qr(g)
    return [q.reshape(d, r, d)[:, k, :] for k in range(r)]


ok2 = True
for trial in range(100):
    d, r = int(rng.integers(2, 4)), int(rng.integers(1, 4))
    H = herm(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)))
    ch = Channel(random_channel(d, r, rng), H)
    gen = sum(dag(A) @ (-1j * (H @ A - A @ H)) for A in ch.K)
    ok2 &= opnorm(gen + 1j * ch.D) < 1e-12
R.check("along the time orbit A_i(t) = e^{-iHt} A_i e^{iHt}: sum_i A_i^* (dA_i/dt) = -iD, so i sum A_i^* dA_i/dt = D", ok2)

# ---------------------------------------------------------------------------------------------------------------------
# 3. the code from the fibre


def code_check(ch, Mc, rng):
    """Flagged interpolation code from a fibre pair; returns (KL error, derivative error, sign)."""
    d, r = ch.d, ch.r
    ker = ch.psi_kernel_hermitian()
    Xk = max(ker, key=lambda x: abs(np.trace(x @ ch.D)))
    w, v = np.linalg.eigh(Xk)
    rp = (v[:, w > 0] * w[w > 0]) @ dag(v[:, w > 0])
    rm = -(v[:, w < 0] * w[w < 0]) @ dag(v[:, w < 0])
    rp, rm = rp / np.trace(rp).real, rm / np.trace(rm).real
    if np.real(np.trace(ch.D @ (rp - rm))) < 0:
        rp, rm = rm, rp
    ok = opnorm(ch.psi(rp) - ch.psi(rm)) < 1e-10 and abs(np.trace(Xk)) < 1e-10
    rhos = [rm + (j / (Mc - 1)) * (rp - rm) for j in range(Mc)]
    # |c_j> = (sqrt(rho_j) x I)|Omega> (x) |j>, on S x R x F
    Om = np.eye(d).reshape(-1)
    cs = []
    for j, rj in enumerate(rhos):
        f = np.zeros(Mc)
        f[j] = 1
        cs.append(np.kron(np.kron(powm_h(rj, 0.5), np.eye(d)) @ Om, f))
    cs = np.array(cs).T                                       # (d d Mc) x Mc
    E = [np.kron(A, np.eye(d * Mc)) for A in ch.K]
    kl = 0.0
    C0 = dag(cs) @ dag(E[0]) @ E[0] @ cs
    Cmat = np.zeros((r, r), dtype=complex)
    for i in range(r):
        for k in range(r):
            blk = dag(cs) @ dag(E[i]) @ E[k] @ cs
            Cmat[i, k] = blk[0, 0]
            kl = max(kl, opnorm(blk - blk[0, 0] * np.eye(Mc)))
    lam, Uc = np.linalg.eigh(herm(Cmat))
    Rk = []
    for m in range(r):
        if lam[m] > 1e-12:
            Fm = sum(Uc[i, m] * E[i] for i in range(r))
            Rk.append(dag(cs) @ dag(Fm) / math.sqrt(lam[m]))          # |j> <c_j| F_m^*
    DL = np.diag([np.real(np.trace(rj @ ch.D)) for rj in rhos])

    def logical(t, XL):
        Ut = np.kron(expm(-1j * ch.H * t), np.eye(d * Mc))
        Y = cs @ XL @ dag(cs)
        out = sum(Ut @ e @ dag(Ut) @ Y @ dag(Ut @ e @ dag(Ut)) for e in E)
        return sum(Rm @ out @ dag(Rm) for Rm in Rk)

    hstep = 1e-5
    der_err_minus, der_err_plus = 0.0, 0.0
    for a_ in range(Mc):
        for b_ in range(Mc):
            XL = np.zeros((Mc, Mc), dtype=complex)
            XL[a_, b_] = 1
            der = (logical(hstep, XL) - logical(-hstep, XL)) / (2 * hstep)
            der_err_minus = max(der_err_minus, opnorm(der - (-1j) * (DL @ XL - XL @ DL)))
            der_err_plus = max(der_err_plus, opnorm(der - (1j) * (DL @ XL - XL @ DL)))
    ok &= opnorm(logical(0.0, np.eye(Mc)) - np.eye(Mc)) < 1e-10
    return ok, kl, der_err_minus, der_err_plus, np.diag(DL)


ok3, rows3 = True, []
Hq = np.diag([0.0, 1.3]).astype(complex)
tests = [("X-dephasing", Channel([np.eye(2) / math.sqrt(2), X / math.sqrt(2)], Hq))]
H3 = np.diag([0.0, 0.7, 1.6]).astype(complex)
for i in range(3):
    tests.append((f"random qutrit {i}", Channel(random_channel(3, 2, rng), H3)))
for name, ch in tests:
    for Mc in (2, 3, 4):
        ok, kl, dm_, dp_, dl = code_check(ch, Mc, rng)
        ok3 &= ok and kl < 1e-10 and dm_ < 1e-6
        a_gap = dl[-1] - dl[0]
        ok3 &= a_gap > 0 and np.allclose(np.diff(dl), a_gap / (Mc - 1))
    rows3.append(f"{name}: a = {a_gap:.4f}, derivative error {dm_:.1e}")
R.check("code from the fibre: rho_+- leave the same environment state, the flagged interpolations satisfy the "
        "Knill-Laflamme conditions, the recovered logical channel is the identity at t = 0 with derivative "
        "-i[D_L, .], D_L = diag(Tr rho_j D) evenly spaced with gap a > 0 (M = 2, 3, 4)", ok3, "; ".join(rows3[:2]))
ok3b = True
for Mc in (2, 3, 5, 8):
    for n in (1, 3, 10):
        a = rng.uniform(0.2, 3)
        dlv = rng.uniform(-1, 1) + a * np.arange(Mc) / (Mc - 1)
        states = []
        for k in range(Mc):
            tk = 2 * math.pi * (Mc - 1) * k / (Mc * n * a)
            KM = 2 * math.pi * (Mc - 1) ** 2 / (Mc * a)
            ok3b &= tk <= KM / n + 1e-12
            states.append(np.exp(-1j * tk * n * dlv) / math.sqrt(Mc))      # GHZ: phase of |j>^n is e^{-i t n D_L(j)}
        G = np.abs(np.array(states).conj() @ np.array(states).T)
        ok3b &= np.allclose(G, np.eye(Mc), atol=1e-12)
R.check("reading the clock: at t_k = 2 pi (M-1) k/(M n a) <= K_M/n the ideal GHZ outputs are orthonormal", ok3b)

# ---------------------------------------------------------------------------------------------------------------------
# 4. probe steps
ok4, near4 = True, 0
for trial in range(3000):
    p1 = rng.uniform(0.01, 0.99)
    dp = rng.uniform(-0.3, 0.3)
    p2 = min(0.999, max(0.001, p1 + dp))
    bc = math.sqrt(p1 * p2) + math.sqrt((1 - p1) * (1 - p2))
    ok4 &= bc <= 1 - (p1 - p2) ** 2 / 2 + 1e-15
    m = int(rng.integers(1, 60))
    ks = np.arange(m + 1)
    tv = 0.5 * np.sum(np.abs(binom.pmf(ks, m, p1) - binom.pmf(ks, m, p2)))
    ok4 &= tv >= 1 - bc ** m - 1e-12
    near4 += tv < 1.5 * (1 - bc ** m)
R.check("two-outcome laws: BC <= 1 - (p1 - p2)^2/2, and their m-fold products are at total variation >= 1 - BC^m, so "
        "a separation c/sqrt(m) gives distance >= 1 - e^{-c^2/2}", ok4, f"{near4} cases within a factor 1.5")
ok4b = True
for trial in range(2000):
    eta = 10 ** rng.uniform(-12, -1)
    sn = 10 ** rng.uniform(0, 8)
    n = 10 ** rng.uniform(1, 6)
    An = max(1.0, (sn / n) ** 2)
    Rn = eta * An
    if Rn > 1e-2:
        continue
    m = math.ceil(An / math.sqrt(Rn))
    ok4b &= m * eta <= math.sqrt(Rn) * (1 + 1 / max(m - 1, 1)) + 1e-15
    ok4b &= sn / (n * math.sqrt(m)) <= Rn ** 0.25 + 1e-12
R.check("reuse step: m = ceil(A_n/sqrt(R_n)), A_n = max{1, (s_n/n)^2}, R_n = eta_n A_n gives m eta_n <= ~sqrt(R_n) and "
        "s_n/(n sqrt m) <= R_n^{1/4}", ok4b)
# X-dephasing constants against the chain p <= 2kg eta + sqrt(s/(beta h k n sqrt g)) with a = h = E
pX = 1 - math.exp(-1 / (128 * math.pi ** 2))
bX = pX / 8192
cX = 9 * pX ** 3 / (4096 * math.sqrt(2))                 # in units of E (beta = E = 1)
ok4c, worst4c = True, np.inf
for zeta in np.geomspace(bX * 1e-6, bX, 25):
    for share in (0.0, 0.3, 0.7, 0.999):
        eps, eta = zeta * share, zeta * (1 - share)
        if eta <= 0:
            continue
        for n in (64, 65, 1000, 10 ** 6):
            best = 0.0
            for k in sorted({max(1, int(x)) for x in np.geomspace(1, 1 / (64 * max(eps, 1e-300)) + 1, 60)} |
                            {max(1, math.floor(pX / (1024 * zeta) * f)) for f in (0.5, 1, 2, 4, 8)}):
                if k * eps > 1 / 64:
                    continue
                r_ = math.cos(math.pi / (k * n)) ** (k * n)
                if (1 + r_) / 2 - 2 * k * eps < 0.5:
                    continue
                gmax_ = pX / (2 * k * eta)
                for g in sorted({256} | {max(256, int(gmax_ * f)) for f in (0.1, 0.2, 1 / 3, 0.5)}):
                    if pX - 2 * k * g * eta > 0:
                        best = max(best, k * math.sqrt(g) * (pX - 2 * k * g * eta) ** 2)
            ratio = best * math.sqrt(eta * (eps + eta)) / cX
            worst4c = min(worst4c, ratio)
            ok4c &= ratio >= 1
R.check("X-dephasing: for n >= 64 and 0 < eps + eta <= p/8192 some k, g satisfy the proof's conditions (k eps <= 1/64, "
        "distance >= 1/2, sqrt g >= 16) with beta E k n sqrt(g)(p - 2kg eta)^2 >= c beta n/sqrt(eta(eps+eta)), "
        "c = 9 p^3 E/(4096 sqrt2)", ok4c, f"least ratio {worst4c:.2f}")

# ---------------------------------------------------------------------------------------------------------------------
# 5. (a)
ok5 = True
for trial in range(500):
    d = int(rng.integers(2, 6))
    Bm = herm(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)))
    Bm -= np.trace(Bm) / d * np.eye(d)
    w, v = np.linalg.eigh(Bm)
    P = v[:, w > 0] @ dag(v[:, w > 0])
    ok5 &= abs(np.real(np.trace(P @ Bm)) - trace_norm(Bm) / 2) < 1e-10
    Mm = (np.eye(d) + P) / 3
    ok5 &= np.min(np.linalg.eigvalsh(Mm)) >= 1 / 3 - 1e-12 and np.max(np.linalg.eigvalsh(Mm)) <= 2 / 3 + 1e-12
worst5 = 0.0
for trial in range(300):
    d, r = 2, int(rng.integers(1, 4))
    H = herm(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)))
    h = np.ptp(np.linalg.eigvalsh(H))
    ch = Channel(random_channel(d, r, rng), H)
    rho = random_density(d * d, rng)
    Mm = herm(rng.standard_normal((d * d, d * d)))
    Mm /= opnorm(Mm)
    t0 = rng.uniform(-2, 2)

    def pt(t):
        Ut = expm(-1j * H * t)
        U2 = np.kron(Ut, np.eye(d))
        x = U2.conj().T @ rho @ U2
        y = sum(np.kron(A, np.eye(d)) @ x @ dag(np.kron(A, np.eye(d))) for A in ch.K)
        return np.real(np.trace(Mm @ U2 @ y @ dag(U2)))

    hh = 1e-3
    p2 = (pt(t0 + hh) - 2 * pt(t0) + pt(t0 - hh)) / hh ** 2
    worst5 = max(worst5, abs(p2) / (4 * h * h))
R.check("Tr PB = ||B||_1/2 for traceless Hermitian B, M = (I+P)/3 has spectrum in [1/3, 2/3], and "
        "|d^2/dt^2 Tr M (Phi_t x id)(rho)| <= 4h^2 ||M|| (h = span H)", ok5 and worst5 <= 1 + 1e-4,
        f"largest ratio {worst5:.3f}")
worst5b = 0.0
for lam in (0.05, 0.2, 0.5):
    for v in (2.2 / lam, 3 / lam, 5 / lam, 10 / lam):
        for n in (400, 4000, 40000):
            J = 4
            gap = lam * v / (2 * math.sqrt(n))
            ps = [0.5 - 1.5 * gap + j * gap for j in range(J)]
            if min(ps) < 1 / 3 or max(ps) > 2 / 3:
                continue
            delta = 4 / (lam * v) ** 2
            for j, p in enumerate(ps):
                err = 0.0
                if j > 0:
                    err += binom.cdf(math.floor((p - gap / 2) * n), n, p)
                if j < J - 1:
                    err += binom.sf(math.ceil((p + gap / 2) * n) - 1, n, p)
                worst5b = max(worst5b, err / delta)
R.check("(a): p'(t) >= lambda - (8h^2/3) tau = 2 lambda/3 >= lambda/2 for |t| <= lambda/(8h^2), and the nearest-mean rule "
        "errs with probability <= 4/(lambda v)^2 (exact binomial laws)", worst5b <= 1 and 2 / 3 >= 1 / 2,
        f"largest ratio {worst5b:.3f}")

# 6. (b)
ok6, near6 = True, np.inf
for i in range(1, 4001):
    zeta = Fraction(1, 32) * Fraction(i, 4000)
    k = math.floor(1 / (16 * zeta))
    ok6 &= k >= 1 / (32 * zeta) and k * zeta <= Fraction(1, 16)
    near6 = min(near6, float(k * 32 * zeta))
ok6 &= Fraction(4, 64) == Fraction(1, 16) and 1 - 2 * Fraction(1, 16) == Fraction(7, 8)
ok6 &= Fraction(7, 8) - Fraction(1, 8) == Fraction(3, 4) and Fraction(3, 4) ** 2 / 2 == Fraction(9, 32)
ok6 &= abs(9 / (32 * 8 * math.sqrt(32)) - 9 / (1024 * math.sqrt(2))) < 1e-18
R.check("(b): zeta <= 1/32, k = floor(1/(16 zeta)) >= 1/(32 zeta) and k zeta <= 1/16; v = 8/lambda gives delta = 1/16, "
        "distance 7/8, 7/8 - 1/8 = 3/4, (3/4)^2/2 = 9/32, and 9/(32 x 8 x sqrt 32) = 9/(1024 sqrt2) (exact)", ok6,
        f"least k/(1/(32 zeta)) = {near6:.3f}")

# ---------------------------------------------------------------------------------------------------------------------
# 7. (c)


def solve_K(ch):
    """Hermitian K with Psi^*(K) = H - Phi^*(H), by least squares; returns (K, residual)."""
    from qtools import hermitian_basis
    hb = hermitian_basis(ch.r)
    target = herm(ch.H - ch.phistar(ch.H))
    cols = [np.concatenate([np.real(ch.psistar(B)).ravel(), np.imag(ch.psistar(B)).ravel()]) for B in hb]
    A = np.array(cols).T
    bvec = np.concatenate([np.real(target).ravel(), np.imag(target).ravel()])
    coef, *_ = np.linalg.lstsq(A, bvec, rcond=None)
    K = sum(c * B for c, B in zip(coef, hb))
    return herm(K), float(np.linalg.norm(A @ coef - bvec))


def with_seed(ch, K, e0):
    d, r = ch.d, ch.r
    emb = np.zeros((r + 1, r))
    emb[:r, :r] = np.eye(r)
    Vp = np.kron(np.eye(d), emb) @ ch.V
    HE = np.zeros((r + 1, r + 1), dtype=complex)
    HE[:r, :r] = K + e0 * np.eye(r)
    HE[r, r] = e0
    W = np.kron(ch.H, np.eye(r + 1)) + np.kron(np.eye(d), HE)
    return Vp, W, HE


def kron_all(ops):
    out = np.array([[1.0 + 0j]])
    for o in ops:
        out = np.kron(out, o)
    return out


ok7, rows7 = True, []
psi_p = np.array([1, 1]) / math.sqrt(2)
balanced = [("replacement by |+>", Channel([np.outer(psi_p, np.eye(2)[i]) for i in range(2)], Hq))]
for i in range(2):
    balanced.append((f"random qubit channel {i}", Channel(random_channel(2, 2, rng), Hq)))
covariant = Channel([np.array([[1, 0], [0, math.sqrt(0.6)]]), np.array([[0, math.sqrt(0.4)], [0, 0]])], Hq)
for name, ch in balanced + [("amplitude damping (covariant)", covariant)]:
    K, res = solve_K(ch)
    e0 = max(0.0, -np.min(np.linalg.eigvalsh(K))) + 0.5
    Vp, W, HE = with_seed(ch, K, e0)
    d, dim = ch.d, ch.d * (ch.r + 1)
    ok7 &= res < 1e-10 and np.min(np.linalg.eigvalsh(HE)) > 0
    ok7 &= opnorm(dag(Vp) @ W @ Vp - ch.H - e0 * np.eye(d)) < 1e-10
    Rm = W @ Vp - Vp @ (ch.H + e0 * np.eye(d))
    kappa = opnorm(Rm)
    ok7 &= opnorm(dag(Vp) @ Rm) < 1e-10
    ok7 &= (kappa < 1e-10) == ("covariant" in name)
    for n in (1, 2, 3):
        Vn = kron_all([Vp] * n)
        Wn = sum(kron_all([W if j == i else np.eye(dim) for j in range(n)]) for i in range(n))
        Hn = sum(kron_all([ch.H if j == i else np.eye(d) for j in range(n)]) for i in range(n)) + n * e0 * np.eye(d ** n)
        Rn = Wn @ Vn - Vn @ Hn
        RR = dag(Rm) @ Rm
        ok7 &= opnorm(dag(Rn) @ Rn - sum(kron_all([RR if j == i else np.eye(d) for j in range(n)]) for i in range(n))) < 1e-9
        ok7 &= opnorm(Rn) <= math.sqrt(n) * kappa + 1e-9
        for t in (1e-3, 0.1, 0.7, 2.0):
            Vt = expm(-1j * t * Wn) @ Vn @ expm(1j * t * Hn)
            ok7 &= opnorm(dag(Vt) @ Wn @ Vt - Hn) < 1e-8 and opnorm(Vt - Vn) <= t * math.sqrt(n) * kappa + 1e-9
    rows7.append(f"{name}: kappa = {kappa:.4f}")
R.check("(c): balance with a seed (H_E = K + e_0 I > 0): V^*WV = H + e_0 I, V^*R = 0, R_n^*R_n = sum_i (R^*R)_i, "
        "||R_n|| <= sqrt(n) kappa, V_t^* W_n V_t = H_n + n e_0, ||V_t - V^(x)n|| <= |t| sqrt(n) kappa; kappa > 0 exactly "
        "for the non-covariant channels", ok7, "; ".join(rows7))

# the exact ladder lift for the replacement channel (energy differences in (E/2) Z)
E = 1.0
chP = Channel([np.outer(psi_p, np.eye(2)[i]) for i in range(2)], np.diag([0.0, E]).astype(complex))
K, _ = solve_K(chP)
e0 = 1.0
Vp, W, HE = with_seed(chP, K, e0)
kappa = opnorm(W @ Vp - Vp @ (chP.H + e0 * np.eye(2)))
omega = E / 2
ok7b, worst7b = True, 0.0
for n in (1, 2):
    Vn = kron_all([Vp] * n)
    dim_out = Vn.shape[0]
    hin = np.real(np.diag(sum(kron_all([chP.H if j == i else np.eye(2) for j in range(n)]) for i in range(n))))
    wout_ops = sum(kron_all([W if j == i else np.eye(W.shape[0]) for j in range(n)]) for i in range(n))
    ew, Uw = np.linalg.eigh(wout_ops)
    shifts = np.round(ew / omega).astype(int)
    ok7b &= np.allclose(ew, shifts * omega)
    for ell in (4, 8, 16, 32):
        u_max = int(np.max(np.abs(shifts[:, None] - np.round((hin + n * e0) / omega)[None, :]))) + 1
        Lc = ell + 2 * u_max + 2
        chi = np.zeros(Lc)
        chi[u_max + 1:u_max + 1 + ell] = math.sqrt(2 / (ell + 1)) * np.sin(math.pi * (np.arange(ell) + 1) / (ell + 1))
        shift_in = np.round((hin + n * e0) / omega).astype(int)
        Vt = dag(Uw) @ Vn                                       # rows: eigenbasis of W_n
        lift = np.zeros((dim_out * Lc, 2 ** n * Lc), dtype=complex)
        for x in range(dim_out):
            for y in range(2 ** n):
                if abs(Vt[x, y]) < 1e-15:
                    continue
                dshift = shift_in[y] - shifts[x]
                for lvl in range(Lc):
                    if 0 <= lvl + dshift < Lc:
                        lift[x * Lc + lvl + dshift, y * Lc + lvl] += Vt[x, y]
        lift = np.kron(Uw, np.eye(Lc)) @ lift
        Hin_full = np.kron(np.diag(hin + n * e0), np.eye(Lc)) + np.kron(np.eye(2 ** n), np.diag(omega * np.arange(Lc)))
        Hout_full = np.kron(wout_ops, np.eye(Lc)) + np.kron(np.eye(dim_out), np.diag(omega * np.arange(Lc)))
        cols = [y * Lc + lvl for y in range(2 ** n) for lvl in range(u_max, Lc - u_max)]
        ok7b &= opnorm(dag(lift[:, cols]) @ lift[:, cols] - np.eye(len(cols))) < 1e-10
        ok7b &= opnorm((Hout_full @ lift - lift @ Hin_full)[:, cols]) < 1e-9
        err = 0.0
        for _ in range(20):
            v = rng.standard_normal(2 ** n) + 1j * rng.standard_normal(2 ** n)
            v /= np.linalg.norm(v)
            out = lift @ np.kron(v, chi)
            ideal = np.kron(Vn @ v, chi)
            err = max(err, np.linalg.norm(out - ideal))
            clockE = lambda st: np.real(np.vdot(st, np.kron(np.eye(st.size // Lc), np.diag(omega * np.arange(Lc))) @ st))
            ok7b &= abs(clockE(out) - clockE(np.kron(v, chi))) < 1e-9
        bound = math.pi ** 2 * kappa * math.sqrt(n) / (2 * omega * (ell + 1))
        ok7b &= err <= bound + 1e-12
        worst7b = max(worst7b, err / bound)
R.check("(c), the clock: the ladder lift of V^(x)n is an isometry that conserves energy exactly, leaves the clock's mean "
        "energy unchanged on every input, and is within pi^2 kappa sqrt(n)/(2 omega (l+1)) of V^(x)n (x) packet "
        "(replacement channel, n = 1, 2, l = 4..32)", ok7b, f"largest ratio {worst7b:.3f}")
ok7c = True
for kap in (0.1, 0.5, 1.3, 7.0):
    for om in (0.1, 0.5, 1.0, 3.0):
        for n in (1, 2, 3, 10, 1000):
            for a in (1.0, 0.5, 0.01):
                ell = math.ceil(2 * math.pi ** 2 * kap * math.sqrt(n) / (om * a))
                ok7c &= math.pi ** 2 * kap * math.sqrt(n) / (2 * om * (ell + 1)) <= a / 4
                ok7c &= om * (ell + 1) / 2 <= (math.pi ** 2 * kap + om) * math.sqrt(n) / a
for ell in (1, 5, 20, 100):
    chi = math.sqrt(2 / (ell + 1)) * np.sin(math.pi * (np.arange(ell) + 1) / (ell + 1))
    pE = chi ** 2
    med = np.arange(ell)[np.searchsorted(np.cumsum(pE), 0.5)]
    ok7c &= pE @ np.abs(np.arange(ell) - med) <= (ell + 1) / 2
R.check("(c): l = ceil(2 pi^2 kappa sqrt(n)/(omega a)) gives vector error <= a/4 and spread <= beta omega (l+1)/2 <= "
        "beta(pi^2 kappa + omega) sqrt(n)/a", ok7c)
mp.mp.dps = 30
ok7d = True
for Lw in (0.5, 3.0, 17.0):
    L_ = mp.mpf(Lw)
    f2 = mp.quad(lambda x: (mp.cos(mp.pi * x / (2 * L_))) ** 2 / L_, [-L_, L_])
    fp2 = mp.quad(lambda x: (mp.pi / (2 * L_) * mp.sin(mp.pi * x / (2 * L_))) ** 2 / L_, [-L_, L_])
    ok7d &= abs(f2 - 1) < mp.mpf(10) ** -25 and abs(mp.sqrt(fp2) - mp.pi / (2 * L_)) < mp.mpf(10) ** -25
kap, n, a = 1.7, 9, 0.3
L_ = 2 * math.pi * kap * math.sqrt(n) / a
ok7d &= abs(n * kap ** 2 * math.pi ** 2 / (4 * L_ ** 2) - a ** 2 / 16) < 1e-15
ok7d &= 2 * (a / (2 * math.sqrt(2)) + a / 2) <= 2 * a and 2 * (a / 4 + a / 2) <= 2 * a
R.check("(c), rank >= 2: f_L = L^{-1/2} cos(pi x/(2L)) has unit norm and ||f_L'||_2 = pi/(2L); at L = 2 pi kappa sqrt(n)/a "
        "the squared error n kappa^2 pi^2/(4L^2) = a^2/16; return errors 2(a/4 + a/2) and 2(a/(2 sqrt2) + a/2) are <= 2a",
        bool(ok7d))
# equidistribution of the Gram coefficients of the slab packet on Z^2 with omega = (1, sqrt2)
om2 = np.array([1.0, math.sqrt(2)])
Lw = 2.0
fL = lambda x: np.where(np.abs(x) <= Lw, np.cos(np.pi * x / (2 * Lw)) / math.sqrt(Lw), 0.0)
Gb = lambda u: np.prod(np.where(np.abs(u) < 1, np.exp(-1 / np.maximum(1 - u ** 2, 1e-300)), 0.0), axis=-1)
limit = lambda s: float(mp.quad(lambda x: (mp.cos(mp.pi * x / (2 * Lw)) * mp.cos(mp.pi * (x - s) / (2 * Lw)) / Lw)
                                if abs(x - s) <= Lw else 0, [-Lw, max(-Lw, s - Lw), Lw]))
errs = []
for Lam in (40, 160, 640):
    qs = np.array(np.meshgrid(np.arange(-Lam, Lam + 1), np.arange(-Lam, Lam + 1))).reshape(2, -1).T
    phi = fL(qs @ om2) * Gb(qs / Lam)
    phi /= np.linalg.norm(phi)
    idx = {tuple(q): i for i, q in enumerate(qs)}
    e_ = 0.0
    for zv in ((1, 0), (0, 1), (1, -1), (-2, 1), (3, -2)):
        sh = np.array([idx.get((q[0] - zv[0], q[1] - zv[1]), -1) for q in qs])
        val = np.sum(phi * np.where(sh >= 0, phi[sh], 0.0))
        e_ = max(e_, abs(val - limit(np.array(zv) @ om2)))
    errs.append(e_)
R.check("(c), rank 2: the Gram coefficients <phi_Lambda|T_z phi_Lambda> of the slab packet (omega = (1, sqrt2)) tend to "
        "int f_L(x) f_L(x - omega.z) dx as Lambda grows", errs[-1] < errs[0] and errs[-1] < 2e-3,
        "errors " + ", ".join(f"{e_:.1e}" for e_ in errs) + " at Lambda = 40, 160, 640")
ok7e = True
for dE in (2, 3, 6):
    spanHE = 1.7
    beta = 1.3
    for n in (1, 2, 10, 1000, 10 ** 6):
        for a in (1.0, 0.1, 1e-3):
            qt = min(a * a / (4 * n), n ** -2.0)
            w = spanHE + math.log(dE / qt) / beta
            ok7e &= dE * math.exp(-beta * (w - spanHE)) <= qt * (1 + 1e-12)
            ok7e &= math.sqrt(n * qt) <= a / 2 + 1e-15 and n * qt <= 1 / n + 1e-15
            ok7e &= w <= spanHE + (math.log(dE) + 2 * math.log(n + 1) + 2 * math.log(2 / a) + 2) / beta
    for j_e in np.linspace(0, spanHE, 5):
        w = 3.0
        ok7e &= abs((j_e + w + 0) - (0 + 0 + (w + j_e - 0))) < 1e-12        # e_j + w + 0 = e_0 + 0 + (w + e_j - e_0), e_0 = 0
hq = lambda q_: -q_ * math.log(q_) - (1 - q_) * math.log(1 - q_)
vals = [n * (hq(n ** -2.0) + n ** -2.0 * math.log(5)) for n in (10, 100, 10 ** 4, 10 ** 6)]
ok7e &= all(np.diff(vals) < 0) and vals[-1] < 1e-4
R.check("(c), seeds: q <= d_E e^{-beta(w - span H_E)} <= min{a^2/(4n), n^-2} with w = O(log(n/a)); sqrt(nq) <= a/2, "
        "nq <= 1/n; each swap conserves energy; the seeds' entropy n[h(q) + q log(d_E - 1)] -> 0", ok7e,
        "n = 10, 100, 1e4, 1e6: " + ", ".join(f"{v:.1e}" for v in vals))

# ---------------------------------------------------------------------------------------------------------------------
# 8. (d)
ok8 = True
for t in (0.0, 0.1, 0.7, 2.0):
    Ut = expm(-1j * t * np.diag([0, E]))
    kr = [Ut @ np.eye(2) @ dag(Ut) / math.sqrt(2), Ut @ X @ dag(Ut) / math.sqrt(2)]
    enc = np.zeros((4, 2))
    enc[2, 0] = 1                                             # |0_L> = |1>_S |0>_A
    enc[1, 1] = 1                                             # |1_L> = |0>_S |1>_A
    Pm = np.zeros((4, 4))
    for s_ in range(2):
        for a_ in range(2):
            Pm[2 * a_ + (s_ ^ a_), 2 * s_ + a_] = 1
    DL = np.diag([-E / 2, E / 2])
    UL = expm(-1j * t * DL)
    for XL in (np.array([[1, 0], [0, 0]]), np.array([[0, 1], [0, 0]]), np.array([[0, 0], [1, 0]]), np.array([[0, 0], [0, 1]])):
        rho4 = enc @ XL @ enc.T
        out = sum(np.kron(k, np.eye(2)) @ rho4 @ dag(np.kron(k, np.eye(2))) for k in kr)
        out = Pm @ out @ Pm.T
        logical = np.trace(out.reshape(2, 2, 2, 2), axis1=1, axis2=3)
        model = UL @ XL @ dag(UL)
        model = model * np.array([[1, math.cos(E * t)], [math.cos(E * t), 1]])
        ok8 &= np.allclose(logical, model, atol=1e-13)
for rr in (0.0, 0.3, 0.9):
    dephase = lambda m, rr=rr: m * np.array([[1, rr], [rr, 1]])
    ok8 &= abs(diamond_half(choi_of(dephase, 2), choi_of(lambda m: m, 2), 2, 2) - (1 - rr) / 2) < 1e-6
xg = np.linspace(0, 0.5, 2001)
ok8 &= all(np.all(1 - np.cos(xg) ** n <= n * xg ** 2 / 2 + 1e-15) for n in (1, 2, 10, 4096, 10 ** 6))
R.check("(d): on the flagged code Phi_{X,t} acts as Ad_{e^{-itD_L}} o Delta_{cos Et}, D_L = diag(-E/2, E/2); "
        "(1/2)||Delta_r - id||_diamond = (1-r)/2 (SDP); 1 - cos^n x <= n x^2/2", ok8)
ok8b = True
for eps in np.concatenate([np.geomspace(1e-14, 1 / 4096, 3000), [1 / 4096]]):
    for n in (4096, 5000, 10 ** 5, 10 ** 9):
        t = 64 * math.sqrt(eps) / (n * E)
        ok8b &= n * E ** 2 * t ** 2 / 4 <= eps / 4 * (1 + 1e-12)
        phi_ = t * n * E
        ok8b &= phi_ <= 1 + 1e-12 and 2 * math.sqrt(eps) + 2 * math.sqrt(2 * eps) < 8 * math.sqrt(eps)
        fmax = 8 * math.sqrt(eps) / math.sin(phi_ / 2)
        ok8b &= fmax <= math.pi / 8 + 1e-12 and 1 - fmax > 0.5
        ok8b &= abs(1 / (8 * t) - n * E / (512 * math.sqrt(eps))) <= 1e-9 * n * E / (512 * math.sqrt(eps))
R.check("(d), lower-bound chain: n E^2 t^2/4 = 1024 eps/n <= eps/4 for n >= 4096, phi = 64 sqrt(eps) <= 1, "
        "2 sqrt(eps) + 2 sqrt(2 eps) < 8 sqrt(eps), f <= 8 sqrt(eps)/sin(32 sqrt eps) <= pi/8, 1 - f > 1/2, and "
        "beta/(8t) = beta E n/(512 sqrt eps)", ok8b)
worst8c = 0.0
for trial in range(150):
    U = random_unitary(2, rng)
    r = int(rng.integers(2, 4))
    s_ = 10 ** rng.uniform(-3, -0.5)
    e0v = np.zeros((r, 1))
    e0v[0] = 1
    Wm = np.kron(U, e0v) + s_ * (rng.standard_normal((2 * r, 2)) + 1j * rng.standard_normal((2 * r, 2)))
    w, v = np.linalg.eigh(dag(Wm) @ Wm)
    Wm = Wm @ (v * w ** -0.5) @ dag(v)
    kr = [Wm.reshape(2, r, 2)[:, i, :] for i in range(r)]
    delta = diamond_half(choi_of(lambda m: sum(k @ m @ dag(k) for k in kr), 2), choi_of(lambda m: U @ m @ dag(U), 2), 2, 2)
    phi_b = np.eye(2).reshape(4) / math.sqrt(2)
    PsiW = np.kron(np.eye(2), Wm) @ phi_b
    PsiU = np.kron(np.eye(2), U) @ phi_b
    xv = PsiU.conj() @ PsiW.reshape(4, r)
    ev = xv / np.linalg.norm(xv)
    worst8c = max(worst8c, opnorm(Wm - np.kron(U, ev.reshape(r, 1))) / (2 * math.sqrt(delta)))
R.check("Stinespring continuity: a qubit channel within delta (half diamond) of a unitary U has ||W - U (x) e|| <= "
        "2 sqrt(delta) for the Uhlmann-aligned e (150 near-unitary channels)", worst8c <= 1, f"largest ratio {worst8c:.3f}")
# programmable phase gate: f sin(phi/2) <= 2 sqrt(d0) + 2 sqrt(d1), W_p^* W_q = f I
ok8d, worst8d = True, np.inf
for ell in (8, 32, 128):
    for phi_ in (0.05, 0.2, 0.6, 1.0):
        Nc = ell + 2
        pad = np.zeros(Nc)
        pad[1:ell + 1] = math.sqrt(2 / (ell + 1)) * np.sin(math.pi * (np.arange(ell) + 1) / (ell + 1))
        Nv = np.arange(Nc)

        def iso(prog):
            Wt = np.zeros((2, Nc, 2), dtype=complex)
            Wt[0, :, 0] = np.roll(prog, 1)
            Wt[1, :, 1] = np.roll(prog, -1)
            return Wt.reshape(2 * Nc, 2)

        pv = pad.astype(complex)
        qv = np.exp(-1j * (phi_ / 2) * Nv) * pad
        Wp, Wq = iso(pv), iso(qv)
        f = abs(np.vdot(pv, qv))
        ok8d &= np.allclose(dag(Wp) @ Wq, np.vdot(pv, qv) * np.eye(2))
        chan = lambda Wt: (lambda m: sum(Wt.reshape(2, Nc, 2)[:, c, :] @ m @ dag(Wt.reshape(2, Nc, 2)[:, c, :]) for c in range(Nc)))
        Uphi = expm(1j * (phi_ / 2) * Z)
        d0 = trace_norm(choi_of(chan(Wp), 2) - choi_of(lambda m: m, 2)) / 2
        d1 = trace_norm(choi_of(chan(Wq), 2) - choi_of(lambda m: Uphi @ m @ dag(Uphi), 2)) / 2
        worst8d = min(worst8d, 2 * math.sqrt(d0) + 2 * math.sqrt(d1) - f * math.sin(phi_ / 2))
zs_ = rng.standard_normal(20000) + 1j * rng.standard_normal(20000)
fs_ = rng.uniform(0, 1, 20000)
ph_ = rng.uniform(0, 2 * math.pi, 20000)
ep = np.minimum(np.abs(fs_ - zs_ * np.exp(1j * ph_ / 2)), np.abs(fs_ - zs_ * np.exp(-1j * ph_ / 2)))
mx = np.maximum(np.abs(fs_ - zs_ * np.exp(1j * ph_ / 2)), np.abs(fs_ - zs_ * np.exp(-1j * ph_ / 2)))
ok8d &= bool(np.all(mx >= fs_ * np.sin(ph_ / 2) - 1e-12))
zc = fs_ * np.cos(ph_ / 2)
mxc = np.maximum(np.abs(fs_ - zc * np.exp(1j * ph_ / 2)), np.abs(fs_ - zc * np.exp(-1j * ph_ / 2)))
ok8d &= bool(np.allclose(mxc, fs_ * np.abs(np.sin(ph_ / 2)), atol=1e-12))
R.check("no-programming step: two programs give W_p^* W_q = f I; max |f - z e^{+-i phi/2}| >= f sin(phi/2) (equality at "
        "z = f cos(phi/2); also proved in Lean); f sin(phi/2) <= 2 sqrt(err_0) + 2 sqrt(err_1) on a programmable phase gate",
        ok8d and worst8d >= 0, f"least slack {worst8d:.4f}")
ok8e = True
for trial in range(300):
    d = int(rng.integers(2, 4))
    a1, a2 = random_density(d, rng), random_density(d, rng)
    ok8e &= trace_norm(a1 - a2) / 2 >= 1 - fidelity(a1, a2) - 1e-12
R.check("(1/2)||alpha_t - alpha_C||_1 >= 1 - f (Fuchs-van de Graaf)", ok8e)
# (d) construction
ok8f, worstE, worstV = True, 0.0, 0.0
for eps in (1, 0.3, 1e-2, 1e-4, 1e-8):
    for eta in (1, 0.3, 1e-2, 1e-4, 1e-8):
        for n in (1, 3, 100, 10 ** 4, 10 ** 7):
            for bEv in (0.01, 1, 50):
                tau = min(eta, math.sqrt(eps), 0.25)
                Lc = math.ceil(100 * math.pi ** 2 * n / tau)
                m = math.ceil(max(2, 1e4 * n / tau ** 2, (1 / bEv) * math.log(1e4 * n / tau ** 2)))
                z = math.exp(-bEv * m) / (1 + math.exp(-bEv * m))
                err = math.pi ** 4 * n ** 2 / (Lc + 1) ** 2 + n / (2 * m)
                v = 2 * math.sqrt(n * z) + math.sqrt(n / m) + n / m + 3 * math.pi ** 2 * n / (2 * (Lc + 1))
                ok8f &= err < eps and v < tau / 10 and 2 * v < eta
                ok8f &= 2 * n * z <= 2 * tau ** 2 / 1e4 + 1e-300
                worstE, worstV = max(worstE, err / eps), max(worstV, v / tau)
                ok8f &= n * (2 * m + 3) + 1 > n * (2 * m + 3)
R.check("(d), construction constants: error pi^4 n^2/(L+1)^2 + n/(2m) < eps, v < tau/10, 2v < eta, drift 2nzE <= "
        "2E tau^2/10^4, and the margin b = n(2m+3)+1 exceeds the largest excursion n(2m+3) of 2m+3 levels per use",
        ok8f, f"largest error/eps {worstE:.1e}, largest v/tau {worstV:.4f}")
ok8g = True
for mm in (2, 5, 40):
    M = mm * E
    z = 1 / (1 + math.exp(M))
    Hs = np.diag([0, E])
    Am, Fm = powm_h(np.eye(2) - Hs / M, 0.5), powm_h(Hs / M, 0.5)
    lam = lambda r_: Am @ r_ @ Am + Fm @ r_ @ Fm
    ok8g &= diamond_half(choi_of(lam, 2), choi_of(lambda r_: r_, 2), 2, 2) <= 1 / (2 * mm) + 1e-7
    J = np.block([[Am, -Fm], [Fm, Am]])
    for _ in range(5):
        rho = random_density(2, rng)
        gain = 0.0
        for g, pg in ((0, 1 - z), (1, z)):
            st = J @ np.kron(dm(np.eye(2)[g]), rho) @ dag(J)
            eG = M * np.real(np.trace(st[2:, 2:]))
            sS = st[:2, :2] + st[2:, 2:]
            out = 0.5 * sS + 0.5 * X @ sS @ X                     # program bit in I/2 controls X
            gain += pg * (eG + np.real(np.trace(Hs @ out)) - np.real(np.trace(Hs @ rho)) - M * g)
        ok8g &= abs(gain - np.real(np.trace(rho @ (E / 2 * np.eye(2) - 2 * z * Hs)))) < 1e-12
R.check("(d), construction: the contact disturbs the system by at most 1/(2m) (SDP) and the initialized energy gain of "
        "system, B and G is exactly (E/2)I - 2zH", ok8g)

# ---------------------------------------------------------------------------------------------------------------------
# 9. the replacement stock and the table
rows9 = []
for n in (10, 100, 1000, 10 ** 4, 10 ** 5):
    k = np.arange(n + 1)
    p = binom.pmf(k, n, 0.5)
    med = k[np.searchsorted(np.cumsum(p), 0.5)]
    rows9.append((n, float(p @ np.abs(k - med)) / math.sqrt(n / (2 * math.pi))))
R.check("a stock of n states |+> has energy law Bin(n, 1/2) times E, so its spread is beta E x MAD -> beta E sqrt(n/(2 pi))",
        abs(rows9[-1][1] - 1) < 1e-2, ", ".join(f"n={n}: {r_:.4f}" for n, r_ in rows9))
ok9, worst9 = True, 0.0
for le in np.linspace(1, 12, 23):
    for lz in np.linspace(1, 24, 47):
        eta, eps = 10 ** -le, 10 ** -lz
        lower = max(1 / math.sqrt(eps), 1 / math.sqrt(eta * (eps + eta)))
        upper = max(1 / eta, 1 / math.sqrt(eps))
        if eps <= eta:
            ok9 &= upper / lower <= math.sqrt(2) + 1e-12
            worst9 = max(worst9, upper / lower)
        if eps >= 100 * eta:
            ok9 &= abs(upper / lower / math.sqrt(eps / eta) - 1) < 0.01 or upper / lower <= math.sqrt(eps / eta) * 1.01
        if eps <= eta ** 2 / 100:
            ok9 &= abs(lower * math.sqrt(eps) - 1) < 1e-12
        if eta ** 2 * 100 <= eps <= eta / 100:
            ok9 &= abs(lower * math.sqrt(eta * (eps + eta)) - 1) < 1e-12
for le in (2, 4, 8):
    for lz in (1, 2, 4, 8):
        eta, eps = 10 ** -le, 10 ** -lz
        a = min(2 * eps, eta / 2, 1.0)
        ok9 &= 1 / a <= 2 * max(1 / eta, 1 / eps, 1.0)
R.check("Table: for X-dephasing with eps = O(eta) the lower bounds max{n/sqrt eps, n/sqrt(eta(eps+eta))} and the upper "
        "bound n max{1/eta, 1/sqrt eps} agree within sqrt2; (d) decides when eps << eta^2, the reliable bound when "
        "eta^2 << eps << eta, and the sides differ by sqrt(eps/eta) when eta << eps; the balanced upper bound "
        "C sqrt(n)/a with a = min{2 eps, eta/2} is sqrt(n) max{eta^-1, eps^-1}", ok9, f"largest ratio {worst9:.3f}")
R.close()
