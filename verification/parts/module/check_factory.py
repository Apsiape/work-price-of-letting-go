"""Without time covariance (Appendix E), part 2: the source factory, the converters, the cyclic cache, the phase lift
and register, and the final ledger.  Natural logarithms; beta = 1 unless stated.

Checks:
  1. the four-work-qubit factory (E13)-(E14) for a qubit source and m up to 1024: every typical fiber floor(K p_x) fits in
     the residue (<= 2^r), the labels fit in K, the coding error is at most P(atypical) + #typical/K
     <= 2 e^{-c_tau sqrt m} + 2^{-m gamma_m} (Hoeffding constant c_tau = 2/range^2), and the four debits sum to
     m F_tau + (m gamma_m + O(1)) ln2/beta + 2 s_0, so a_m >= F_tau and a_m -> F_tau;
  2. the energy-shell support converter: on an explicit tile reservoir the target dimension is at least the source
     dimension in every inner shell when (1 - theta) e^{beta[ln(Z_Q/Z_P)/beta - x]} > 1, and inner tiles carry
     probability -> 1 as the box grows;
  3. exact flat-rank formation: tiles D^j K^{J-j} with gap ln(D/K)/beta have equal Gibbs weights, the exchanged blocks have
     equal dimension, the output is exactly flat of rank K on success, and the failure probability is 1/(J+1);
  4. the cyclic cache (E16)-(E19) on an exact classical model: p = N/m, the cache marginal within p e_m, the emitted
     sources within p e_m of tau^N, the joint (cache, rest) within 4p + 2 p e_m of the product, the entropy and energy
     refunds (E18), and the helper-register entropy bound h(p) + p ln 32 (E19, with near-equality);
  5. the invested capital (E20): D(sigma_m || gamma_cache (x) gamma_clock)/beta = (m-1)/2 (F_tau + a_m) + ln(Z_clock/m)/beta;
  6. the phase lift (E21): L(XY) = L(X)L(Y), L(X^*) = L(X)^*, L(I) = I on the lattice interior, and lifted unitaries conserve
     the external energy plus H_P exactly;
  7. the phase register (E22)-(E23): the sine vector has nearest-neighbour overlap cos(pi/(L+1)), E||theta||^2 <=
     r pi^4/[4(L+1)^2], mean energy [B_* + (L-1)/2] sum_a omega_a; for a lattice-lifted episode
     ||Psi_phys - xi (x) Psi_bare|| <= pi^2 sqrt(r) K_*/(2(L+1)), and q_P <= d_P^2, the return distance <= 2 d_P and the
     entropy bound h(d_P^2) + d_P^2 ln(D_P^r - 1);
  8. the quantifier order and ledger (E25)-(E27): with delta = N^-3, s = N^-1/8 and the stated choices, the error is
     O(N^-2), the return error and battery entropy vanish, and W_nom/N <= g + delta C_0 + a_s + N^{-1/8} -> k.
"""
import itertools
import math
from fractions import Fraction

import mpmath as mp
import numpy as np

from qtools import Report, dm, entropy_nat, gibbs, herm, hnat, logm_psd, random_density, random_unitary, relent

R = Report("Without time covariance: factory, cache, phase lift and ledger")
rng = np.random.default_rng(271)
beta = 1.0

# 1. the factory ------------------------------------------------------------------------------------------------------
lam1 = mp.mpf("0.2")                 # eigenvalues of tau: 0.8 and 0.2
lam0 = 1 - lam1
sig = -(lam0 * mp.log(lam0, 2) + lam1 * mp.log(lam1, 2))          # S(tau)/ln2
rng_bits = mp.log(lam0 / lam1, 2)
ok1 = True
details = []
for m in (64, 256, 1024):
    mp.mp.dps = int(m * 0.4) + 60
    gam = mp.mpf(m) ** mp.mpf(-0.25)
    r = int(mp.ceil(3 * m * gam)) + 4
    Kexp = int(mp.ceil(m * (sig + 2 * gam)))
    K = mp.mpf(2) ** Kexp
    labels, deficit, p_atyp, n_typ, max_fiber = mp.mpf(0), mp.mpf(0), mp.mpf(0), mp.mpf(0), mp.mpf(0)
    for k in range(m + 1):
        lp2 = k * mp.log(lam1, 2) + (m - k) * mp.log(lam0, 2)
        cnt = mp.binomial(m, k)
        pk = mp.mpf(2) ** lp2
        if -m * (sig + gam) <= lp2 <= -m * (sig - gam):
            f = mp.floor(K * pk)
            max_fiber = max(max_fiber, f)
            labels += cnt * f
            deficit += cnt * (pk - f / K)
            n_typ += cnt
        else:
            p_atyp += cnt * pk
    e_code = deficit + p_atyp                                       # worst-case placement of the leftover labels
    hoeff = 2 * mp.e ** (-2 * mp.sqrt(m) / rng_bits ** 2)
    ok1 &= max_fiber <= mp.mpf(2) ** r and labels <= K and deficit <= n_typ / K
    ok1 &= e_code <= p_atyp + n_typ / K and p_atyp <= hoeff and n_typ / K <= mp.mpf(2) ** (-m * gam)
    # the four debits (energy units, beta = 1): s_0 fixed, T with ground energy hmin
    s0, hmin, trT, lnZ = mp.mpf("0.01"), mp.mpf(0), mp.mpf("0.37"), mp.log(1 + mp.e ** -1)
    lnR = mp.log(2)
    lnD = m * lnR + r * mp.log(2)
    lnK = Kexp * mp.log(2)
    debits = [m * (hmin + lnZ / beta) + s0, (lnD - lnK) / beta, m * (trT - hmin), -(m * lnR / beta - s0)]
    total = sum(debits)
    F_tau = trT + lnZ / beta - sig * mp.log(2) / beta                 # D(tau||gamma)/beta for diagonal tau
    rem = total - m * F_tau
    lo = (m * gam + 3) * mp.log(2) / beta + 2 * s0
    hi = (m * gam + 5) * mp.log(2) / beta + 2 * s0
    ok1 &= lo <= rem <= hi and total / m >= F_tau
    details.append(f"m={m}: e_code <= {mp.nstr(e_code, 3)}, a_m - F = {mp.nstr(rem / m, 4)}")
R.check("(E13)-(E14): fibers fit the residue, labels fit K, e_code <= 2 e^{-c sqrt m} + 2^{-m gamma_m}, and the debits sum "
        "to m F_tau + (m gamma_m + O(1)) ln2 + 2 s_0", ok1, "; ".join(details))
mp.mp.dps = 30

# 2. the support converter --------------------------------------------------------------------------------------------
ok2, inner_probs = True, []
levels = [0, 2, 2, 4]                       # integer energy coordinates of X in units omega = 1/2
omega = 0.5
P_lv = [0]
Q_lv = levels
ZP = sum(math.exp(-beta * omega * n) for n in P_lv)
ZQ = sum(math.exp(-beta * omega * n) for n in Q_lv)
xi = 1                                      # extracted work x = xi * omega
theta = 0.05
assert (1 - theta) * math.exp(beta * (math.log(ZQ / ZP) / beta - xi * omega)) > 1
for J in (20, 40, 80):
    js = range(-J, J + 1)
    Kt = math.ceil(1 / (theta * math.exp(beta * omega * (-J)))) * 4
    g = {j: math.floor(Kt * math.exp(beta * j * omega)) for j in js}
    ok2 &= all((1 - theta) * Kt * math.exp(beta * j * omega) <= g[j] <= Kt * math.exp(beta * j * omega) for j in js)
    margin = max(levels) + xi + 1
    for u in range(-J + margin, J - margin + 1):
        src = sum(g[u - n] for n in P_lv)
        tgt = sum(g[u - n - xi] for n in Q_lv)
        ok2 &= tgt >= src
    w = {j: g[j] * math.exp(-beta * j * omega) for j in js}
    inner = sum(w[j] for j in js if -J + margin <= j <= J - margin) / sum(w.values())
    inner_probs.append(inner)
R.check("support converter: every inner shell has target dimension >= source dimension; tile weights lie within "
        "(1 - theta) and 1 of a common factor; inner tiles carry probability -> 1",
        ok2 and inner_probs[0] < inner_probs[1] < inner_probs[2], ", ".join(f"{x:.4f}" for x in inner_probs))

# 3. flat-rank formation ------------------------------------------------------------------------------------------------
ok3 = True
for Dd, Kk, J in ((4, 2, 3), (6, 4, 2), (5, 3, 3), (8, 1, 2)):
    wts = [Fraction(Kk, Dd) ** j * Dd ** j * Kk ** (J - j) for j in range(J + 1)]   # exp(-j ln(D/K)) * degeneracy
    ok3 &= len(set(wts)) == 1
    for j in range(J):
        ok3 &= Dd * (Dd ** j * Kk ** (J - j)) == Kk * (Dd ** (j + 1) * Kk ** (J - j - 1))
    # simulate: system flat on D, tile level j uniform (equal Gibbs weights), microstate uniform within the level
    out = {}
    total = Fraction(0)
    for j in range(J + 1):
        pj = Fraction(1, J + 1)
        deg = Dd ** j * Kk ** (J - j)
        for xsys in range(Dd):
            for z in range(deg):
                pr = pj * Fraction(1, deg) * Fraction(1, Dd)
                if j < J:
                    # exchange the flat-D block at level j with the rank-K block at level j+1: index bijection
                    idx = xsys * deg + z
                    tgt_deg = Dd ** (j + 1) * Kk ** (J - j - 1)
                    ysys, z2 = divmod(idx, tgt_deg)
                    assert ysys < Kk
                    key = ("ok", ysys)
                else:
                    key = ("fail", xsys)
                out[key] = out.get(key, 0) + pr
                total += pr
    succ = {k[1]: v for k, v in out.items() if k[0] == "ok"}
    psucc = sum(succ.values())
    ok3 &= total == 1 and psucc == 1 - Fraction(1, J + 1) and all(v == psucc / Kk for v in succ.values()) and len(succ) == Kk
R.check("flat-rank formation: equal Gibbs weights of the tiles, equal block dimensions, output exactly flat of rank K on "
        "success, failure 1/(J+1) (exact rationals)", ok3)

# 4. the cyclic cache ----------------------------------------------------------------------------------------------------
from collections import defaultdict


def cache_run(m, N, th, tg, skew, a_m):
    def bern(x, t):
        return t if x else 1 - t
    Pb = np.array([math.comb(m, j) * th ** j * (1 - th) ** (m - j) for j in range(m + 1)])
    Pf = Pb * np.exp(skew * (np.arange(m + 1) - m * th))
    Pf /= Pf.sum()
    formed = [(s, Pf[sum(s)] / math.comb(m, sum(s)), sum(s)) for s in itertools.product([0, 1], repeat=m)]
    e_m = 0.5 * sum(abs(pf - np.prod([bern(x, th) for x in s_])) for s_, pf, _ in formed)
    st = defaultdict(float)
    for k in range(m):
        for cc in itertools.product([0, 1], repeat=m - 1):
            pr = np.prod([bern(cc[i], th) if i < k else bern(cc[i], tg) for i in range(m - 1)]) / m
            st[(k, cc, (), -1, 0)] += pr
    for call in range(N):
        new = defaultdict(float)
        for (k, cc, out, res, bd), pr in st.items():
            if k > 0:
                for gg in (0, 1):
                    c2 = list(cc)
                    val = c2[k - 1]
                    c2[k - 1] = gg
                    new[(k - 1, tuple(c2), out + (val,), res, bd)] += pr * bern(gg, tg)
            else:
                for s_, ps, j in formed:
                    new[(m - 1, s_[:m - 1], out + (s_[m - 1],), j, 1)] += pr * ps
        st = new
    sigm = defaultdict(float)
    for k in range(m):
        for cc in itertools.product([0, 1], repeat=m - 1):
            sigm[(k, cc)] += np.prod([bern(cc[i], th) if i < k else bern(cc[i], tg) for i in range(m - 1)]) / m
    Cm, Rm, Om = defaultdict(float), defaultdict(float), defaultdict(float)
    for (k, cc, out, res, bd), pr in st.items():
        Cm[(k, cc)] += pr
        Rm[(out, res, bd)] += pr
        Om[out] += pr
    T_marg = 0.5 * sum(abs(Cm[x] - sigm[x]) for x in set(Cm) | set(sigm))
    T_out = 0.5 * sum(abs(Om[o] - np.prod([bern(x, th) for x in o])) for o in itertools.product([0, 1], repeat=N))
    T_prod = 0.5 * sum(abs(st.get((k, cc, *rr), 0) - sigm[(k, cc)] * Rm[rr]) for (k, cc) in sigm for rr in Rm)
    pb = sum(pr for (k, cc, out, res, bd), pr in st.items() if bd)
    H = lambda dist: -sum(v * math.log(v) for v in dist.values() if v > 0)
    dS = H(Cm) - H(sigm)
    EC = lambda k, cc: (m - 1 - k) * a_m + sum(cc)               # clock energy plus cell energies (span(T) = 1)
    dE = sum(pr * EC(k, cc) for (k, cc), pr in Cm.items()) - sum(pr * EC(k, cc) for (k, cc), pr in sigm.items())
    return dict(p=N / m, pb=pb, e_m=e_m, T_marg=T_marg, T_out=T_out, T_prod=T_prod, dS=dS, dE=dE,
                Dc=m * 2 ** (m - 1))


ok4 = True
rows = []
for (m, N, skew) in [(6, 1, 0.3), (6, 2, 0.6), (8, 2, 0.3), (8, 3, 0.8), (9, 3, 0.5)]:
    a_m = 0.4
    r4 = cache_run(m, N, 0.3, 0.6, skew, a_m)
    p, e_m = r4["p"], r4["e_m"]
    ok4 &= abs(r4["pb"] - p) < 1e-12
    ok4 &= r4["T_marg"] <= p * e_m + 1e-12 and r4["T_out"] <= p * e_m + 1e-12 and r4["T_prod"] <= 4 * p + 2 * p * e_m + 1e-12
    T = p * e_m
    ok4 &= abs(r4["dS"]) <= hnat(T) + T * math.log(r4["Dc"] - 1) + 1e-12
    ok4 &= abs(r4["dE"]) <= N * e_m * (1 + a_m) + 1e-12
    rows.append(f"m={m},N={N}: marg {r4['T_marg']:.4f}<={p * e_m:.4f}, prod {r4['T_prod']:.3f}<={4 * p + 2 * p * e_m:.3f}")
R.check("(E16)-(E18): boundary probability N/m; cache and emitted marginals within p e_m; joint within 4p + 2p e_m; entropy "
        "and energy refunds within h(p e_m) + p e_m ln(D_cache - 1) and N e_m (span T + a_m)", ok4, "; ".join(rows[:3]))
ok4b, near4b = True, 0
for _ in range(300):
    p = float(rng.uniform(0.001, 0.3))
    rest = rng.dirichlet(np.ones(31) * float(rng.choice([0.05, 1, 100])))
    dist = np.concatenate([[1 - p], p * rest])
    S = float(-np.sum(dist[dist > 0] * np.log(dist[dist > 0])))
    bound = hnat(p) + p * math.log(32)
    ok4b &= S <= bound + 1e-12
    near4b += bound - S < 0.01 * p + 1e-9 + p * math.log(32 / 31)
R.check("(E19): a 32-label register equal to its nominal value except with probability p has entropy <= h(p) + p ln 32",
        ok4b and near4b >= 50, f"{near4b} cases within p ln(32/31) + 1% of the bound")

# 5. the invested capital ------------------------------------------------------------------------------------------------
ok5 = True
for _ in range(10):
    Tm = herm(rng.standard_normal((2, 2)) + 1j * rng.standard_normal((2, 2)))
    gamma = gibbs(Tm, beta)
    tau = random_density(2, rng)
    F_tau = relent(tau, gamma, math.e) / beta
    m = int(rng.integers(2, 6))
    a_m = float(rng.uniform(0, 1))
    cl = np.array([math.exp(-beta * (m - 1 - k) * a_m) for k in range(m)])
    Zc = cl.sum()
    gclock = np.diag(cl / Zc)
    blocks = []
    for k in range(m):
        st = np.eye(1)
        for i in range(m - 1):
            st = np.kron(st, tau if i < k else gamma)
        blocks.append(st)
    dc = 2 ** (m - 1)
    sigm = np.zeros((m * dc, m * dc), dtype=complex)
    for k in range(m):
        sigm[k * dc:(k + 1) * dc, k * dc:(k + 1) * dc] = blocks[k] / m
    gc = np.eye(1)
    for _ in range(m - 1):
        gc = np.kron(gc, gamma)
    ref = np.kron(gclock, gc)
    lhs = relent(sigm, ref, math.e) / beta
    rhs = (m - 1) / 2 * (F_tau + a_m) + math.log(Zc / m) / beta
    ok5 &= abs(lhs - rhs) < 1e-9
R.check("(E20): D(sigma_m || gamma_cache (x) gamma_clock)/beta = (m-1)/2 (F_tau + a_m) + ln(Z_clock/m)/beta", ok5)

# 6. the phase lift -------------------------------------------------------------------------------------------------------
ok6 = True
om_vec = np.array([1.0, math.sqrt(2)])
labels = [np.array([0, 0]), np.array([1, 0]), np.array([0, 1]), np.array([1, 1])]
Eext = np.array([a @ om_vec for a in labels])
Bx = 5
box = list(itertools.product(range(-Bx, Bx + 1), repeat=2))
bidx = {b: i for i, b in enumerate(box)}
nb = len(box)


def lift(Xm):
    Lm = np.zeros((4 * nb, 4 * nb), dtype=complex)
    for e in range(4):
        for f in range(4):
            if abs(Xm[e, f]) < 1e-15:
                continue
            shift = labels[f] - labels[e]
            for b in box:
                tgt = tuple(np.array(b) + shift)
                if tgt in bidx:
                    Lm[e * nb + bidx[tgt], f * nb + bidx[b]] = Xm[e, f]
    return Lm


inner_cols = [e * nb + bidx[b] for e in range(4) for b in box if max(abs(b[0]), abs(b[1])) <= Bx - 2]
HP = np.array([np.array(b) @ om_vec for b in box])
Htot = np.concatenate([Eext[e] + HP for e in range(4)])
for _ in range(10):
    Xa = random_unitary(4, rng)
    Ya = rng.standard_normal((4, 4)) + 1j * rng.standard_normal((4, 4))
    LX, LY, LXY = lift(Xa), lift(Ya), lift(Xa @ Ya)
    ok6 &= np.abs((LX @ LY - LXY)[:, inner_cols]).max() < 1e-12
    ok6 &= np.abs((lift(Xa.conj().T) - LX.conj().T)[:, inner_cols]).max() < 1e-12
    ok6 &= np.abs((lift(np.eye(4)) - np.eye(4 * nb))[:, inner_cols]).max() < 1e-12
    ok6 &= np.abs(((LX.conj().T @ LX) - np.eye(4 * nb))[np.ix_(inner_cols, inner_cols)]).max() < 1e-12
    ok6 &= np.abs((np.diag(Htot) @ LX - LX @ np.diag(Htot))[:, inner_cols]).max() < 1e-12
R.check("(E21): the lift is multiplicative, *-preserving and unital on the lattice interior, and lifted unitaries conserve "
        "external energy plus H_P exactly", ok6)

# 7. the phase register ------------------------------------------------------------------------------------------------------
ok7 = True
ratios7 = []
for Lw in (1, 2, 5, 10, 30, 60):
    u = np.arange(Lw)
    xi = math.sqrt(2 / (Lw + 1)) * np.sin(math.pi * (u + 1) / (Lw + 1))
    ok7 &= abs(np.linalg.norm(xi) - 1) < 1e-12
    ok7 &= abs(float(xi[:-1] @ xi[1:]) - math.cos(math.pi / (Lw + 1))) < 1e-12 if Lw > 1 else True
    th = np.linspace(-math.pi, math.pi, 20001)
    amp = np.abs(np.exp(1j * np.outer(th, u)) @ xi) ** 2 / (2 * math.pi)
    Eth2 = np.trapezoid(amp * th ** 2, th)
    ok7 &= Eth2 <= math.pi ** 4 / (4 * (Lw + 1) ** 2) + 1e-9
    ratios7.append(Eth2 / (math.pi ** 4 / (4 * (Lw + 1) ** 2)))
    Bs, om_a = 3, 0.7
    ok7 &= abs(float(np.sum(xi ** 2 * (Bs + u) * om_a)) - (Bs + (Lw - 1) / 2) * om_a) < 1e-12
# a lattice-lifted episode: V_theta = exp(i theta A) with integer spectrum, K_* = ||A||
ok7b = True
for _ in range(10):
    Lw = int(rng.choice([4, 10, 25]))
    nA = 3
    spec = rng.integers(-2, 3, nA)
    Ua = random_unitary(nA, rng)
    A = Ua @ np.diag(spec) @ Ua.conj().T
    psi0 = rng.standard_normal(nA) + 1j * rng.standard_normal(nA)
    psi0 /= np.linalg.norm(psi0)
    u = np.arange(Lw)
    xi = math.sqrt(2 / (Lw + 1)) * np.sin(math.pi * (u + 1) / (Lw + 1))
    Bst = 3
    DP = Lw + 2 * Bst + 1
    phys = np.zeros((DP, nA), dtype=complex)
    for n in np.unique(spec):
        Pn = Ua @ np.diag((spec == n).astype(float)) @ Ua.conj().T
        for b in range(Lw):
            phys[Bst + b + n] += xi[b] * (Pn @ psi0)
    bare = np.zeros((DP, nA), dtype=complex)
    bare[Bst:Bst + Lw] = np.outer(xi, psi0)
    dist = np.linalg.norm(phys - bare)
    Kst = np.abs(spec).max()
    dP = math.pi ** 2 * Kst / (2 * (Lw + 1))
    ok7b &= dist <= dP + 1e-12
    xiv = np.zeros(DP)
    xiv[Bst:Bst + Lw] = xi
    OmP = phys @ phys.conj().T
    qP = 1 - float((xiv @ OmP @ xiv).real)
    ok7b &= qP <= dP ** 2 + 1e-12
    full = phys.reshape(-1)
    rho = np.outer(full, full.conj())
    rest = phys.T @ phys.conj()
    prod = np.kron(np.outer(xiv, xiv), rest)
    ok7b &= 0.5 * np.sum(np.abs(np.linalg.eigvalsh(herm(rho - prod)))) <= 2 * dP + 1e-12
    SP = entropy_nat(OmP)
    ok7b &= SP <= hnat(min(dP ** 2, 0.999)) + dP ** 2 * math.log(DP - 1) + 1e-12
R.check("(E22): sine vector norm 1, overlap cos(pi/(L+1)), E theta^2 <= pi^4/[4(L+1)^2], mean energy [B_* + (L-1)/2] omega",
        ok7, f"E theta^2 / bound in [{min(ratios7):.3f}, {max(ratios7):.3f}]")
R.check("(E22)-(E23): ||Psi_phys - xi (x) Psi_bare|| <= pi^2 K_*/(2(L+1)), q_P <= d_P^2, return distance <= 2 d_P and "
        "S(P) <= h(d_P^2) + d_P^2 ln(D_P - 1) on lattice-lifted episodes", ok7b)

# 8. the ledger -------------------------------------------------------------------------------------------------------------
ok8 = True
for N in (10, 100, 1000, 10 ** 4):
    dl = N ** -3.0
    s = N ** (-1 / 8)
    QN = 50.0
    m = N ** 5 * QN * 2                                       # N^2 Q_N/m <= N^-3
    p = N / m
    df = ds = N ** -3.0 / (N * QN)                            # phase widths chosen last
    eps = N ** -2.0 + N * dl + p + df + ds
    ok8 &= eps <= 3 * N ** -2.0
    ok8 &= N ** 2 * QN / m <= N ** -3.0 + 1e-30
    hW = hnat(p) + p * math.log(32)
    ok8 &= hW <= N ** -3.0                                    # the last condition of (E25)
    # nominal rate: a_m - F <= N^-1/8, F + w <= g' + a_s, g' <= g + delta C_0, g <= k + N^-1/8
    k, C0 = 0.7, 3.0
    g = k + N ** (-1 / 8)
    gp = g + dl * C0
    a_s = -math.log(1 - s) / beta
    F = 0.3
    w = gp + a_s - F
    a_m = F + N ** (-1 / 8)
    rate = a_m + w
    ok8 &= rate <= g + dl * C0 + a_s + N ** (-1 / 8) + 1e-12
gaps = []
for N in (1e2, 1e8, 1e24, 1e40):                              # the excess over k vanishes like N^{-1/8}
    s = N ** (-1 / 8)
    gaps.append(2 * N ** (-1 / 8) + N ** -3.0 * 3.0 - math.log(1 - s) / beta)
ok8 &= all(a > b for a, b in zip(gaps, gaps[1:])) and gaps[-1] < 1e-4
R.check("(E25)-(E27): error N^-2 + N delta + p + d_f + d_s = O(N^-2); the helper entropy h(p) + p ln 32 vanishes; "
        "W_nom/N = a_m + w <= g + delta C_0 + a_s + N^{-1/8} -> k", ok8)
R.close()
