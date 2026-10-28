"""Release rank and the classical witness (Proposition "Release rank", Appendix "Release rank", Section 8).

Checks:
  1. the compiler stores G a_L and returns b + F a exactly on every input, with memory entropy rank F_L on fair inputs;
  2. rank F_L = rank F - dim C(R) for the subcode C(R) of words supported in R (random matrices);
  3. min over |R| <= m of rank F_L equals rank F - max{d : d_d(C) <= m}, with the generalized Hamming weights d_d
     computed independently by enumerating subcodes;
  4. holding m carriers lowers the cost exactly when C has a nonzero word of weight at most m;
  5. the shell-stock reset is a full permutation that conserves energy, returns the memory to |0> on every initialized
     branch, puts heat (1-q) r w into the stock and leaves the battery entropy at h2(q) + q r at most;
  6. the classical witness: the time-sharing device has errors e1, e2 and entropy increase exactly 1 - h2(e1 + e2) for
     e1 + e2 <= 1/2, this is not the trade-off above 1/2, and Delta S_D >= 1 - h2(delta) on perturbed quantum devices
     for every measured disagreement delta; the noise register is cleared while the first carrier is still held: on
     every branch the first step alone, which acts on (A, S, N, M) before A is released, leaves A' = a + s n,
     M = a + (1 - s) n and N = 0, and the second step acts on (B, S, N, M) only.
"""
import itertools
import math

import numpy as np

from qtools import Report, apply, dm, embed, entropy, h2, ket, near_unitary, ptrace

R = Report("Release rank")
rng = np.random.default_rng(20261011)


def rank2(m):
    """Rank over F2 of a 0/1 matrix."""
    m = np.array(m, dtype=np.uint8) % 2
    m = m.copy()
    r = 0
    rows, cols = m.shape
    for c in range(cols):
        piv = next((i for i in range(r, rows) if m[i, c]), None)
        if piv is None:
            continue
        m[[r, piv]] = m[[piv, r]]
        for i in range(rows):
            if i != r and m[i, c]:
                m[i] ^= m[r]
        r += 1
        if r == rows:
            break
    return r


def row_basis(m):
    m = np.array(m, dtype=np.uint8) % 2
    basis = []
    for row in m:
        cand = basis + [row]
        if rank2(np.array(cand)) > len(basis):
            basis.append(row)
    return np.array(basis, dtype=np.uint8).reshape(len(basis), m.shape[1])


def codewords(F):
    k = F.shape[1]
    B = row_basis(F)
    words = set()
    for coeffs in itertools.product((0, 1), repeat=B.shape[0]):
        w = np.zeros(k, dtype=np.uint8)
        for c, row in zip(coeffs, B):
            if c:
                w ^= row
        words.add(tuple(w))
    return words, B


def solve_T(FL, G):
    """T with FL = T G over F2, G having independent rows spanning the row space of FL."""
    T = np.zeros((FL.shape[0], G.shape[0]), dtype=np.uint8)
    for i, row in enumerate(FL):
        for coeffs in itertools.product((0, 1), repeat=G.shape[0]):
            comb = np.zeros(G.shape[1], dtype=np.uint8)
            for c, g in zip(coeffs, G):
                if c:
                    comb ^= g
            if np.array_equal(comb, row):
                T[i] = coeffs
                break
        else:
            raise AssertionError("row not in the span")
    return T


# 1. compiler, exact on all inputs
ok_comp = ok_ent = True
for trial in range(150):
    k, l = int(rng.integers(1, 6)), int(rng.integers(1, 5))
    F = rng.integers(0, 2, (l, k)).astype(np.uint8)
    L = [i for i in range(k) if rng.random() < 0.6]
    Rset = [i for i in range(k) if i not in L]
    FL = F[:, L] if L else np.zeros((l, 0), dtype=np.uint8)
    G = row_basis(FL) if L else np.zeros((0, 0), dtype=np.uint8)
    rL = G.shape[0]
    T = solve_T(FL, G) if rL else np.zeros((l, 0), dtype=np.uint8)
    counts = {}
    for a in itertools.product((0, 1), repeat=k):
        a = np.array(a, dtype=np.uint8)
        aL, aR = a[L], a[Rset]
        mem = (G @ aL) % 2 if rL else np.zeros(0, dtype=np.uint8)
        counts[tuple(mem)] = counts.get(tuple(mem), 0) + 1
        for b in itertools.product((0, 1), repeat=l):
            b = np.array(b, dtype=np.uint8)
            out = (b + ((T @ mem) % 2 if rL else 0) + ((F[:, Rset] @ aR) % 2 if Rset else 0)) % 2
            ok_comp &= np.array_equal(out, (b + F @ a) % 2)
    p = np.array(list(counts.values())) / 2 ** k
    H = float(-np.sum(p * np.log2(p)))
    ok_ent &= abs(H - (rank2(FL) if L else 0)) < 1e-12 and len(counts) == 2 ** rL
R.check("the compiler returns b + F a exactly on every input (150 random tasks)", ok_comp)
R.check("on fair inputs the memory G a_L is uniform on rank F_L bits", ok_ent)

# 2-4. coding form
ok2 = ok3 = ok4 = True
for trial in range(120):
    k, l = int(rng.integers(2, 8)), int(rng.integers(1, 5))
    F = rng.integers(0, 2, (l, k)).astype(np.uint8)
    r = rank2(F)
    words, B = codewords(F)
    nz = [w for w in words if any(w)]
    # generalized Hamming weights by enumerating subcodes spanned by d codewords
    ghw = {0: 0}
    for d in range(1, r + 1):
        best = None
        for combo in itertools.combinations(nz, d):
            if rank2(np.array(combo)) < d:
                continue
            support = set()
            for c in combo:
                support |= {i for i, x in enumerate(c) if x}
            best = len(support) if best is None else min(best, len(support))
        ghw[d] = best
    for m in range(0, k + 1):
        brute = min(rank2(F[:, [i for i in range(k) if i not in Rs]]) if len(Rs) < k else 0
                    for size in range(0, m + 1) for Rs in itertools.combinations(range(k), size))
        formula = r - max(d for d in range(0, r + 1) if ghw[d] <= m)
        ok3 &= brute == formula
        helps = brute < r
        ok4 &= helps == any(sum(w) <= m for w in nz)
    for size in range(0, k + 1):
        for Rs in itertools.combinations(range(k), size):
            L = [i for i in range(k) if i not in Rs]
            dimCR = rank2(np.array([w for w in words if all(w[i] == 0 for i in L)])) if words else 0
            ok2 &= (rank2(F[:, L]) if L else 0) == r - dimCR
R.check("rank F_L = rank F - dim C(R) for every split (120 random codes)", ok2)
R.check("least cost with m held carriers = rank F - max{d : d_d(C) <= m}, against enumerated subcodes", ok3)
R.check("holding m carriers helps exactly when C has a nonzero word of weight <= m", ok4)

# 5. the shell-stock reset
ok5 = True
for r_, J in [(1, 1), (1, 2), (1, 4), (2, 1), (2, 2), (3, 1)]:
    K = 2 ** r_
    w = r_  # energies in units of kT ln2, so that w = r
    stock = [(j, z) for j in range(J + 1) for z in range(K ** j)]
    batt = [("g",)] + [("c", x) for x in range(K)]
    states = [(x, s, c) for x in range(K) for s in stock for c in batt]
    energy = lambda st: st[1][0] * w + (0 if st[2] == ("g",) else w)
    perm = {st: st for st in states}
    for x in range(K):
        for (j, z) in stock:
            src = (x, (j, z), ("c", 0))
            if j < J:
                img = (0, (j + 1, x * K ** j + z), ("g",))
            else:
                img = (0, (J, z), ("c", x))
            if src != img:
                assert perm[src] == src and perm[img] == img
                perm[src], perm[img] = img, src
    bij = sorted(map(repr, perm.values())) == sorted(map(repr, states))
    cons = all(energy(a) == energy(b) for a, b in perm.items())
    ret = all(perm[(x, s, ("c", 0))][0] == 0 for x in range(K) for s in stock)
    # Gibbs stock: microstate (j, z) has weight 2^{-j r} / (J+1); memory in any state; battery starts in c_0
    q = 1 / (J + 1)
    gibbs = {s: 2.0 ** (-s[0] * r_) / (J + 1) for s in stock}
    heat = sum(gibbs[s] / K * (perm[(x, s, ("c", 0))][1][0] - s[0]) * w for x in range(K) for s in stock)
    pW = {}
    for x in range(K):
        for s in stock:
            c = perm[(x, s, ("c", 0))][2]
            pW[c] = pW.get(c, 0) + gibbs[s] / K
    SW = -sum(p * math.log2(p) for p in pW.values() if p > 0)
    ok5 &= bij and cons and ret and abs(sum(gibbs.values()) - 1) < 1e-12 and abs(heat - (1 - q) * r_) < 1e-12 \
        and SW <= h2(q) + q * r_ + 1e-12 and abs(pW[("g",)] - (1 - q)) < 1e-12
R.check("reset: full energy-conserving permutation, memory returned on every branch, heat (1-q) r, "
        "battery entropy <= h2(q) + q r", ok5, "r in {1,2,3}, J up to 4")

# 6. classical witness: exact time-sharing device


def timeshare(e1, e2):
    """Errors and entropy increase of the time-sharing device (selector s, noise n, record M)."""
    t = e1 + e2
    ps = e1 / t if t > 0 else 0.0
    dist0, dist1, err1, err2 = {}, {}, 0.0, 0.0
    for s_ in (0, 1):
        for n in (0, 1):
            pr = (ps if s_ else 1 - ps) * (t if n else 1 - t)
            if pr == 0:
                continue
            dist0[(s_, n, 0)] = dist0.get((s_, n, 0), 0) + pr
            for a in (0, 1):
                A1, M = (a ^ n, a) if s_ == 1 else (a, a ^ n)
                err1 += pr / 2 * (A1 != a)
                for b in (0, 1):
                    err2 += pr / 4 * (((b ^ M) ^ b) != a)
                    dist1[(s_, 0, M)] = dist1.get((s_, 0, M), 0) + pr / 4
    H = lambda dd: -sum(p_ * math.log2(p_) for p_ in dd.values() if p_ > 0)
    return err1, err2, H(dist1) - H(dist0)


ok6 = True
for e1, e2 in [(0.01, 0.03), (0.05, 0.05), (0.002, 0.2), (0.1, 0.0), (0.2, 0.3), (0.0, 0.0)]:
    r1, r2, dS = timeshare(e1, e2)
    ok6 &= abs(r1 - e1) < 1e-12 and abs(r2 - e2) < 1e-12 and abs(dS - (1 - h2(e1 + e2))) < 1e-12
R.check("time-sharing device: errors e1, e2 and entropy increase exactly 1 - h2(e1 + e2) (e1 + e2 <= 1/2)", ok6)
r1, r2, dS = timeshare(0.1, 0.4)
R.check("above e1 + e2 = 1/2 the value 1 - h2(e1 + e2) is not the trade-off: errors (0.1, 0.4) <= (0.3, 0.4) "
        "cost 0 < 1 - h2(0.7)", abs(dS) < 1e-12 and r1 <= 0.3 and r2 <= 0.4 and 1 - h2(0.7) > 0.1,
        f"cost {dS:.2e}, 1 - h2(0.7) = {1 - h2(0.7):.3f}")

# perturbed quantum devices. Step 1 acts on (A, S, N, M) only and step 2 on (B, S, N, M) only, so the
# perturbations respect the release order; fair a and b, with observer copies kept as classical labels.
CN = np.eye(4, dtype=complex)[[0, 1, 3, 2]]
d4 = [2, 2, 2, 2]


def cnot4(c, t_):
    return embed(CN, [c, t_], d4)


def ccnot4(sval, c, t_):
    """CNOT c->t on the four sites, controlled on the selector (site 1) being sval."""
    P = np.diag([1, 0]).astype(complex) if sval == 0 else np.diag([0, 1]).astype(complex)
    return embed(P, [1], d4) @ cnot4(c, t_) + embed(np.eye(2) - P, [1], d4)


# step-1 sites (A, S, N, M) = 0..3; step-2 sites (B, S, N, M) = 0..3
ideal1 = cnot4(3, 2) @ cnot4(0, 2) @ ccnot4(0, 2, 3) @ ccnot4(1, 2, 0) @ cnot4(0, 3)
ideal2 = cnot4(3, 0)
dims = [2, 2, 2, 2, 2]          # (A, B, S, N, M)

# the order of the first step: n is cleared by n <- n + A' + M while A is still held, and only then is A released
order_ok = True
for a_, s_, n_ in itertools.product((0, 1), repeat=3):
    out = ideal1 @ ket((a_, s_, n_, 0))
    k = int(np.argmax(np.abs(out)))
    bits = tuple((k >> (3 - i)) & 1 for i in range(4))               # (A', S, N, M)
    order_ok &= abs(abs(out[k]) - 1) < 1e-12 and bits == (a_ ^ (s_ & n_), s_, 0, a_ ^ ((1 - s_) & n_))
R.check("witness: on every branch the first step, before A is released, leaves A' = a + s n, M = a + (1 - s) n and "
        "clears N (n <- n + A' + M); the second step touches only (B, S, N, M)", order_ok)
worst, informative = 1e9, 0
for trial in range(200):
    e1, e2 = rng.uniform(0, 0.15, 2)
    t = e1 + e2
    ps = e1 / t
    eps = rng.choice([0.0, 0.02, 0.05, 0.1])
    u1 = embed(ideal1 if eps == 0 else near_unitary(ideal1, eps, rng), [0, 2, 3, 4], dims)
    u2 = embed(ideal2 if eps == 0 else near_unitary(ideal2, eps, rng), [1, 2, 3, 4], dims)
    rhoD = np.diag([(1 - ps) * (1 - t), (1 - ps) * t, ps * (1 - t), ps * t]).astype(complex)
    rhoD = np.kron(rhoD, np.diag([1, 0]).astype(complex))          # (S, N, M), M blank
    S0 = entropy(rhoD)
    final_D = np.zeros((8, 8), dtype=complex)
    disagree = 0.0
    for a in (0, 1):
        for b in (0, 1):
            rho = np.kron(np.kron(dm(ket((a,))), dm(ket((b,)))), rhoD)
            out = apply(u2 @ u1, rho)
            final_D += ptrace(out, dims, [2, 3, 4]) / 4
            pAB = np.real(np.diag(ptrace(out, dims, [0, 1])))
            for x in (0, 1):
                for y in (0, 1):
                    disagree += pAB[2 * x + y] / 4 * (x != (y ^ b))
    if eps == 0:
        assert abs(disagree - t) < 1e-12
    informative += disagree < 0.2
    worst = min(worst, entropy(final_D) - S0 - (1 - h2(disagree)))
R.check("Delta S_D >= 1 - h2(delta) on 200 perturbed devices, for every disagreement delta",
        worst > -1e-9 and informative >= 100, f"{informative} informative, smallest slack {worst:.3e}")
R.close()
