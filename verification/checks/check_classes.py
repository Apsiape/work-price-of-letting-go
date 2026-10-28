#!/usr/bin/env python3
"""check_classes.py -- the fiber law for a released past (Theorem 7.1, Appendix I).

Prices (bits per episode, zero Hamiltonians):
  real time (x released before y arrives):  log2 F'(g),  F'(g) = max_z |{(c,y): g(c,y)=z}|  (c = continuation class)
  held      (x kept until y arrives):       log2 F(g),   F(g)  = max_{x,z} |{y: g(x,y)=z}|
  order price = log2 F' - log2 F  in [0, log2 K(g)];  = log2 K for reversible questions;  = 0 for a constant answer.

Checks (exact integer/rational arithmetic unless stated):
  1. constant answer g = z0: both schedules pay log2|Y| (Landauer erasure of y), order price 0.
     The naive "class count" formula would predict 0; this check fails if that formula is used.
  2. XOR task g = a xor y: held 0, real time 1, order price 1 bit.
  3. the record-transfer circuit (M,Y) = (a,y) -> (y, a xor y) answers every question, and its register holds y
     afterwards: zero entropy against the observer who always sends y = 0 (so a record is not yet a price).
  4. the steering observer: for every g, the fiber of the largest answer has F' pairs; against it, the
     upper-bound device (class register + fiber index) holds exactly log2 F' bits, and the index map is injective.
  5. exhaustive search over all 65536 tasks g: {0,1}^3 x {0,1} -> {0,1}: F <= F' <= K F always; F' = K and F = 1
     whenever the questions are reversible; and the naive class formula log2 K disagrees with log2 F' on 12,610 of them.
  6. the reversible three-bit task g = y + f(x) mod 3 with f(011)=1, f(100)=2, else 0: prices 1, 1, 1, log2 3 for
     released sets {3}, {1,3}, {2,3}, {1,2,3}; violation log2(3/2); exhaustive search over all 6561 such f finds
     no larger violation.
  7. linear tasks over GF(2): order price = rank(F_L), submodular (60 random F).
  8. the record and the exit (Section 7, "A record is not yet a price", and the reading of Lemma I.6): records of
     different classes stay orthogonal when the departing carrier leaves in the same state on both branches, and can
     coincide when it leaves in different states (the record moves into the answer), numerically. This illustrates
     why the steering observer, who makes every answer the same, closes the exit; it is not a separate lemma.
With --perturb the real-time price is replaced by the naive class count log2 K and checks 1, 4 must FAIL.
"""
import itertools, math, sys
import numpy as np

PERTURB = '--perturb' in sys.argv
rng = np.random.default_rng(20261013)
passed = failed = 0
def check(name, ok, info=''):
    global passed, failed
    passed += ok; failed += (not ok)
    print(('  ok    ' if ok else '  FAIL  ') + name + (f'  [{info}]' if info else ''))

def class_map(g, X, Y):
    prof = {x: tuple(g[(x, y)] for y in Y) for x in X}; cl = {}
    for x in X: cl.setdefault(prof[x], len(cl))
    return {x: cl[prof[x]] for x in X}, len(cl)

def F_held(g, X, Y):
    Z = {g[(x, y)] for x in X for y in Y}
    return max(sum(1 for y in Y if g[(x, y)] == z) for x in X for z in Z)

def F_real(g, X, Y):
    c, K = class_map(g, X, Y)
    if PERTURB: return K                       # the naive (wrong) formula
    reps = {}
    for x in X: reps.setdefault(c[x], x)
    Z = {g[(x, y)] for x in X for y in Y}
    return max(sum(1 for x in reps.values() for y in Y if g[(x, y)] == z) for z in Z)

def reversible(g, X, Y):
    Z = {g[(x, y)] for x in X for y in Y}
    return all(len({g[(x, y)] for y in Y}) == len(Y) == len(Z) for x in X)

# 1. constant answer
X = [0, 1]; Y = [0, 1]
g0 = {(x, y): 0 for x in X for y in Y}
check('constant answer: held price log2|Y| = 1, real-time price 1, order price 0 (Landauer, not order)',
      math.log2(F_held(g0, X, Y)) == 1 and math.log2(F_real(g0, X, Y)) == 1,
      f'held {math.log2(F_held(g0,X,Y)):.3f}, real {math.log2(F_real(g0,X,Y)):.3f}')

# 2. XOR
gx = {(x, y): x ^ y for x in X for y in Y}
check('XOR: held 0, real time 1, order price 1 bit', F_held(gx, X, Y) == 1 and F_real(gx, X, Y) == 2)

# 3. record transfer circuit
def transfer(a, y):           # CNOT M->Y then CNOT Y->M
    y2 = a ^ y; m2 = a ^ y2
    return m2, y2
ok3 = all(transfer(a, y)[1] == gx[(a, y)] and transfer(a, y)[0] == y for a in X for y in Y)
mem_y0 = {transfer(a, 0)[0] for a in X}
check('record-transfer circuit (a,y)->(y, a xor y) answers correctly and leaves the register holding y', ok3)
check('against the observer who always sends y = 0 the register ends in the constant state 0: zero entropy', mem_y0 == {0}, f'register values {sorted(mem_y0)}')

# 4. steering observer and the upper-bound device, on random tasks
ok4 = True; info4 = ''
for trial in range(40):
    kx, ky, kz = int(rng.integers(2, 5)), int(rng.integers(2, 4)), int(rng.integers(2, 4))
    Xr, Yr = list(range(kx)), list(range(ky))
    g = {(x, y): int(rng.integers(0, kz)) for x in Xr for y in Yr}
    c, K = class_map(g, Xr, Yr)
    reps = {}
    for x in Xr: reps.setdefault(c[x], x)
    Z = {g[(x, y)] for x in Xr for y in Yr}
    fibers = {z: [(cc, y) for cc, x in reps.items() for y in Yr if g[(x, y)] == z] for z in Z}
    z0 = max(fibers, key=lambda z: len(fibers[z]))
    Fp = len(fibers[z0])
    # device: class register, then (c,y) -> (index within fiber of g(c,y), g(c,y)); must be injective
    images = {}
    for cc, x in reps.items():
        for y in Yr:
            z = g[(x, y)]; idx = fibers[z].index((cc, y)); images[(cc, y)] = (idx, z)
    injective = len(set(images.values())) == len(images)
    # entropy of the register against the steering observer (uniform on the largest fiber): log2 Fp exactly
    idxs = {images[p][0] for p in fibers[z0]}
    ok4 &= injective and len(idxs) == Fp and Fp == F_real(g, Xr, Yr)
    if not ok4 and not info4: info4 = f'trial {trial}: Fp={Fp}, F_real={F_real(g,Xr,Yr)}, injective={injective}'
check('steering observer forces exactly log2 F\' bits; the class-and-index device is injective and attains it (40 random tasks)', ok4, info4)

# 5. exhaustive: three bits, two binary questions, binary answers
X3 = list(itertools.product([0, 1], repeat=3)); Y2 = [0, 1]
keys = [(x, y) for x in X3 for y in Y2]
ok5 = True; naive_disagree = 0; rev_ok = True
for code in range(1 << 16):
    g = {kk: (code >> i) & 1 for i, kk in enumerate(keys)}
    c, K = class_map(g, X3, Y2); F = F_held(g, X3, Y2); Fp = F_real(g, X3, Y2)
    if not (F <= Fp <= K * F): ok5 = False
    if reversible(g, X3, Y2) and not (F == 1 and Fp == K): rev_ok = False
    if Fp != K: naive_disagree += 1
check('all 65536 tasks: F <= F\' <= K F', ok5)
check('all 65536 tasks: reversible questions give F = 1 and F\' = K', rev_ok)
check('the naive class formula log2 K disagrees with the real-time price on thousands of tasks', naive_disagree > 10000, f'{naive_disagree} of 65536')

# 6. the reversible three-bit example, prices P(L) = log2 max_h K_h, and the exhaustive bound
Y3 = [0, 1, 2]
def price_rev(f, L):
    H = [i for i in range(3) if i not in L]; best = 1
    for h in itertools.product([0, 1], repeat=len(H)):
        vals = set()
        for xl in itertools.product([0, 1], repeat=len(L)):
            x = [0] * 3
            for i, v in zip(L, xl): x[i] = v
            for i, v in zip(H, h): x[i] = v
            vals.add(f[tuple(x)])
        best = max(best, len(vals))
    return math.log2(best)
f = {x: 0 for x in X3}; f[(0, 1, 1)] = 1; f[(1, 0, 0)] = 2
g6 = {(x, y): (y + f[x]) % 3 for x in X3 for y in Y3}
check('the mod-3 task has reversible questions', reversible(g6, X3, Y3))
P = {L: price_rev(f, L) for L in [(2,), (0, 2), (1, 2), (0, 1, 2)]}
check('prices P({3}) = 1, P({1,3}) = 1, P({2,3}) = 1, P({1,2,3}) = log2 3',
      all(abs(P[L] - v) < 1e-12 for L, v in [((2,), 1), ((0, 2), 1), ((1, 2), 1), ((0, 1, 2), math.log2(3))]),
      ', '.join(f'{v:.4f}' for v in P.values()))
viol = P[(0, 1, 2)] + P[(2,)] - P[(0, 2)] - P[(1, 2)]
check('submodularity violated by exactly log2(3/2) bits', abs(viol - math.log2(1.5)) < 1e-12, f'{viol:.6f}')
# consistency: for the full release, log2 F' of g6 equals P({1,2,3})
check('the real-time fiber price of the mod-3 task equals log2 K = log2 3', abs(math.log2(F_real(g6, X3, Y3)) - math.log2(3)) < 1e-12)
worst = 0.0
pairs = []
for A in range(3):
    for B in range(A + 1, 3):
        rest = [i for i in range(3) if i not in (A, B)]
        for r in range(len(rest) + 1):
            for S in itertools.combinations(rest, r): pairs.append((S, A, B))
for code in range(3 ** 8):
    ff = {}; cc = code
    for x in X3: ff[x] = cc % 3; cc //= 3
    for S, A, B in pairs:
        v = price_rev(ff, tuple(sorted(S + (A, B)))) + price_rev(ff, S) - price_rev(ff, tuple(sorted(S + (A,)))) - price_rev(ff, tuple(sorted(S + (B,))))
        if v > worst + 1e-12: worst = v
check('exhaustive search over all 6561 reversible tasks y + f(x) mod 3: largest violation is log2(3/2)', abs(worst - math.log2(1.5)) < 1e-12, f'{worst:.6f}')

# 7. linear tasks
def rank_gf2(M):
    M = [row[:] for row in M]; r = 0; cols = len(M[0]) if M else 0
    for col in range(cols):
        piv = next((i for i in range(r, len(M)) if M[i][col]), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(len(M)):
            if i != r and M[i][col]: M[i] = [a ^ b for a, b in zip(M[i], M[r])]
        r += 1
    return r
ok_rank = ok_sub = True
for _ in range(60):
    kk, m = int(rng.integers(2, 5)), int(rng.integers(1, 4))
    Fm = [[int(rng.integers(0, 2)) for _ in range(kk)] for _ in range(m)]
    Xl = list(itertools.product([0, 1], repeat=kk)); Yl = list(itertools.product([0, 1], repeat=m))
    prices = {}
    for r in range(kk + 1):
        for L in itertools.combinations(range(kk), r):
            Hh = [i for i in range(kk) if i not in L]; best = 1
            for h in itertools.product([0, 1], repeat=len(Hh)):
                vals = set()
                for xl in itertools.product([0, 1], repeat=len(L)):
                    x = [0] * kk
                    for i, v in zip(L, xl): x[i] = v
                    for i, v in zip(Hh, h): x[i] = v
                    vals.add(tuple(sum(Fm[i][j] * x[j] for j in range(kk)) % 2 for i in range(m)))
                best = max(best, len(vals))
            pr = math.log2(best); prices[L] = pr
            FL = [[Fm[i][j] for j in L] for i in range(m)] if L else [[] for _ in range(m)]
            if abs(pr - rank_gf2(FL)) > 1e-12: ok_rank = False
    for L1 in prices:
        for L2 in prices:
            U = tuple(sorted(set(L1) | set(L2))); I = tuple(sorted(set(L1) & set(L2)))
            if prices[L1] + prices[L2] + 1e-12 < prices[U] + prices[I]: ok_sub = False
check('linear tasks: order price of released set L equals rank(F_L) over GF(2) (60 random F)', ok_rank)
check('linear tasks: the rank price is submodular', ok_sub)

# 8. the record and the exit: orthogonal records stay orthogonal when the carrier leaves in the same state
def haar(n):
    z = (rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))) / np.sqrt(2)
    q, r = np.linalg.qr(z); return q * (np.diag(r) / np.abs(np.diag(r)))
def complete(vs):
    n = len(vs[0]); M = np.column_stack(vs + [rng.normal(size=n) + 1j * rng.normal(size=n) for _ in range(n - len(vs))])
    q, _ = np.linalg.qr(M); return q
same_ok = True; diff_seen = False
for _ in range(50):
    dB, dC = 4, 2
    V = haar(dB); r0, r1 = V[:, 0], V[:, 1]
    y = np.array([1, 0]); z = np.array([0, 1]); zp = np.array([1, 0])
    src0, src1 = np.kron(r0, y), np.kron(r1, y)
    # same output state z on both branches
    t0 = np.kron(haar(dB)[:, 0], z); t1 = np.kron(haar(dB)[:, 1], z); t1 -= t0 * np.vdot(t0, t1); t1 /= np.linalg.norm(t1)
    W = complete([t0, t1]) @ complete([src0, src1]).conj().T
    o0 = (W @ src0).reshape(dB, dC); o1 = (W @ src1).reshape(dB, dC)
    if abs(np.trace((o0 @ o0.conj().T) @ (o1 @ o1.conj().T))) > 1e-10: same_ok = False
    # different output states: the device marginals may coincide (the record-transfer case)
    u = haar(dB)[:, 0]
    t0d, t1d = np.kron(u, z), np.kron(u, zp)
    Wd = complete([t0d, t1d]) @ complete([src0, src1]).conj().T
    p0 = (Wd @ src0).reshape(dB, dC); p1 = (Wd @ src1).reshape(dB, dC)
    if abs(np.trace((p0 @ p0.conj().T) @ (p1 @ p1.conj().T)) - 1) < 1e-10: diff_seen = True
check('record and exit: records of different classes stay orthogonal when the carrier leaves in the same state (50 instances)', same_ok)
check('and can become identical when the carrier leaves in different states (the record moves into the answer)', diff_seen)

print()
if PERTURB:
    if failed == 0: print('NEGATIVE CONTROL DID NOT FIRE'); sys.exit(1)
    print(f'negative control fired as required ({failed} check(s) failed under --perturb)'); sys.exit(0)
if failed: print(f'{failed} check(s) failed.'); sys.exit(1)
print('All checks passed.')
