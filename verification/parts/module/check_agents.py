"""Classical agents (Section 7, "Classical agents", and the table there).

The process: Y1 = A, then Y2 = B xor A xor R with a fresh coin R ~ Bern(p), p < 1/2.  Costs are entropy increases of
everything the device holds (memory, coins, blanks, kept cells), per episode, in bits, with uniform independent inputs;
at zero Hamiltonian this is the work in units of kT ln2 by the accounting identity.

Checks (exact enumeration over all bits, entropies to 30 digits):
  1. the four constructions of the table implement the process exactly, and their costs are 1 - h(p), 1, 2 - h(p), 2;
     the agents whose memory is a function of the past keep A; the unrestricted memory M = A xor R is not a function of
     the past but is fixed by the future, M = Y2 xor B;
  2. in the copy-out interface, keeping the memory instead of releasing it as the Y2 cell costs one bit more;
  3. batch costs: 0 in place and 2 - h(p) in copy-out (attained, and equal to max H(in) - H(out) over input laws);
     so the excess of the function-of-past agent over batch is h(p) in copy-out (Thompson et al.'s online cost) and the
     unrestricted agent's online price is 0 in copy-out and 1 - h(p) in place; both columns differ by h(p);
  4. a function-of-past memory must determine A: any agent whose memory after slot 1 does not distinguish A errs by at
     least (1 - 2p)/2 on some input;
  5. the lower bound for the unrestricted copy-out agent, Delta S_D >= 2 - h(e1) - h(e2), on perturbed quantum devices
     that use the kept inputs only as controls, with equality for the ideal device;
  6. one-time-pad phase coins dephase a coherent kept input and leave the coin's entropy unchanged (cost 0);
  7. at p = 1/2 an agent with no memory of A implements the process, so both columns agree.
"""
import itertools
import math

import mpmath as mp
import numpy as np

from qtools import CNOT, I2, Report, Z, apply, dm, embed, entropy, h2, ket, near_unitary, ptrace, random_density

R = Report("Classical agents")
mp.mp.dps = 30
rng = np.random.default_rng(77)


def H(dist):
    tot = mp.mpf(0)
    for v in dist.values():
        if v > 0:
            tot -= v * mp.log(v, 2)
    return tot


def marg(joint, f):
    out = {}
    for k, v in joint.items():
        key = f(k)
        out[key] = out.get(key, 0) + v
    return out


def h(p):
    return -p * mp.log(p, 2) - (1 - p) * mp.log(1 - p, 2)


def run(agent, p):
    """Enumerate a, b uniform, coins r ~ Bern(p), incoming mixed cells u1, u2.  Returns the joint distribution of
    (inputs, outputs, device before, device after)."""
    joint = {}
    for a, b, r, u1, u2 in itertools.product((0, 1), repeat=5):
        pr = mp.mpf(1) / 16 * (p if r else 1 - p)
        y1, y2, before, after = agent(a, b, r, u1, u2)
        key = (a, b, y1, y2, before, after)
        joint[key] = joint.get(key, 0) + pr
    return joint


# agents return (Y1, Y2, device registers before, device registers after)
def in_place_masked(a, b, r, u1, u2):
    M = r                                   # advance-committed coin
    before = (M,)
    M ^= a                                  # slot 1: add a into M, release a (carrier unchanged)
    y1 = a
    y2 = b ^ M                              # slot 2: B <- B xor M, released in place
    return y1, y2, before, (M,)


def in_place_fop(a, b, r, u1, u2):
    mem, R_ = 0, r
    before = (mem, R_)
    mem ^= a                                # memory = A, a function of the past
    y1 = a
    y2 = b ^ mem ^ R_
    return y1, y2, before, (mem, R_)


def copy_out_masked(a, b, r, u1, u2, keep_memory=False):
    M, blank1, blank2 = r, 0, 0
    before = (M, blank1, blank2)
    blank1 ^= a                             # write Y1 on a fresh blank, keep the incoming mixed cell u1
    y1 = blank1
    M ^= a
    M ^= b
    if keep_memory:
        blank2 ^= M
        y2 = blank2
        after = (u1, u2, M)
    else:
        y2 = M                              # release the memory register itself as the cell carrying Y2
        after = (u1, u2, blank2)
    return y1, y2, before, after


def copy_out_fop(a, b, r, u1, u2, keep_memory=False):
    mem, blank1, blank2, R_ = 0, 0, 0, r
    before = (mem, blank1, blank2, R_)
    blank1 ^= a
    y1 = blank1
    mem ^= a                                # memory = A
    mem ^= b
    mem ^= R_                               # a fresh coin added at the second slot
    if keep_memory:
        blank2 ^= mem
        y2 = blank2
        after = (u1, u2, mem, R_)
    else:
        y2 = mem
        after = (u1, u2, blank2, R_)
    return y1, y2, before, after


def batch_in_place(a, b, r, u1, u2):
    R_ = r
    return a, b ^ a ^ R_, (R_,), (R_,)


def batch_copy_out(a, b, r, u1, u2):
    R_, blank = r, 0
    before = (R_, blank)
    blank ^= a
    R_ ^= a ^ b
    return blank, R_, before, (u1, u2, 0)


def cost(agent, p):
    j = run(agent, p)
    return H(marg(j, lambda k: k[5])) - H(marg(j, lambda k: k[4])), j


def implements(j, p):
    """Exact output law: Y1 = a and P(Y2 = b xor a | a, b) = 1 - p."""
    ok = True
    for a, b in itertools.product((0, 1), repeat=2):
        cond = {k: v for k, v in j.items() if k[0] == a and k[1] == b}
        tot = sum(cond.values())
        py1 = sum(v for k, v in cond.items() if k[2] == a) / tot
        py2 = sum(v for k, v in cond.items() if k[3] == b ^ a) / tot
        ok &= abs(py1 - 1) < mp.mpf(10) ** -25 and abs(py2 - (1 - p)) < mp.mpf(10) ** -25
    return ok


ok1 = ok2 = ok3 = ok_mem = True
table = []
for p in (mp.mpf("0.1"), mp.mpf("0.25"), mp.mpf(1) / 3, mp.mpf("0.45")):
    c_ipm, j1 = cost(in_place_masked, p)
    c_ipf, j2 = cost(in_place_fop, p)
    c_com, j3 = cost(copy_out_masked, p)
    c_cof, j4 = cost(copy_out_fop, p)
    ok1 &= all(implements(j, p) for j in (j1, j2, j3, j4))
    tol = mp.mpf(10) ** -25
    ok1 &= abs(c_ipm - (1 - h(p))) < tol and abs(c_ipf - 1) < tol and abs(c_com - (2 - h(p))) < tol and abs(c_cof - 2) < tol
    table.append(f"p={float(p):.3f}: {float(c_ipm):.4f} {float(c_ipf):.4f} {float(c_com):.4f} {float(c_cof):.4f}")
    ck_m, _ = cost(lambda *x: copy_out_masked(*x, keep_memory=True), p)
    ck_f, _ = cost(lambda *x: copy_out_fop(*x, keep_memory=True), p)
    ok2 &= abs(ck_m - c_com - 1) < tol and abs(ck_f - c_cof - 1) < tol
    cb_ip, jb1 = cost(batch_in_place, p)
    cb_co, jb2 = cost(batch_copy_out, p)
    ok3 &= implements(jb1, p) and implements(jb2, p) and abs(cb_ip) < tol and abs(cb_co - (2 - h(p))) < tol
    ok3 &= abs((c_cof - cb_co) - h(p)) < tol and abs(c_com - cb_co) < tol and abs((c_ipm - cb_ip) - (1 - h(p))) < tol
    ok3 &= abs((c_ipf - c_ipm) - h(p)) < tol and abs((c_cof - c_com) - h(p)) < tol
    # the memories: FoP memory = A after slot 1; masked M = A xor R is not a function of (A, Y1) but M = Y2 xor B
    jm = {}
    for a, b, r in itertools.product((0, 1), repeat=3):
        pr = mp.mpf(1) / 4 * (p if r else 1 - p)
        M = r ^ a
        y2 = b ^ M
        jm[(a, M, y2, b)] = jm.get((a, M, y2, b), 0) + pr
    HM_given_past = H(marg(jm, lambda k: (k[0], k[1]))) - H(marg(jm, lambda k: k[0]))
    HM_given_future = H(marg(jm, lambda k: (k[1], k[2], k[3]))) - H(marg(jm, lambda k: (k[2], k[3])))
    ok_mem &= abs(HM_given_past - h(p)) < tol and abs(HM_given_future) < tol
    # batch lower bound: H(in) - H(out) over input laws (a, b) with q_a, q_b
    for qa, qb in ((0.5, 0.5), (0.2, 0.7), (0.9, 0.1)):
        qa, qb = mp.mpf(qa), mp.mpf(qb)
        def law(a, b):
            return (qa if a else 1 - qa) * (qb if b else 1 - qb)
        Hin_ip = H({(a, b): law(a, b) for a in (0, 1) for b in (0, 1)})
        out = {}
        for a, b, r in itertools.product((0, 1), repeat=3):
            key = (a, b ^ a ^ r)
            out[key] = out.get(key, 0) + law(a, b) * (p if r else 1 - p)
        ok3 &= Hin_ip - H(out) <= tol                                   # in place: never positive
        out2 = {}
        for a, b, r in itertools.product((0, 1), repeat=3):
            key = (a, a, b, b ^ a ^ r)
            out2[key] = out2.get(key, 0) + law(a, b) * (p if r else 1 - p)
        ok3 &= abs((Hin_ip + 2 - H(out2)) - (2 - h(p))) < tol           # copy-out: exactly 2 - h(p)
R.check("the four constructions implement the process exactly and cost 1 - h(p), 1, 2 - h(p), 2 (the table)",
        ok1, "; ".join(table))
R.check("the function-of-past memory is A; M = A xor R has H(M | A) = h(p) but H(M | Y2, B) = 0 (fixed by the future)", ok_mem)
R.check("in copy-out, keeping the memory instead of releasing it as the Y2 cell costs exactly one bit more", ok2)
R.check("batch costs 0 (in place) and 2 - h(p) (copy-out), attained and equal to max H(in) - H(out); the function-of-past "
        "agent pays h(p) more in both interfaces; online excess h(p), 0 and 1 - h(p)", ok3)

# 4. a function-of-past memory must determine A ------------------------------------------------------------------
worst = 1.0
for p in (0.1, 0.3, 0.45):
    # memory constant in A: then P(Y2 | a, b) cannot depend on a; best error = half the difference of the laws
    for q in np.linspace(0, 1, 101):        # any law of Y2 xor b the agent can produce, the same for both a
        err = max(0.5 * (abs(q - (1 - p)) + abs((1 - q) - p)), 0.5 * (abs(q - p) + abs((1 - q) - (1 - p))))
        worst = min(worst, err - (1 - 2 * p) / 2)
R.check("an agent whose memory after slot 1 does not distinguish A errs by at least (1 - 2p)/2 on some input",
        worst > -1e-12)

# 5. lower bound for the unrestricted copy-out agent on perturbed devices -------------------------------------------
SW = np.eye(4)[[0, 2, 1, 3]].astype(complex)


def controlled(ops):
    """sum_x |x><x| (x) ops[x] with the control first."""
    return sum(np.kron(dm(ket((x,))), op) for x, op in enumerate(ops))


def slot1_ideal():
    # sites (x1, y1, M, K): K ^= x1, M ^= x1, then swap y1 <-> K; as controlled on x1: ops on (y1, M, K)
    ops = []
    for x in (0, 1):
        flip = np.linalg.matrix_power(np.array([[0, 1], [1, 0]], dtype=complex), x)
        ops.append(embed(SW, [0, 2], [2, 2, 2]) @ np.kron(np.kron(I2, flip), flip))
    return ops


def slot2_ideal():
    # sites (x2, y2, M, K): M ^= x2, then swap y2 <-> M
    ops = []
    for x in (0, 1):
        flip = np.linalg.matrix_power(np.array([[0, 1], [1, 0]], dtype=complex), x)
        ops.append(embed(SW, [0, 1], [2, 2, 2]) @ np.kron(np.kron(I2, flip), I2))
    return ops


worst5, near5, exact5 = 1e9, 0, 0.0
for trial in range(200):
    p = float(rng.choice([0.05, 0.2, 0.35]))
    eps = float(rng.choice([0.0, 0.003, 0.01, 0.05, 0.2]))
    lam = float(rng.choice([0.0, 0.0, 0.02]))
    o1 = [near_unitary(o, eps, rng) if eps else o for o in slot1_ideal()]
    o2 = [near_unitary(o, eps, rng) if eps else o for o in slot2_ideal()]
    U1, U2 = controlled(o1), controlled(o2)
    rhoD = (1 - lam) * np.kron(np.diag([1 - p, p]), dm(ket((0,)))) + lam * random_density(4, rng)
    dims = [2, 2, 2, 2, 2, 2]                    # (x1, y1, x2, y2, M, K)
    U1f, U2f = embed(U1, [0, 1, 4, 5], dims), embed(U2, [2, 3, 4, 5], dims)
    e1 = e2 = 0.0
    Dfin = np.zeros((4, 4), dtype=complex)
    for a, b in itertools.product((0, 1), repeat=2):
        rho = np.kron(np.kron(np.kron(dm(ket((a,))), I2 / 2), np.kron(dm(ket((b,))), I2 / 2)), rhoD)
        rho = apply(U1f, rho)
        e1 += 0.25 * np.real(np.diag(ptrace(rho, dims, [1])))[1 - a]
        rho = apply(U2f, rho)
        pY2 = np.real(np.diag(ptrace(rho, dims, [3])))
        e2 += 0.25 * pY2[1 - (a ^ b)]            # the value of a xor r read as y2 xor b differs from a
        Dfin += 0.25 * ptrace(rho, dims, [4, 5])
    dS = entropy(Dfin) - entropy(rhoD)
    slack = dS - (2 - h2(e1) - h2(e2))
    worst5 = min(worst5, slack)
    near5 += slack < 0.02
    if eps == 0 and lam == 0:
        exact5 = max(exact5, abs(dS - (2 - h2(p))), abs(e2 - p), e1)
R.check("copy-out: Delta S_D >= 2 - h(e1) - h(e2) on 200 perturbed quantum devices; the ideal one attains 2 - h(p)",
        worst5 > -1e-10 and near5 >= 50 and exact5 < 1e-12, f"smallest slack {worst5:.2e}, {near5} within 0.02")

# 6. phase coins ----------------------------------------------------------------------------------------------------
ok6 = True
for _ in range(20):
    psi = rng.standard_normal(4) + 1j * rng.standard_normal(4)
    psi /= np.linalg.norm(psi)                    # (reference, kept input x)
    rho = np.kron(dm(psi), I2 / 2)                # coin uniform
    CZ3 = embed(np.diag([1, 1, 1, -1]).astype(complex), [2, 1], [2, 2, 2])
    out = apply(CZ3, rho)
    rx = ptrace(out, [2, 2, 2], [0, 1])
    deph = sum(np.kron(I2, dm(ket((x,)))) @ dm(psi) @ np.kron(I2, dm(ket((x,)))) for x in (0, 1))
    ok6 &= np.allclose(rx, deph) and abs(entropy(ptrace(out, [2, 2, 2], [2])) - 1) < 1e-12
R.check("a one-time-pad phase coin dephases a coherent kept input and its own entropy stays 1 (cost 0)", ok6)

# 7. p = 1/2 ------------------------------------------------------------------------------------------------------
def memoryless(a, b, r, u1, u2):
    R_ = r
    return a, b ^ R_, (R_,), (R_,)


half = mp.mpf(1) / 2
c_half, jh = cost(memoryless, half)
R.check("at p = 1/2 an agent with no memory of A implements the process at cost 0 = 1 - h(1/2) in place",
        implements(jh, half) and abs(c_half) < mp.mpf(10) ** -25)
R.close()
