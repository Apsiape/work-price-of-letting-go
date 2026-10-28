"""Finite processes (combs), collisions and testers in the conventions of Section 2 and Appendix A.

Conventions (validated in check_setting.py by direct simulation):
  * The Choi operator of an n-slot process lives on (I_1, O_1, ..., I_n, O_n) and is
        R = sum |i><i'| (x) P(|i><i'|),
    with the unprimed inputs kept as the reference.  Its prefixes satisfy Tr_{O_j} R^(j) = I_{I_j} (x) R^(j-1).
  * A tester is described by its record C_n = Z_n on (I_1, O_1, ..., O_{n-1}, I_n): the physical state of the actual
    inputs and of the partners of maximally entangled halves fed in place of the outputs (Appendix E, eq. (E5)).
    The tester operator is t = Z_n (x) I_{O_n} and x = t^T, so that the observer's final state is
    nu = sqrt(x) R sqrt(x) (eq. (testerstate)).
  * A realization is an initial vector on a memory M_0 and a purifier F, and isometries
    V_j : I_j (x) M_{j-1} -> O_j (x) M_j (rows (O_j, M_j), columns (I_j, M_{j-1})).  A collision is the special
    case M_j = B for all j, with the initial vector |sqrt tau>> on B (x) F.
"""
import math

from qtools import entropy, herm, logm_psd, random_isometry, random_state, sqrtm_psd  # noqa: I001 (sets warning filters)
import cvxpy as cp
import numpy as np


# --------------------------------------------------------------------------------------------- realizations
class Realization:
    def __init__(self, dims, init, isos, mem_dims, dF):
        """dims: port dimensions d_j; init: vector on (M_0, F); isos[j]: matrix (d_j*M_{j+1}) x (d_j*M_j)."""
        self.dims = list(dims)
        self.n = len(dims)
        self.init = np.asarray(init, dtype=complex).reshape(mem_dims[0], dF)
        self.isos = [np.asarray(v, dtype=complex) for v in isos]
        self.mem = list(mem_dims)            # M_0 .. M_n
        self.dF = dF
        self._build()

    @classmethod
    def collision(cls, dims, tau, contacts):
        dB = tau.shape[0]
        init = sqrtm_psd(tau).reshape(-1)    # |sqrt tau>> on (B, F)
        return cls(dims, init, contacts, [dB] * (len(dims) + 1), dB)

    def _build(self):
        t = self.init.reshape(1, self.mem[0], self.dF)       # axes (prefix, M, F)
        self.prefix_vec = [t]
        for j, d in enumerate(self.dims):
            V = self.isos[j].reshape(d, self.mem[j + 1], d, self.mem[j])
            t = np.einsum("omia,paf->piomf", V, t)
            t = t.reshape(-1, self.mem[j + 1], self.dF)
            self.prefix_vec.append(t)
        self.vec = t                                           # (d^2, M_n, F)

    def prefix_choi(self, j):
        """Choi operator of the first j slots (memory and F traced); j = 0 gives [[1]]."""
        t = self.prefix_vec[j]
        m = t.reshape(t.shape[0], -1)
        return m @ m.conj().T

    @property
    def R(self):
        return self.prefix_choi(self.n)

    def RB(self):
        """Choi operator with the final memory (bath) kept, F traced; order (I_1 ... O_n, M_n)."""
        D = self.vec.shape[0] * self.vec.shape[1]
        m = self.vec.reshape(D, self.dF)
        return m @ m.conj().T

    def RF(self):
        """Choi operator with F kept, final memory traced; order (I_1 ... O_n, F)."""
        t = self.vec.transpose(0, 2, 1)
        m = t.reshape(t.shape[0] * t.shape[1], t.shape[2])
        return m @ m.conj().T

    def S_tau(self):
        """Entropy (bits) of the initial memory, i.e. S(F)."""
        return entropy(self.init @ self.init.conj().T)


def comb_from_channels(dims, isos, mem_dims):
    """Realization with no purifier (pure initial memory |0>)."""
    init = np.zeros(mem_dims[0], dtype=complex)
    init[0] = 1
    return Realization(dims, init, isos, mem_dims, 1)


# --------------------------------------------------------------------------------------------- testers
class Tester:
    """psi on (I_1, T_1); Ls[k] : (O_{k+1}, T_{k+1}) -> (I_{k+2}, T_{k+2}) for k = 0..n-2 (0-based slots)."""

    def __init__(self, dims, psi, Ls, tdims):
        self.dims = list(dims)
        self.n = len(dims)
        self.psi = np.asarray(psi, dtype=complex).reshape(dims[0], tdims[0])
        self.Ls = [np.asarray(L, dtype=complex) for L in Ls]
        self.tdims = list(tdims)

    def amplitudes(self, k):
        """K_k with Z_k = K_k K_k^*: rows (I_1, O_1, ..., O_{k-1}, I_k), columns T_k (k is 1-based)."""
        K = self.psi                                           # (I_1, T_1)
        for j in range(1, k):
            L = self.Ls[j - 1].reshape(self.dims[j], self.tdims[j], self.dims[j - 1], self.tdims[j - 1])
            K = np.einsum("imoa,pa->poim", L, K).reshape(-1, self.tdims[j])
        return K

    def record(self, k=None):
        k = self.n if k is None else k
        K = self.amplitudes(k)
        return K @ K.conj().T

    def record_by_epr(self, k=None):
        """Independent engine for (E5): feed the tester halves of normalized EPR pairs in place of the outputs and
        return the physical state of (A_1, R_1, ..., A_{k-1}, R_{k-1}, I_k), times c_k."""
        k = self.n if k is None else k
        state = self.psi.reshape(-1)                           # (A_1 = I_1, T_1)
        dims_list = [self.dims[0], self.tdims[0]]
        for j in range(1, k):
            d = self.dims[j - 1]
            phi = np.eye(d).reshape(-1) / math.sqrt(d)          # (O_j, R_j)
            st = np.kron(state, phi)                            # (..., T_j, O_j, R_j)
            nprev = int(np.prod(dims_list[:-1]))
            st = st.reshape(nprev, self.tdims[j - 1], d, d)
            L = self.Ls[j - 1].reshape(self.dims[j], self.tdims[j], d, self.tdims[j - 1])
            st = np.einsum("imoa,paor->prim", L, st)            # (prev, R_j, I_{j+1}, T_{j+1})
            state = st.reshape(-1)
            dims_list = dims_list[:-1] + [d, self.dims[j], self.tdims[j]]
        m = state.reshape(-1, self.tdims[k - 1])
        c = int(np.prod(self.dims[:k - 1])) if k > 1 else 1
        return c * (m @ m.conj().T)


def random_tester(dims, rng, tdim=3):
    n = len(dims)
    tdims = [tdim]
    for k in range(n - 1):
        tdims.append(max(tdim, -(-dims[k] * tdims[k] // dims[k + 1])))
    psi = random_state(dims[0] * tdims[0], rng)
    Ls = [random_isometry(dims[k + 1] * tdims[k + 1], dims[k] * tdims[k], rng) for k in range(n - 1)]
    return Tester(dims, psi, Ls, tdims)


def flat_record(dims):
    d = int(np.prod(dims))
    c = int(np.prod(dims[:-1]))
    return np.eye(c * c * dims[-1], dtype=complex) / d


def record_prefixes(Zn, dims):
    """[Z_1, ..., Z_n] from Z_n by Tr_{I_k} Z_k = Z_{k-1} (x) I_{O_{k-1}}."""
    out = [Zn]
    Zk = Zn
    for k in range(len(dims) - 1, 0, -1):
        pre = int(np.prod([dd * dd for dd in dims[:k - 1]])) if k > 1 else 1
        a, o, i = dims[k - 1], dims[k - 1], dims[k]
        t = Zk.reshape(pre, a, o, i, pre, a, o, i)
        Zk = np.einsum("paoiqboi->paqb", t).reshape(pre * a, pre * a) / o
        out.append(Zk)
    return out[::-1]


# --------------------------------------------------------------------------------------------- evaluation
def simulate(real, tester, H):
    """Direct simulation of a tester against a realization.  Returns the final memory state omega, the port states,
    the payload energy (energy units), S(Z|F) in bits, and the final global vector (O_n, T_n, M_n, F)."""
    dims = real.dims
    st = np.einsum("it,mf->itmf", tester.psi, real.init)      # (I_1, T_1, M_0, F)
    rin, rout = [], []
    for j in range(real.n):
        d = dims[j]
        m = st.reshape(d, -1)
        rin.append(m @ m.conj().T)
        V = real.isos[j].reshape(d, real.mem[j + 1], d, real.mem[j])
        st = np.einsum("omia,itaf->otmf", V, st)              # (O_j, T, M_j, F)
        m = st.reshape(d, -1)
        rout.append(m @ m.conj().T)
        if j < real.n - 1:
            L = tester.Ls[j].reshape(dims[j + 1], tester.tdims[j + 1], d, tester.tdims[j])
            st = np.einsum("iuot,otmf->iumf", L, st)
    sh = st.shape
    full = st.reshape(sh[0] * sh[1], sh[2], sh[3])
    m_mem = full.transpose(1, 0, 2).reshape(sh[2], -1)
    omega = m_mem @ m_mem.conj().T
    m_F = full.transpose(2, 0, 1).reshape(sh[3], -1)
    rhoF = m_F @ m_F.conj().T
    SZF = entropy(omega) - entropy(rhoF)                      # global purity: S(ZF) = S(M_n)
    energy = sum(np.trace(Hj @ (o - i)).real for Hj, i, o in zip(H, rin, rout))
    return dict(omega=omega, rin=rin, rout=rout, energy=energy, SZF=SZF, state=st)


def _contract(Z, R, dA, dK):
    """sum_{a,a'} Z[a',a] R[(a',k),(a,k')] for R on (A, K) with A of dim dA: the link product Tr_A[(Z^T (x) I) R]."""
    t = R.reshape(dA, dK, dA, dK)
    return np.einsum("ba,bxay->xy", Z, t)


def link(real, Zn, H):
    """The same quantities as `simulate`, from the Choi operators and the tester record (link products)."""
    dims = real.dims
    Zs = record_prefixes(Zn, dims)
    rin, rout = [], []
    for j in range(real.n):
        d = dims[j]
        pre = int(np.prod([dd * dd for dd in dims[:j]])) if j > 0 else 1
        Rp = real.prefix_choi(j)                               # on (I_1..O_{j})
        Zj = Zs[j].reshape(pre, d, pre, d)
        rin.append(np.einsum("ab,aibk->ik", Rp, Zj))           # sum R[a,b] Z[(a,i),(b,k)]
        Rj = real.prefix_choi(j + 1)                           # on (prefix, I_{j+1}, O_{j+1})
        rout.append(_contract(Zs[j], Rj, pre * d, d))
    dA = Zn.shape[0]
    RB = real.RB()
    omega = _contract(np.kron(Zn, np.eye(dims[-1])), RB, dA * dims[-1], real.mem[-1])
    energy_c = sum(np.trace(Hj @ (o - i)) for Hj, i, o in zip(H, rin, rout))
    return dict(omega=omega, rin=rin, rout=rout, energy=float(energy_c.real), energy_c=energy_c)


def nu_ZF(real, Zn):
    """The observer's purified final state (sqrt x (x) I_F) R^F (sqrt x (x) I_F), x = (Z_n (x) I_{O_n})^T."""
    x = np.kron(Zn, np.eye(real.dims[-1])).T
    sx = np.kron(sqrtm_psd(x), np.eye(real.dF))
    return sx @ real.RF() @ sx


# --------------------------------------------------------------------------------------------- linear functionals
def omega_map(real):
    """Function Z_n -> omega (final bath), linear."""
    dims = real.dims
    RB = real.RB()
    dA = int(np.prod([d * d for d in dims[:-1]])) * dims[-1]
    t = RB.reshape(dA, dims[-1], real.mem[-1], dA, dims[-1], real.mem[-1])
    Mt = np.einsum("boxaoy->baxy", t)                            # omega = sum_{b,a} Z[b,a] Mt[b,a]

    def f(Zn):
        return np.einsum("ba,baxy->xy", Zn, Mt)
    return f, Mt


def functional_matrix(fun, dim):
    """G with fun(Z) = Re Tr(G Z) for a real-linear functional of Hermitian Z (evaluated on a Hermitian basis)."""
    G = np.zeros((dim, dim), dtype=complex)
    for i in range(dim):
        for j in range(dim):
            E = np.zeros((dim, dim), dtype=complex)
            E[i, j] = 1
            G[j, i] = fun(E)
    return G


def energy_matrix(real, H):
    """G_e with payload energy = Re Tr(G_e Z_n) for every tester record Z_n."""
    dims = real.dims
    dA = int(np.prod([d * d for d in dims[:-1]])) * dims[-1]
    return functional_matrix(lambda Z: link(real, Z, H)["energy_c"], dA)


def bath_functional(Mt, A):
    """G with Tr(A omega(Z)) = Tr(G Z) for omega(Z) = sum_{b,a} Z[b,a] Mt[b,a]."""
    return np.einsum("xy,bayx->ab", A, Mt)


# --------------------------------------------------------------------------------------------- SDPs over testers
def tester_constraints(dims, Zn):
    """cvxpy constraints saying that Z_n is a tester record (eq. (E5))."""
    cons = [Zn >> 0]
    n = len(dims)
    cur = Zn
    for k in range(n - 1, 0, -1):
        pre = int(np.prod([d * d for d in dims[:k - 1]])) * dims[k - 1]
        o, i = dims[k - 1], dims[k]
        Zprev = cp.Variable((pre, pre), hermitian=True)
        cons.append(cp.partial_trace(cur, [pre * o, i], axis=1) == cp.kron(Zprev, np.eye(o)))
        cons.append(Zprev >> 0)
        cur = Zprev
    cons.append(cp.real(cp.trace(cur)) == 1)
    return cons


class TesterLP:
    """max over testers of Re Tr(G Z_n), compiled once with G as a parameter."""

    def __init__(self, dims):
        self.dims = dims
        dA = int(np.prod([d * d for d in dims[:-1]])) * dims[-1]
        self.dA = dA
        self.Z = cp.Variable((dA, dA), hermitian=True)
        self.G = cp.Parameter((dA, dA), hermitian=True)
        self.prob = cp.Problem(cp.Maximize(cp.real(cp.trace(self.G @ self.Z))), tester_constraints(dims, self.Z))

    def solve(self, G):
        self.G.value = herm(np.asarray(G, dtype=complex))
        self.prob.solve(solver="CLARABEL")
        return herm(self.Z.value), float(self.prob.value)


def maximize_score(real, H, beta, lp, iters=60, tol=1e-9, energy_only=False):
    """Fully corrective Frank-Wolfe maximization of S(omega_t) - S(tau) + (beta/ln2) e(t) (bits) over testers.

    Each step calls the SDP oracle with the linearization at the current point, then re-optimizes the weights of all
    vertices found so far.  Returns (Z, value, upper), where upper = value + duality gap is a certified upper bound on
    the maximum (up to the SDP accuracy), by concavity."""
    from scipy.optimize import minimize
    om, Mt = omega_map(real)
    Ge = energy_matrix(real, H)
    S0 = real.S_tau()
    dA = lp.dA
    c = beta / math.log(2)

    def f(Z):
        return entropy(om(Z)) - S0 + c * float(np.trace(Ge @ Z).real)

    verts = [np.eye(dA, dtype=complex) / int(np.prod(real.dims))]
    oms = [om(verts[0])]
    ens = [float(np.trace(Ge @ verts[0]).real)]
    w = np.array([1.0])
    upper = math.inf
    Z = verts[0]
    for k in range(iters):
        Z = sum(wi * V for wi, V in zip(w, verts))
        wom = herm(om(Z))
        Lw = -logm_psd(wom, 2, floor=1e-300)
        G = bath_functional(Mt, Lw) + c * Ge
        Zs, val = lp.solve(G)
        gap = val - float(np.trace(G @ Z).real)
        upper = min(upper, f(Z) + max(gap, 0.0))
        if gap < tol:
            break
        verts.append(Zs)
        oms.append(om(Zs))
        ens.append(float(np.trace(Ge @ Zs).real))
        w = np.append(w * 0.9, 0.1)
        OM = np.array(oms)
        EN = np.array(ens)

        def negf(x):
            W = np.einsum("i,ixy->xy", x, OM)
            return -(entropy(W) + c * float(x @ EN))

        def grad(x):
            W = herm(np.einsum("i,ixy->xy", x, OM))
            L = -logm_psd(W, 2, floor=1e-300)
            return -(np.real(np.einsum("xy,iyx->i", L, OM)) + c * EN)

        res = minimize(negf, w, jac=grad, method="SLSQP", bounds=[(0, 1)] * len(w),
                       constraints=[{"type": "eq", "fun": lambda x: x.sum() - 1, "jac": lambda x: np.ones_like(x)}],
                       options={"ftol": 1e-15, "maxiter": 500})
        if -res.fun >= -negf(w) - 1e-15:
            w = np.clip(res.x, 0, None)
            w /= w.sum()
        keep = w > 1e-12
        verts = [V for V, kk in zip(verts, keep) if kk]
        oms = [o for o, kk in zip(oms, keep) if kk]
        ens = [e for e, kk in zip(ens, keep) if kk]
        w = w[keep] / w[keep].sum()
    Z = sum(wi * V for wi, V in zip(w, verts))
    return Z, f(Z), upper


def strategy_distance(R1, R2, dims):
    """d_c(R1, R2) = max over two-outcome testers of the difference of outcome probabilities."""
    d = int(np.prod(dims))
    dA = int(np.prod([dd * dd for dd in dims[:-1]])) * dims[-1]
    Zn = cp.Variable((dA, dA), hermitian=True)
    T0 = cp.Variable((d * d, d * d), hermitian=True)
    cons = tester_constraints(dims, Zn) + [T0 >> 0, cp.kron(Zn, np.eye(dims[-1])) - T0 >> 0]
    prob = cp.Problem(cp.Maximize(cp.real(cp.trace(T0 @ herm(R1 - R2)))), cons)
    prob.solve(solver="CLARABEL")
    return float(prob.value)


def causal_defect(R, dims):
    """Largest violation of Tr_{O_j} R^(j) = I_{I_j} (x) R^(j-1) over the prefixes obtained by partial traces."""
    worst = 0.0
    cur = R
    for j in range(len(dims), 0, -1):
        pre = int(np.prod([d * d for d in dims[:j - 1]])) if j > 1 else 1
        d = dims[j - 1]
        t = cur.reshape(pre, d, d, pre, d, d)
        trO = np.einsum("aiobko->aibk", t).reshape(pre * d, pre * d)
        prev = np.einsum("aiobio->ab", t) / d
        worst = max(worst, float(np.max(np.abs(trO - np.kron(prev, np.eye(d))))))
        cur = prev
    worst = max(worst, abs(cur[0, 0] - 1) if cur.shape == (1, 1) else 1.0)
    return worst


def translation_generator(dims, H, slots=None, weights=None):
    """Sum_j w_j (H_j on O_j - H_j^T on I_j) on (I_1, O_1, ..., I_n, O_n): the generator of eq. (cov)."""
    n = len(dims)
    full = [x for d in dims for x in (d, d)]
    D = int(np.prod(full))
    G = np.zeros((D, D), dtype=complex)
    from qtools import embed
    for j in range(n):
        w = 1.0 if weights is None else weights[j]
        if slots is not None and j not in slots:
            continue
        G += w * (embed(H[j], [2 * j + 1], full) - embed(H[j].T, [2 * j], full))
    return G


# --------------------------------------------------------------------------------------------- constructions
def block_isometry(in_energies, out_energies, rng):
    """A random isometry mapping each eigenspace of the diagonal input energy into the same eigenspace of the output."""
    from qtools import random_isometry as riso
    ein, eout = np.asarray(in_energies, float), np.asarray(out_energies, float)
    V = np.zeros((len(eout), len(ein)), dtype=complex)
    for e in np.unique(ein):
        I_ = np.where(np.abs(ein - e) < 1e-9)[0]
        O_ = np.where(np.abs(eout - e) < 1e-9)[0]
        if len(O_) < len(I_):
            raise ValueError("energy shell too small for an isometry")
        V[np.ix_(O_, I_)] = riso(len(O_), len(I_), rng)
    return V


def minimal_realization(R, dims):
    """The minimal realization of Lemma "Covariant realization": V_j = (I_{O_j} (x) conj(R^(j))^{1/2} conj(R^(j-1))^{-1/2})(|I>> (x) id),
    as matrices from (I_j, copies of slots < j) to (O_j, copies of slots <= j)."""
    pref = [R]
    for j in range(len(dims), 0, -1):
        pre = int(np.prod([d * d for d in dims[:j - 1]])) if j > 1 else 1
        d = dims[j - 1]
        pref.append(np.einsum("aiobio->ab", pref[-1].reshape(pre, d, d, pre, d, d)) / d)
    pref = pref[::-1]                                             # R^(0) .. R^(n)
    Vs = []
    for j, d in enumerate(dims, start=1):
        Rb, Rb0 = pref[j].conj(), pref[j - 1].conj()
        ws, vs = np.linalg.eigh(herm(Rb))
        S = (vs * np.sqrt(np.where(ws > 1e-12, ws, 0))) @ vs.conj().T       # round-off eigenvalues set to zero
        w, v = np.linalg.eigh(herm(Rb0))
        inv = np.where(w > 1e-10, 1 / np.sqrt(np.clip(w, 1e-300, None)), 0)
        Sinv = (v * inv) @ v.conj().T
        P0 = Rb0.shape[0]
        V = np.einsum("bxio,xc->obic", S.reshape(-1, P0, d, d), Sinv)
        Vs.append(V.reshape(d * S.shape[0], d * P0))
    return Vs, pref


def realize_record(Zn, dims):
    """A tester whose record is the given positive chain (converse half of (E5))."""
    Zs = record_prefixes(Zn, dims)

    def amp(Zk):
        w, v = np.linalg.eigh(herm(Zk))
        keep = w > 1e-11
        return v[:, keep] * np.sqrt(w[keep])

    K = amp(Zs[0])
    psi, Ls, tdims = K, [], [K.shape[1]]
    for k in range(1, len(dims)):
        dprev, dk = dims[k - 1], dims[k]
        P = amp(Zs[k])                                            # rows (alpha, o, i), cols m'
        r = P.shape[1]
        Pt = P.reshape(-1, dprev, dk, r).reshape(K.shape[0] * dprev, dk * r)
        A = np.kron(K, np.eye(dprev))                             # rows (alpha, o), cols (m, o')
        W = np.linalg.pinv(A, rcond=1e-10) @ Pt                   # rows (m, o'), cols (i, m')
        L = W.reshape(K.shape[1], dprev, dk * r).transpose(2, 1, 0).reshape(dk * r, dprev * K.shape[1])
        Ls.append(L)
        tdims.append(r)
        K = (np.einsum("pm,imom2->poim2", K, L.reshape(dk, r, dprev, K.shape[1]))
             if False else _next_amp(K, L, dprev, dk, r))
    return Tester(dims, psi, Ls, tdims)


def _next_amp(K, L, dprev, dk, r):
    L4 = L.reshape(dk, r, dprev, K.shape[1])
    return np.einsum("imoa,pa->poim", L4, K).reshape(-1, r)
