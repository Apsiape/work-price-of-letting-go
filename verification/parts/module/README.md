# Machine checks

`python verification/run_all.py` runs every check below and exits with status 0 only if all pass. The Python checks
need the packages in `requirements.txt`; `check_lean.py` needs Lean 4.30.0 and Mathlib v4.30.0 (see the end of this
file). Each script prints what it verifies. The whole run takes about five minutes and well under 1 GB of memory.

The manuscript is the authority for the statements and their proofs. The checks fall into two kinds. **Formal
proofs** in Lean are complete proofs of the stated lemmas for all parameters. **Exact and numerical computations**
in Python establish some identities in exact rational arithmetic and check others numerically to a tolerance of 1e-10 or better, recompute the numbers quoted in the text (apart from those listed below as not checked),
and test inequalities on many random or perturbed instances; a computation of this second kind checks the instances it
runs, not the general statement. Where an inequality is sharp, the instances include cases at or near equality, and
the check fails if too few of them occur; where a stated constant is not sharp, the check reports the largest ratio
observed and, when it is easy, also tests the sharp constant with an instance that attains it.

Section, appendix and paragraph numbers in this file and in the scripts are those of the companion paper *The work
cost of answering in real time*, version 1.0.2, which Appendix F of the manuscript reproduces: its Sections 2-7 are
Appendices F.1-F.6 of the manuscript, its Appendices A-F are Appendices F.7-F.12, and its paragraphs B.1-B.7 and
C.1-C.5 are Steps 1-7 of Appendix F.8 and Steps 1-5 of Appendix F.9, whose closing Remarks are its C.6.

Two helper modules are shared by the scripts. `qtools.py` holds small linear-algebra helpers and the `Report` class.
`combs.py` evaluates finite processes, dilations and adaptive testers in the conventions of Section 2 and Appendix A
by two independent routes, direct simulation of testers with quantum memory and link products of Choi operators with
the tester record, which `check_setting.py` validates against each other; it also provides the SDPs over testers
(largest linear score, strategy distance) and a fully corrective Frank-Wolfe method that maximizes the score of a
dilation over all testers and returns a certified upper bound from its duality gap.

## Formal proofs (Lean 4 with Mathlib)

| File | What is proved | Manuscript |
|---|---|---|
| `lean/Gibbs.lean` | The finite Gibbs variational principle and its equality case; for the delay process, `h(p) - βE p ≤ ln(1 + e^{-βE})` with equality at the Gibbs state, while the two terms maximized separately give `ln 2`, which is larger; the entropy of an integer-valued variable is at most `λμ + ln Σ_b e^{-λ b²}` | Sections 2 and 7 (delay process), Appendix B.7 |
| `lean/Order.lean` | Controlled-`Z` conserves every diagonal Hamiltonian and controlled-`X` conserves it exactly when `Q` is degenerate; on all bits the masked record gives `Y₂ = B ⊕ A ⊕ R` and `M = Y₂ ⊕ B`; `I(M : a) = ln 2 - h(p)`; entropies of independent registers add; the four entries of the classical-agents table, the extra `h(p)` of the agent whose memory is a function of the past, and the extra bit for keeping the memory in copy-out; single-shot formation of a biased bit costs `ln(2(1-p)) > ln 2 - h(p)` | Proposition "Order costs work" and its proof, Section 7 "Classical agents" |
| `lean/HiddenBit.lean` | `3/2 + cos 2t + sin 2t < (1 + 1/√2)²` for `0 < t < π/8`, with equality at `π/8` (so `v_t` is below the branchwise worst case); the purified overlap of the branches is at least `|cos t|`; the process depends on `t` only modulo `π` | Section 7 "A correlated process", Appendix "The correlated process" |
| `lean/Lift.lean` | The whole-history phase lift `L(X) = Σ P_e X P_f ⊗ T_{a_f - a_e}` on any lattice group: only one intermediate label contributes to a product, `L` is multiplicative, `*`-preserving and unital, and every nonzero entry conserves external energy plus `H_P`; SWAP conjugation leaves `H ⊗ 1 + 1 ⊗ H` invariant | Appendix E (E21); Sections 5 and 7 (delay devices) |
| `lean/Converse.lean` | A degenerate battery target costs `log2` of its rank (`b_β(P_B) ≤ βW/ln2 + log2 R_B`); `m + 2·C(m,2) = m²` informationally complete vectors per block and `Σ m_b² ≤ (Σ m_b)²`; the arithmetic of the cap lemma (`a₀ Z_K = (1-s)/2`, the constant 4 at `s = 1/2`); `4δ/r ≤ 1/16`; `1 - 2 log2(δ p_G) ≤ 13 + 4 log2(1/p)`; the assembly of (eq. eat) and (eq. cap); with `a = min{δ/16, δ²/(256 C_f²)}` the final inequality holds for all `N` with `C_f √(13N) ≤ Nδ/8` and `Nδ/8 > 4` | Section 4, Appendix C.2, C.4, C.5 |
| `lean/Counting.lean` | `Σ_{k ≤ αN} C(N,k) L^k ≤ e^{N h(α)} L^{αN}` for `0 < α ≤ 1/2`, `L ≥ 1` (the bound `|G| ≤ 2^{N θ_γ}`) | Appendix C.3 |
| `lean/Repair.lean` | The exponent bookkeeping of Step 6 (`L^{-1/3} = g^{1/4} L^{r/2 - 1/3} = g^{1/(6r)}` for `L = g^{-1/(2r)}`, and `g^{1/6}` for `r ≤ 1`); the lattice energy identity of Step 7; the Chernoff exponent `N^{5/8}` of B.4 | Appendix D Steps 6-7, Appendix B.4 |
| `lean/Binning.lean` | `min{1, |x|/h} ≤ |e^{x/2} - 1|/(1 - e^{-h/2})` for all real `x` and `h > 0` | Appendix D Step 3 |
| `lean/Ladder.lean` | For all `D ≥ 1` and `L`: the episode-clock ladder swap conserves energy, resets the clock, maps valid columns to valid states, is injective and never lands on an initialized column (so it completes to a full energy-conserving permutation), and all ladder levels have equal Gibbs weight; exact flat-rank formation has equal tile weights and equal exchanged block dimensions | Appendix D Step 9, Appendix E "Exact flat-rank formation" |
| `lean/Factory.lean` | The chains (E9), (E10) and (E27); the four factory debits sum to `m F_τ + (r - k + mσ) ln2/β + 2s₀` with `r - k + mσ ∈ [mγ + 3, mγ + 5]`; typical fibers fit the residue and `#typical/K ≤ 2^{-mγ}`; the cache averages, the capital formula (E20) given additivity of relative entropy, `p = N/m`, and the clock charge `m a_m` | Appendix E (E9)-(E14), (E16)-(E20), (E27) |

Every theorem is audited with `#print axioms` and may use only `propext`, `Classical.choice` and `Quot.sound`.

## Exact and numerical computations (Python)

| Script | What is checked | Manuscript |
|---|---|---|
| `check_setting.py` | The two engines agree on 72 adaptive testers; `ν_ZF = √x R^F √x` and `S(Z|F) = S(ω_t) - S(τ)`; the rare-branch record is the tester record (E5), and every positive chain, including SDP extreme points, is realized by an explicit tester; the causal constraints; the minimal realization of the covariant-realization lemma on random covariant combs, all rank deficient (isometries, reproduction, energy conservation with the stated memory Hamiltonians, invariant supports); common versus separate covariance of the delay process; `ω_t ≤ d²ω₀` (the sharp constant `cd` is attained); the strategy-distance bound via SDP; the score bound (its entropy part attained); concavity and flag cancellation (minimax); causal accumulation with correlated devices; the accounting identity and (E3) on 40 random energy-conserving devices; the product bound of "Basic properties" (b); the ports example | Sections 2-3, Appendix A, (E1), (E3), (E5) |
| `check_law.py` | The joint tangent of B.2 via SDP (equality at the maximizer, support condition, a singular and an energy-dominated case); the rounding of B.2 and eq. (tangent); the filtered contacts of B.3; the B.4 exponent; the constants of B.6-B.7 and the geometric-tail bound on `Z_{P_X}`; the entropy bound for integer variables (equality at the Gibbs law); covariance by a flagged grid of common phases without increasing the gain (B.1) | Section 3, Appendix B |
| `check_converse.py` | `b_β` for one eigenstate and for degenerate targets (with equality cases); the invariant tester of C.1, its minimal dilations, stage isometries and energy intertwining; `Tr H_Z ν_Z` equals the payload energy for invariant testers; the informationally complete instrument of C.2; the counting bound of C.3 in exact integers; every step of the cap lemma and its conclusion, with the smooth min-entropy computed by an SDP; the constants of C.4-C.5, with an explicit threshold in `N` | Section 4, Appendix C |
| `check_free.py` | The defect identity (eq. defect), the prefix identity (eq. prefix) with three slots, the Gibbs tester; the gauge (eq. gauge); `D(σ‖η_j) = Σ a_l ≤ g` and the square-root bound (the reverse order fails); `‖√ρ - √σ‖₂² ≤ D_nat(ρ‖σ)` with near-equality cases; eq. (common) on random and nearly thermal dilations with certified gains; thermal realizations score `-D(ω_t‖σ)`; Steps 1, 3 (exact offset integration and the bin inequality with near-equality cases), 4, 6 (sympy, Dirichlet by brute force), 7 and 9; Werner-Holevo | Section 5, Appendix D |
| `check_noncov.py` | On a random non-covariant two-slot dilation: (E1), the rare-branch contacts and distance `≤ δ` (E4), the rare-branch record (E5), (E6), the joint tangent (E7), (E8), a positive `D_hist` and its trace and norm bounds (E9), the accessible effect (E10), and the hot-qubit contact (E11) with full simulation of episodes | Section 6, Appendix E (E1)-(E11) |
| `check_factory.py` | The four-work-qubit factory for `m` up to 1024 in high precision (E13)-(E14); the energy-shell support converter on an explicit tile reservoir; exact flat-rank formation in rationals; the cyclic cache on an exact classical model (E16)-(E19); the capital (E20); the phase lift (E21); the sine register and a lattice-lifted episode (E22)-(E23); the ledger (E25)-(E27) | Appendix E |
| `check_order.py` | The masked-record device implements `P_{p,V}` exactly; the one-channel thermal-operation circuit and its energy conservation; `I(M : a) = 1 - h(p)`; the inequality `ΔS_D ≥ 1 - h(e₁) - h(e₂)` on 500 perturbed devices with classical and quantum probes (the ideal device attains equality); `e₁ ≤ ε`, `e₂ ≤ p + ε` with `ε` from an SDP; the masked-record dilation scores exactly `1 - h(p)` and the batch realization at most 0; single-shot formation | Proposition "Order costs work" and its proof |
| `check_delay.py` | The delay process: score formula on adaptive testers, the maximum `log2(1 + e^{-βE})` (certified), the separate maxima, the lower-bound tester on scrambled exact extensions, the free-energy reading; delayed channels: `κ_β(Φ) + log2 Z_H` and `κ_β(Φ)` with a Gibbs filler for Hadamard, `X`, a phase, the identity and amplitude damping; `E/√2` for the Hadamard gate (sympy); covariance of `P_Φ`; separate phases move the delay process by 1/2; the half-distance bound of the remark on covariance | Sections 2 and 7, Discussion "Clocks", Remark "Why covariance" |
| `check_hidden_bit.py` | `S(Z|F) = 0` with a classical copy of `b`; the tester SDP gives `v_t` for `0 < t < π/8` and `(E/2)(1 + 1/√2)` for `π/8 ≤ t ≤ 7π/8`, and the value depends on `t` modulo `π`; the fidelity-constrained pair program; reachable pairs (necessity on random testers, sufficiency by explicit testers); the four eigenphases; the branchwise worst case; the kept state is the tester record; a positive heat effect of norm `≤ 8E/δ` (SDP); the constant chain; the lift of Appendix F, Step 2 (`F² = (1 + R·R′)/2` for qubits, and no mixed pair within the angle beats `v_t`) | Section 7 "A correlated process", Appendix "The correlated process" |
| `check_agents.py` | The four constructions of the table implement the process exactly and cost `1 - h(p)`, `1`, `2 - h(p)`, `2`; keeping the memory in copy-out costs one bit more; batch costs and the online excesses; a function-of-past memory must determine `A`; `ΔS_D ≥ 2 - h(e₁) - h(e₂)` in copy-out on perturbed devices; phase coins cost nothing; the case `p = 1/2` | Section 7 "Classical agents" |
| `check_lean.py` | compiles the Lean files and audits their axioms | — |

## What is not checked by machine

The general proofs are not formalized. In particular: the minimax and the construction of Appendix B beyond the
steps listed above (the strip estimate and three-lines argument of B.3, the bank identity (eq. lifted) of B.4, the
finite bank of B.5 and the truncated second moments of B.7); the entropy-accumulation argument of the strong converse
and the existence of the affine tradeoff of C.2; the process telescope of Step 5 and the limit argument of Step 8 in
Appendix D, so eq. (modulus) is checked only through its ingredients; the phase-drift bounds (E15) and (E24), the
closedness argument behind (E9) and the quantifier order of Appendix E as a whole; and every lower bound that ranges
over all extensions or all devices (the values of `K_β` in Section 7 are checked by matching devices and by specific
testers on exact extensions, not by an infimum over extensions). The real-time cost `κ_β` of a channel, including the
amplitude-damping formula used for delayed channels, and the other results listed in the appendix "Results from the
companion papers" are imported and are checked in the companion repositories. The energy-bank example of Section 4
rests on a single derivation and is not checked; for the comparison with Thompson et al. only our own constructions
and their costs are checked, not the cited formulas. Order-of-magnitude statements about hardware (the clock capital
of order `E N^20`, the battery dimension `32(N+1)²`) and all statements about the literature are not checked.

## Lean setup

The proofs build with Lean 4.30.0 and Mathlib v4.30.0. Either point `MATHLIB_DIR` at a Mathlib v4.30.0 checkout whose
cache has been fetched (`lake exe cache get`), or fetch Mathlib into this folder:

    cd verification/lean
    lake exe cache get
    lake build

`check_lean.py` then compiles each file with `lake env lean` and checks the axiom report.
