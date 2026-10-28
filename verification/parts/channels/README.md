# Machine checks

`python verification/run_all.py` runs every check below and exits with status 0 only if all pass. The Python checks
need the packages in `requirements.txt`; `check_lean.py` needs Lean 4.30.0 and Mathlib v4.30.0 (see the end of this
file). Each script prints what it verifies.

The manuscript is the authority for the statements and their proofs. The checks fall into two kinds. **Formal
proofs** in Lean are complete proofs of the stated lemmas for all parameters. **Exact and numerical computations**
in Python establish some identities in exact rational arithmetic and check others numerically to a tolerance of 1e-9 or better, recompute the numbers quoted in the text (apart from those listed below as not checked),
and test inequalities on many random or perturbed instances, including instances at or near equality; a computation
of this second kind checks the instances it runs, not the general statement.

## Formal proofs (Lean 4 with Mathlib)

| File | What is proved | Manuscript |
|---|---|---|
| `lean/Hadamard.lean` | For every `n`: the basis strings with `k` excitations number `C(n,k)`; the middle coefficient is the largest; `(n+1) C(n,⌊n/2⌋)² ≤ 4^n`, hence `2^{-n} C(n,⌊n/2⌋) ≤ 1/√(n+1)` and the error bound `1 - 2^{-n} C(n,⌊n/2⌋)` is at least `1 - 1/√(n+1)`, which tends to one | Proposition "A returning clock" |
| `lean/FiniteDevice.lean` | For all `R, n, k, w`: the ratio `C(R,k+w)/C(R+n,k)` does not increase in `k`, so the shells that cannot be moved form an upper tail; every movable shell has an injective, energy-conserving map onto its target; the qubit counts of Table 2 (the finite-device table). The integers of the finite saving: `w = 137` and `150` are the least with `2^w ≥ (3/2)^n` at `n = 234, 256`; refunds of `5` and `11` are the largest within the error budget; the error `10^{-12} + √(8·32·(5/6)^234)` is below `8.71·10^{-9}` | Section 4, "A finite example", Table 2 (finite device), "A finite saving" |
| `lean/WernerHolevo.lean` | Over `ℤ` after scaling by `√2`: `V` is an isometry, `VV^* = P₋`, tracing out either factor of `V` gives `W` (so `W` is its own complement), and the Choi state is `P₋/3`; over any commutative ring, `W^{-1}(Y) = Tr(Y) I - 2Yᵀ` is a two-sided inverse of `W` and fixes `I` | Section 5, Appendix "The Werner–Holevo support test" |
| `lean/Qutrit.lean` | For every `λ ∈ (0,1)`: `Δ_λ > 0`; `δ(λ) = Δ²/(4Δ + k)`; the complete chain of Steps 1–4 (from `2ε ≥ \|y\| + \|e\|`, `(s-y)² ≤ (s²+2ε)(1-T21)` and `√(λx) ≥ Δ - y` follows `ε ≥ δ(λ)`); Gibbs preservation with the output populations of `Φ(ψ₀)` forces `T01 = 0`, `T02 = 1`, `T20 = λ`; the scalar facts of the lemma (`λ f(T20/λ) = λ - √(λ(λ-T20))`, `f(z) ≤ z f'(z)`, equality at `T20 = λ(1-a²)`); `u ≤ c√(2δ)` gives `δ ≥ u²/(2c²)` | Proposition "A Gibbs-preserving process that is not free in real time", Lemma "Coherence and transfer", Appendix "A single input" |
| `lean/FullReset.lean` | `h(y) - c y ≤ log(1 + e^{-c})` on `[0,1]`, with equality at `y = 1/(1 + e^c)`; hence the real-time rate of a partial reset equals the full-reset cost once `p ≥ 1/(1 + e^{βΔ})` | Section 4, "Reset and partial reset" |
| `lean/Constants.lean` | The formation reservoir (equal Gibbs weight on every level, swapped subspaces of equal dimension); the converter inequality `(1-θ) e^{βs} > 1`; the purified-distance bound `≤ 4δ/r ≤ 1/16` of the lemma in "From the event G to all three projections"; the assembly step `C√(n(13 + 4an)) + 2an ≤ C√(13n) + nδ'/4` for `a = min{δ'/16, δ'²/(256C²)}`; `1 - 2 log₂(δ p) = 13 + 4 log₂(1/p)` at `δ = p/64` | Appendices "The construction" and "The fixed-error converse" |

Every theorem is audited with `#print axioms` and may use only `propext`, `Classical.choice` and `Quot.sound`.

## Exact and numerical computations (Python)

| Script | What is checked | Manuscript |
|---|---|---|
| `check_reset.py` | amplitude damping: Kraus form, complement (damping with `1 - p`, invertible exactly for `p > 0`, symbolic), the natural dilation, energy conservation and entanglement with the environment; `S(Φ^c(ρ)) ≤ h(px)` with equality on diagonal inputs; `T_rt > T_cap` for `0 < p < 1` at every temperature tested, with gap at least `I(O:E)`, equality at `p = 1`; diagonal inputs attain the batch maximum; the full-reset optimum (sympy), saturation for `p ≥ 1/(1 + e^{βΔ})`, Figure 2; 0.585 and 0.154; Table 2 (the finite-device table) by exact integer tails (upper tail, failure probability, qubit counts); the family `R = n²` at `n = 1000` (exact error below `n^{-2}`) and its `O(√ln n)` excess up to `n = 10^6` | Theorem 2(b), Figure 2, "A finite example", Table 2 (finite device) |
| `check_finite_saving.py` | `‖(Φ^c)^{-1}‖_⋄ = 3` (exact certificate, witness and SDP); the real-time bound 132.1094956 at 234 uses and 144.530049 at 256 uses with two engines (certified rationals and 60-digit mpmath); the batch integers 137, 5, 132 and 150, 11, 139; error below `8.71·10^{-9}`; saving above `5.5Δ`; the one-use structure behind the decoder (`Tr_M[(I⊗γ)P1] = diag(5/6, 1/3)`) and the Hayashi–Nagaoka inequality | "A finite saving", Appendix "Invertible environments" |
| `check_werner.py` | exact identities for `V`, `W`, the Choi state and `W^{-1}`; `‖W^{-1}‖_⋄ ≤ 9` (SDP value 5); the exact device adds `log₂ 3` per round and triples its rank; the support test on 600 perturbed rounds (gentle measurement, the `20√δ` bound and `S(QO\|F) ≥ log₂3 - g_9(min{1, 10√δ})`); convexity behind the averaged form; the thresholds `2·10^{-4}` and `10^{-6}`; `n log₂ 3 - O(log n)` at error `n^{-2}`; `6 log₂ n + O(1)` in batch | Theorem 3, Section 5, Appendix "The Werner–Holevo support test", Section 8 |
| `check_extreme.py` | Choi's criterion (Werner–Holevo, damping for `p ≠ 0`, tensor powers); mixed-bath exact dilations raise the device entropy by exactly `S(Φ^c(ρ))`, and fail to for a non-extreme channel; `a_β = T_rt` for damping and Werner–Holevo; entangled inputs give no more on two uses | Proposition "At zero error, waiting saves nothing for extreme channels", Appendix "Zero error and extreme channels" |
| `check_law.py` | `S(QO\|F) ≥ S(Q) - S(O)` and the accumulation identity on real-time rounds; the dilation entropy identity; the accounting identity on random energy-conserving two-round implementations; the energy correction and continuity bounds; the flagged direct sum, concavity and `\|f - S(ρ)\| ≤ log d`; `A(0)`, `A(t) ≥ 0`, `A'(0)`; the register similarity; the formation reservoir; the converter; the net work and its `O(n^{-1/4})` overhead; the informationally complete test and the instrument; `Σ_{k≤2γn} C(n,k) L^k ≤ 2^{nθ_γ}`; the battery remark; the constants of the cap, of the purified-distance lemma and of the assembly | Sections 2–3, Appendices "The construction" and "The fixed-error converse" |
| `check_invertible.py` | the Alicki–Fannes–Winter bound on 3000 pairs; the reference-vector bound; exact rounds of damping have `S(QO\|F) = S(Φ^c(ρ))`; on 600 perturbed rounds, the trace-distance bound `t(ε)` and the robust bound of Lemma "Invertible environment" | Lemma "Invertible environment", Appendix "Invertible environments" |
| `check_classical.py` | Lemma "Coherence is free"; Lemma "A nearly flat bath" in exact rationals; the seed construction (at most `d²` values, exact law), fibres of size at most `d³`, the ranking permutation, `f_U(p) = H(p) - H(Pp) + I(Y:B')` and the bound on `I(Y:B')`; diagonal inputs suffice; the attainment remark (Birkhoff, deterministic channels, full-rank optimum); on a coherent input the correlation term can be positive (complete dephasing at `(I + 0.6X)/2`: `m_rho = 1 - h2(0.8)` for every exact dilation) | Theorem 2(a), Appendix "Classical channels" |
| `check_free.py` | the relative-entropy form of `T_cap`; thermal operations have `f + e_H = -D(Γ(ρ)‖γ_B) ≤ 0`; the Gibbs-defect identity, zero for thermal operations; the square-root distance bound; the commutator bound and the mixing step; the `C_z` inequality; exact twirling and invariance of the defect; the rounding, the separation probability, Dirichlet's theorem, the lattice isometries and the exponent bookkeeping of the replacement theorem | Theorem "What is free in real time", Section 6, Appendix "What is free in real time" |
| `check_qutrit.py` | the channel is covariant and Gibbs-preserving (symbolic) with `T_cap = 0`; 300 random exact dilations obey `G_Dil ≥ g₁ log₂ 1/(1-g₂)`; Lemma "Coherence and transfer" on 1500 thermal operations, with the mode identities and the attaining oscillator; the population argument; the least error compatible with Steps 1–4 is at least `δ(λ)` (within 4%); `δ(λ)` on 600 thermal operations; the asymptotics `λ/32` and `(1-λ)²/2`; the crossover near `λ = 0.97`; 0.064 and `5.9·10^{-3}`; partial swaps at `0.10λ` and `(1-λ)/2`, and a numerical search that finds nothing closer | Proposition "A Gibbs-preserving process that is not free in real time", Lemma "Coherence and transfer", Appendix "What is free in real time", Section 8 |
| `check_clock.py` | no-broadcasting by SDP; the Choi bound and its triangle step; the Hadamard sectors; the stationary-battery counterexample (exact energy conservation, `π/(√2(L+1))` per use, adaptive simulations); the rare-excitation primitive on 300 instances (unitarity, payload, diamond distance by SDP, energy identity, record); the lift and its partial-trace identity; the Hadamard numbers (`w`, `b`, the sine-packet moment, `δ_n`, the error, `M ≥ n²b`); the tangent inequality and the work identity of "Every channel"; the bath-range ingredients; the X-dephasing capacity below `E/2` | Proposition "A returning clock", Theorem "A clock that returns approximately", Appendix "A clock that returns approximately", Section 1 |
| `check_fixeddim.py` | the formal Gram transfer in exact arithmetic over `Q(i, √2)` (eight answers, rational PVMs) and in floating point for `N = 2`; the null vectors; the converse algebra; the exact filters and the principal-minor test; Schur channels and padding; the thermal realization; the cyclotomic formulas | Theorem "Undecidability", Theorem "Fixed dimension, finite-list non-enumerability", Appendix "Exact inputs and the fixed-dimension reduction" |
| `check_repeatable.py` | repeatable channels outside the mixtures of unitaries: for the six-level Schur channel of Haagerup and Musat (their Example 3.3, matrix `B` with `β = 1/√5`) and for the qubit example with `u = X, Y, Z, (X+Y)/√2, (X+Z)/√2, (Y+Z)/√2`, in exact arithmetic, the matrix is a rank-3 real Gram matrix, `U = Σ_i |i⟩⟨i| ⊗ u_i` with one qubit of memory in `I/2` implements the channel and returns the memory to `I/2` on every input; neither channel is a mixture of unitaries (the criterion of Haagerup and Musat, Cor. 2.5(b), and, for the qubit example, the absence of a phase vector in the range of `M`); three uses of one device without reset give the right channel at every use, including on entangled inputs; two uses on uniform superpositions give a joint output at trace distance `5/9 ≈ 0.56` (Example 3.3) and `0.5233` (qubit example, entry `1/36` at `\|11⟩⟨22\|`) from two independent uses; control: a non-tracial memory state breaks repeatability | Section 12, "Repeated use with memory"; Appendix G, "Relation to prior work" |
| `check_lean.py` | compiles the Lean files and audits their axioms | — |

## What is not checked by machine

The real-time work law (Theorem 1) as a whole is proved in the manuscript: the minimax lemma, the typicality estimates
used to form the baths, and the error and failure bookkeeping of Appendix "The construction" are checked only in their
algebraic steps. In the fixed-error converse, the entropy accumulation theorem is quoted and the Gibbs-weighted cap
lemma is proved in the text; only its constants are checked. The hard direction of Theorem "What is free in real time"
(the robust form of the criterion of Lie et al. and the replacement theorem) is checked only through its ingredient
inequalities and exponents. For Theorem "A clock that returns approximately", the finite-source module of the companion
paper on processes, the derivative bounds of the Hadamard construction, the controller's entropy change
`O(n^{-6} log n)` and the step `T(σ_a, σ_b) ≤ 2√(2ε)` of the bath-range bound are not checked. The undecidability
statements rest on the theorems of Fu, Miller and Slofstra, of Kim, Paulsen and Schafhauser, of Musat and Rørdam and
of Musat; only the finite parts of the reduction are checked. General statements about all extreme channels, all
invertible complements and all classical channels are tested on the examples of the paper and on random instances;
the approximate arguments (continuity of Stinespring dilations and the Pinsker estimate `G ≥ (2/ln 2)[u - c√(2δ)]₊²`
for the qutrit channel, and the compactness step of Appendix "Zero error and extreme channels") are checked only in
their limits and final algebra.
The energy-bank example of Section 2, the two impossibility claims of Appendix "Classical channels" (no finite dilation
attains the cost of the channel with `P(0|1) = a`; no single dilation serves every input of the channel with
`P(1|1) = 1/2`), and the elementary remarks on mean work are not checked. The numerical search of `check_qutrit.py` is
a finite search: it supports the remark that partial swaps are the closest thermal operations found, and proves
nothing about the exact distance. Results quoted from the companion papers are checked in their own repositories.

## Lean setup

The proofs build with Lean 4.30.0 and Mathlib v4.30.0. Either point `MATHLIB_DIR` at a Mathlib v4.30.0 checkout whose
cache has been fetched (`lake exe cache get`), or fetch Mathlib into this folder:

    cd verification/lean
    lake exe cache get
    lake build

`check_lean.py` then compiles each file with `lake env lean` and checks the axiom report.
