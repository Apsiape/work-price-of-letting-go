# Machine checks

`python verification/run_all.py` runs every check below and exits with status 0 only if all pass. The Python checks
need the packages in `requirements.txt`; `check_lean.py` needs Lean 4.30.0 and Mathlib v4.30.0 (see the end of this
file). Each script prints what it verifies.

The manuscript is the authority for the statements and their proofs. The checks fall into two kinds. **Formal
proofs** in Lean are complete proofs of the stated lemmas for all parameters. **Exact and numerical computations**
in Python establish some identities in exact rational arithmetic and check others numerically to a tolerance of 1e-10 or better, recompute the numbers quoted in the text (apart from those listed below as not checked),
and test inequalities on many random or perturbed instances; a computation of this second kind checks the instances it
runs, not the general statement.

## Formal proofs (Lean 4 with Mathlib)

| File | What is proved | Manuscript |
|---|---|---|
| `lean/ReleaseRank.lean` | For every code over any field: `rank F_L + dim C(R) = rank F`; holding `m` coordinates lowers the cost exactly when the code has a nonzero word of weight at most `m`; some `m` held coordinates carry a subcode of dimension at least `d` exactly when some such subcode has support of size at most `m` (the generalized-Hamming-weight form); monotonicity of the binary entropy on `[0, 1/2]` used by the classical witness | Proposition "Release rank" (b), Appendix "Release rank" |
| `lean/Reset.lean` | For all `K ≥ 1` and `J`: the shell-stock reset conserves energy, returns the memory to 0, maps valid columns to valid states, is injective, and meets the initialized columns only in fixed points, so its completion is a full energy-conserving permutation | Appendix "Release rank", construction |
| `lean/Certificate.lean` | The stabilizer formula `4Π = 1 + XX + ZZZ − ZYY`; `Π` is a projector; the two-setting bound `1 − Π ≤ (1 − XX)/2 + (1 − ZZZ)/2` as a positive-semidefinite statement; the decoder identity `V W\|b⟩ = \|b⟩\|Φ+⟩` | Appendix "The two-qubit certificate" |

Every theorem is audited with `#print axioms` and may use only `propext`, `Classical.choice` and `Quot.sound`.

## Exact and numerical computations (Python)

| Script | What is checked | Manuscript |
|---|---|---|
| `check_certificate.py` | the process sends `\|ab⟩` to Bell states with first marginal `I/2`; the held circuit and an explicit early-release circuit implement it exactly; the early-release circuit raises the device entropy by exactly one bit on the probe; the lower bound `ΔS_D ≥ 1 − h2(e) − e log2 3` on 300 perturbed early-release devices, and its failure in batch; `H4(p) ≤ h2(e) + e log2 3`; the leakage estimator with randomized hidden settings is unbiased, and its 150,000-episode Hoeffding-Azuma bound; every number quoted (0.962, 0.878, 0.348, the 0.17 threshold, the finite-sample heat bound 0.433 and 0.429, 346 mK, 1.4e-24 J) | Section 8, Appendix "The two-qubit certificate", Appendix "Coherence and thermodynamic numbers" |
| `check_release_rank.py` | the compiler is exact on every input and stores `rank F_L` uniform bits; the rank identity and the generalized-Hamming-weight formula against brute-force enumeration of subcodes; the reset permutation, its heat `(1 − q) r` and battery entropy, for several `(r, J)`; the time-sharing witness has errors `e1`, `e2` and entropy increase exactly `1 − h2(e1 + e2)`, and clears its noise register while the first carrier is still held (`n ← n ⊕ A' ⊕ M` on every branch, before the release); `ΔS_D ≥ 1 − h2(δ)` on perturbed devices that respect the release order | Proposition "Release rank", Section 8, Appendix "Release rank" |
| `check_beyond_thermo.py` | the release-step identity; the release lemma, exactly for a Bell pair and its robust bound on 3000 noisy states; the coherence surcharge `1 − h2(sin²θ)` and 0.399; the CNOT process, its one-way protocol without entanglement and its early-release circuit; the rank of the order-price matrix and the crossing pair, with the order prices entered as constants from the manuscript (only 0.399 is recomputed; the one-ebit price of BB84 and the coherence lower bound of the CNOT process are proved in the text, not checked here); the delay law | Section 7, Appendix "Coherence and thermodynamic numbers", Section 4 |
| `check_rates.py` | amplitude damping: real-time optimum and `m = h2(1/3) = 0.918`; coherent inputs do not raise the batch rate; the X-dephasing capacity `β⁻¹ ln cosh(βE/2)`; the qutrit value `c = 0.15471030022` from its two equations and by direct maximization | Sections 4 and 5, Table 2 (schedules) |
| `check_speed_order.py` | the collision-model identity; `A_K ≥ l²/(2K)` for cooling strokes at every `K`, its failure outside that scope, and `A_K ≥ l²/(4K)` in every direction; a shared budget of `M` contacts costs `(L_B + L_O)²/(2M)`, the same as separate interfaces with the same total, so the term `L_B L_O / M` appears only against `2M` contacts; the order gap 0.431323 E; the intercept bias of a `1/K` fit; the slow divergence at fixed `K` | Section 8 |
| `check_lean.py` | compiles the Lean files and audits their axioms | — |

## What is not checked by machine

The work law for schedules (Theorem 1) and its constructions (Appendices A and B), the general accounting and
entropy arguments, the robust release lemma (its proof; the bound itself is tested above) and the monotonicity statement
("Order cannot be manufactured") of Section 7 are proved in the manuscript and are not formalized here. The worked
resource-theory examples of Section 7 support its formation-cost picture; the proposed general extension of that picture
is explicitly open and is not proved in the manuscript. The computability statements of Section 6 combine arguments in
the manuscript with results imported from the companion papers and the literature.
Results quoted from the companion papers are checked in their own repositories.

## Lean setup

The proofs build with Lean 4.30.0 and Mathlib v4.30.0. Either point `MATHLIB_DIR` at a Mathlib v4.30.0 checkout whose
cache has been fetched (`lake exe cache get`), or fetch Mathlib into this folder:

    cd verification/lean
    lake exe cache get
    lake build

`check_lean.py` then compiles each file with `lake env lean` and checks the axiom report.
