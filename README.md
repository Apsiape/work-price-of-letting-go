# The thermodynamics of deadlines: one law for the work cost of acting in time

Seth Douglas and Nidhal Mghirbi — November 2026.

[Read the manuscript](paper/main.pdf) · [TeX source](paper/main.tex) ·
[Machine checks](verification/README.md)

Version 1.1.0, November 2026. Concept record: [10.5281/zenodo.23719179](https://doi.org/10.5281/zenodo.23719179). Incorporates The heat price of precision ([10.5281/zenodo.23701732](https://doi.org/10.5281/zenodo.23701732)).

A quantum channel specifies what happens, but the work cost also depends on when inputs arrive, outputs leave and hardware must return. For every finite schedule in which carriers return with their Hamiltonians and the controller comes back, we prove that the optimal asymptotic work rate is the least record entropy plus transferred energy against the most demanding observer. Landauer erasure, thermodynamic capacity and the costs of real-time channels and processes are this law on different schedules. For each positive limit-computable ($\Delta^0_2$) real $\alpha$, a fixed finite nonlocal game has bounded joint-reset work and local-reset work $2\alpha\log_2(1/\varepsilon)+o(\log(1/\varepsilon))$ in units of $k_BT\ln2$, with hardware allowed to grow as precision improves. The precision-reset bounds are proved directly under a separate contract. Thus a reset deadline can force an uncomputable logarithmic cost coefficient, related to Kolchinsky and Wolpert's noncomputable Turing-machine heat functions. We prove the reset sandwich, the quantum/classical recovery tradeoff, a paired heat gap, the four-unit magic-square floor, and exact sector-allocation and access-obstruction results, using explicitly cited game-demand inputs. Early release adds no cost for classical memoryless channels, but has a quantum surcharge; tasks with memory have a fiber-count price. A returned clock has a single-letter batch cost and a separate size requirement. Freeness is decidable in batch and undecidable in real time, already in fixed dimension. Proofs, finite checks and a two-qubit work certificate connect these results to a proposed three-arm experiment. Lean certifies the schedule law for finite-dilation targets, including its physical compiler. The costs survive arbitrarily slow operation: the order of access and reset sets the price.

All rates are optimal asymptotic work rates at vanishing error over the complete interaction, with hardware allowed to
grow. The constructions show what is possible in principle, with large capital and reservoirs; they are not efficient
engines. The lower bounds hold for every device.

The schedule-law proofs in Appendices A–H use two results from our earlier preprints without reproof: Lemma G.6 and [Memory, Theorem 3.2(a)], the zero-Hamiltonian closure theorem used in the undecidability proof. Every reset argument is proved here. The separate game-demand inputs are Theorem 1.1 of The uncomputable price of precision v3.0.0 (Corollary 8.1), and Theorem 11.9 and Corollary 11.11 of The price of precision (Corollary L.2 and Proposition L.9); Appendix K gives, for every result
taken from the companion papers, its number there. The manuscript is the authority for exact statements and
hypotheses; its Section 14 and [verification/README.md](verification/README.md) list what is checked by machine, what
is proved in Lean, and what is proved only in the text.

## Related papers and source attribution

The schedule and reset arguments form one paper with complete proofs under their stated contracts. The following sources provide related results and source attribution; the time-order letter summarizes the schedule results; the reset question is a further application of the same access principle.

| Paper | DOI | Repository |
|---|---|---|
| The price of time order | [10.5281/zenodo.23310622](https://doi.org/10.5281/zenodo.23310622) | [Apsiape/price-of-time-order](https://github.com/Apsiape/price-of-time-order) |
| Only quantum channels save work by waiting* | [10.5281/zenodo.23310624](https://doi.org/10.5281/zenodo.23310624) | [Apsiape/save-work-by-waiting](https://github.com/Apsiape/save-work-by-waiting) |
| The work cost of answering in real time | [10.5281/zenodo.23310628](https://doi.org/10.5281/zenodo.23310628) | [Apsiape/answering-in-real-time](https://github.com/Apsiape/answering-in-real-time) |
| The price of keeping time | [10.5281/zenodo.23310632](https://doi.org/10.5281/zenodo.23310632) | [Apsiape/price-of-keeping-time](https://github.com/Apsiape/price-of-keeping-time) |
| Letter: Order, not speed: the work price of letting go | [10.5281/zenodo.23323808](https://doi.org/10.5281/zenodo.23323808) | [Apsiape/order-not-speed](https://github.com/Apsiape/order-not-speed) |

The manuscript cites version 1.0.2 of the first three papers (10.5281/zenodo.23323043 to 23323045) and version
1.1.0 of The price of keeping time (10.5281/zenodo.23325723); the concept DOIs above always resolve to the latest
version.

\*The title concerns repeated uses of one memoryless channel; classical tasks with memory can pay for early release,
as the task of Figure 1 of the manuscript does.

The reset proofs and examples are in Appendices L–O. The games and matched exponents are the input of Theorem 1.1 of [The uncomputable price of precision](https://doi.org/10.5281/zenodo.23736188); the underlying resource and game papers are [The price of precision](https://doi.org/10.5281/zenodo.23697346) and [the companion game paper](https://doi.org/10.5281/zenodo.23697255). The precision cost coefficient can be uncomputable; related noncomputable heat functions were studied by [Kolchinsky and Wolpert](https://doi.org/10.1103/PhysRevResearch.2.033312). This statement concerns a limiting coefficient.

## Build

Requires a TeX distribution (TeX Live or MiKTeX) with `pdflatex`, BibTeX and the `urlbst` bibliography styles.
From the repository root, run

    python paper/build.py

The build starts from scratch and stops on any undefined reference or citation, duplicate label, overfull box, float
too large for the page or BibTeX warning. The PDF date is fixed, so two builds with the same TeX installation give the
same file.

The title is defined once, in `paper/sections/title.tex`; `python tools/sync_title.py` copies it into this README,
`CITATION.cff`, `.zenodo.json` and the verification notes (`--check` only compares, `--github` also sets the
repository description). The abstract is defined once in `paper/sections/00_front.tex`; `python tools/sync_abstract.py` copies its exact text into this README, `CITATION.cff`, `.zenodo.json` and `paper/abstract-arxiv.txt`. `--check` requires literal equality on all five surfaces and the 1920-character limit.

## Verify

Requires Python 3.10 or later with the packages in [verification/requirements.txt](verification/requirements.txt),
and, for the formal proofs, Lean 4.30.0 with Mathlib v4.30.0.

    python -m pip install -r verification/requirements.txt
    cd verification
    python verify.py              # every Python check; writes SCORECARD.md
    python verify.py --negative   # deliberate corruptions, each of which must be caught
    python verify.py --lean       # also compiles the older finite Lean proofs

[verification/README.md](verification/README.md) explains what a passing check establishes and what it does not.

## Formal verification

The selected development in [verification/lean/](verification/lean/) certifies
`ScheduleLaw.Blueprint.work_law_for_schedules`, proving both `WorkLaw` (universal
lower bound, equality and attainment) and `WorkLawBits`. It includes the
`pointwise_physical_compiler`, `corrected_joint_tangent`,
`finite_factory_of_small_residue_coding`, `source_factory_circuits`,
`cyclic_cache_protocol` and `finite_conserving_phase` roots in the same namespace.
The 359 selected owned modules have no admissions; the exported closure uses
only `propext`, `Classical.choice` and `Quot.sound`.

The pins are Lean 4.30.0 (`d024af099ca4bf2c86f649261ebf59565dc8c622`),
Mathlib v4.30.0 (`c5ea00351c28e24afc9f0f84379aa41082b1188f`) and the selected
Physlib sources (`f5242c99d796b59a390d26cd7d1a8057e04c46b5`). The same
lean4export NDJSON 3.1.0 export was accepted by Lean 4.30 `Environment.replay`
in a fresh empty environment and independently by Rust nanoda, with the three
standard axioms whitelisted. Runtime exporter/parser sources are compiled
against 4.30, outside the proof graph. Package instructions identify exact
source, dependency, tool and export hashes. A fresh replay from this package
rebuilt all 58 vendored and 359 owned modules, and both kernels accepted its new
export (SHA-256 `FFE939E88D712B6C5AA6E4E5DB21B68BAF1AAB16821A15423D4E7DF058753963`); the record is
[verification/lean-clean-replay.json](verification/lean-clean-replay.json). That file is the
package summary and replay evidence the package README refers to; it records the
manifest's own SHA-256, `BD876A72A57DBCCAD7D232022239BF2B1369CD8CCA52FCF70EE01467E3FA4617`.

The formal targets are finite unitary dilations; equivalence to every abstract
finite strategy is not proved in this graph. The definitions impose the paper's
same-carrier, same-Hamiltonian, independent-initial-state and universal-observer
contract, whole-controller/all-rest return, separate energy/entropy refunds,
and the battery entropy, failure and absolute-tail budgets. Lean indexes blocks
by n+1 and supplies the explicit nats-to-bits normalization. The current Lemma
3.4 is the whole-block identity; the joint tangent is in Appendix A and chooses
q separately for each smoothing parameter, as does the certified statement.

This certificate does not cover Theorems 4.1–4.4, 6.1 or 7.1 as complete statements,
Corollary 8.1, heat/reset Appendices L–O, imported game-demand or smoothing/closure
theorems, experimental claims, efficient implementation, or anything outside
the selected graph. Older finite Lean checks are separate.

## How this work was done

The authors developed this work with AI models from more than one developer and take responsibility for every
claim. The section "How this work was done", at the end of the main text, describes how the work was done and what
the machine checks cover.

## License and citation

The manuscript and repository content are available under **CC BY 4.0**. The software and machine-readable
verification artifacts are additionally available under the **MIT License**, at your option; see
[RIGHTS.md](RIGHTS.md) for the scope. [CITATION.cff](CITATION.cff) provides machine-readable citation metadata.

The public source tree excludes `paper/build/**`. The manuscript is `paper/main.pdf`; the standalone TeX upload is `paper/arxiv/`.
