# The thermodynamics of deadlines: one law for the work cost of acting in time

Seth Douglas and Nidhal Mghirbi — October 2026.

[Read the manuscript](paper/main.pdf) · [TeX source](paper/main.tex) ·
[Machine checks](verification/README.md)

Version 1.0.0, October 2026. DOI: [10.5281/zenodo.23719180](https://doi.org/10.5281/zenodo.23719180) (concept DOI, all versions: [10.5281/zenodo.23719179](https://doi.org/10.5281/zenodo.23719179)).

A quantum channel says what happens to each input, not when inputs arrive, when outputs leave for good, or what must
be handed back. We show that for every finite schedule in which each carrier returns with its Hamiltonian and the
controller comes back, the optimal work per use at vanishing error is the least entropy one implementation must add to
its own record, plus the energy it hands over, against the most demanding observer. Landauer's bound, the
thermodynamic capacity of Faist, Berta and Brandão in the time-covariant case, and the real-time costs of channels and
processes are this law on different schedules. The cost survives arbitrarily slow operation: order, not speed, sets
it. Releasing each output of a repeated memoryless channel before the next input arrives costs nothing extra for
classical channels, a positive amount for partial reset at every temperature, and k_B T ln 3 per use for the
Werner–Holevo qutrit at zero Hamiltonian, which is essentially free in batch. For a classical task with zero
Hamiltonians that releases a past and later answers a question about it, the real-time and held prices are logarithms
of two fiber counts; for reversible questions they differ by the logarithm of the number of classes of pasts that
later questions tell apart. With a returned clock, the batch cost of every channel is a single-letter quantity, equal
to the capacity when the environment can carry the channel's energy change; otherwise the clock's spread must grow at
least linearly with the number of uses. Freeness is decidable in batch for exact algebraic data and undecidable in
real time, already in a fixed dimension. A two-qubit process that is free when held costs every early-release device
at least 0.87 k_B T ln 2 per episode at one percent error and budgets of 0.025 k_B T ln 2; for a classical version we
propose a three-arm feedback-trap protocol.

All rates are optimal asymptotic work rates at vanishing error over the complete interaction, with hardware allowed to
grow. The constructions show what is possible in principle, with large capital and reservoirs; they are not efficient
engines. The lower bounds hold for every device.

The manuscript has a main text of 42 pages and Appendices A–K with complete proofs, except for two results imported from our earlier preprints (Lemma G.6, and the zero-Hamiltonian closure theorem used in the undecidability proof); Appendix K gives, for every result
taken from the companion papers, its number there. The manuscript is the authority for exact statements and
hypotheses; its Section 14 and [verification/README.md](verification/README.md) list what is checked by machine, what
is proved in Lean, and what is proved only in the text.

## The companion papers

Most of the results first appeared in four papers, each with its own repository, which this paper brings together.
A short letter summarizes them.

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

## Build

Requires a TeX distribution (TeX Live or MiKTeX) with `pdflatex`, BibTeX and the `urlbst` bibliography styles.
From the repository root, run

    python paper/build.py

The build starts from scratch and stops on any undefined reference or citation, duplicate label, overfull box, float
too large for the page or BibTeX warning. The PDF date is fixed, so two builds with the same TeX installation give the
same file.

The title is defined once, in `paper/sections/title.tex`; `python tools/sync_title.py` copies it into this README,
`CITATION.cff`, `.zenodo.json` and the verification notes (`--check` only compares, `--github` also sets the
repository description). The abstract is defined once, in `paper/sections/00_front.tex`; `python tools/sync_abstract.py`
copies it into this README, `CITATION.cff` and `.zenodo.json`, writing k_B T in plain text and in HTML, and
`--check` only compares the normalized texts and checks that each is within arXiv's 1920 characters.

## Verify

Requires Python 3.10 or later with the packages in [verification/requirements.txt](verification/requirements.txt),
and, for the formal proofs, Lean 4.30.0 with Mathlib v4.30.0.

    python -m pip install -r verification/requirements.txt
    cd verification
    python verify.py              # every Python check; writes SCORECARD.md
    python verify.py --negative   # deliberate corruptions, each of which must be caught
    python verify.py --lean       # also compiles the Lean proofs

[verification/README.md](verification/README.md) explains what a passing check establishes and what it does not.

## How this work was done

The authors developed this work with AI models from more than one developer and take responsibility for every
claim. The section "How this work was done", at the end of the main text, describes how the work was done and what
the machine checks cover.

## License and citation

The manuscript and repository content are available under **CC BY 4.0**. The software and machine-readable
verification artifacts are additionally available under the **MIT License**, at your option; see
[RIGHTS.md](RIGHTS.md) for the scope. [CITATION.cff](CITATION.cff) provides machine-readable citation metadata.
