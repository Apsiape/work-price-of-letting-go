# Verification package for *The thermodynamics of deadlines: one law for the work cost of acting in time*

This folder lets anyone, including a referee who does not read Python, confirm the finite
identities that the paper's Table 7 lists and the numbers quoted in its Sections 3 to 11, and see
which statements are formally proved, which are machine-checked, which are proved in the text
only, which are imported from the literature, and which are used from our earlier preprints. The manuscript is the authority for exact statements; the paper's Section 14
(Verification status) is the map from statements to the rows below.

## Three commands

```sh
python -m pip install -r requirements.txt        # numpy, scipy, sympy, mpmath, cvxpy
python verify.py --quick                         # about 4 minutes: every check that runs in under a minute
python verify.py                                 # about 20 minutes: every Python check; writes SCORECARD.md
python verify.py --negative                      # the negative controls: each corruption must be CAUGHT
```

`verify.py` prints one line per check and writes `SCORECARD.md`, a table with one row per script:
PASS or FAIL, the claim the script checks, the script, the part of the paper it belongs to, and its
running time. Table 7 of the paper names the scripts against its statements; its rows whose only
classes are Text, External or Earlier preprint have no script. The exit status is 0 only if every selected check passed. A pre-generated
`SCORECARD.md` from the authors' run is included; delete it and regenerate it to be sure.

Tested with Python 3.10–3.13. Checks that use `cvxpy` print a solver notice on stderr; that is
not an error. Two checks (`parts/channels/check_qutrit.py`, `parts/channels/check_reset.py`)
take three to four minutes each.

## What a PASS means, and what it does not

* **Exact computations** (rational arithmetic, integer identities, finite-field ranks) establish the
  identity they test for all parameters they enumerate. Example: `checks/check_classes.py`
  enumerates every task y + f(x) mod 3 on three bits (all 3^8 functions f) and reports the largest
  violation of submodularity, log2(3/2), as the paper's Proposition I.9 states.
* **Numerical computations** check closed-form identities typically to 1e-9 or better, quantities
  obtained by optimization, grid search or semidefinite programming to the accuracy of that method,
  as coarse as 1e-3, and inequalities on hundreds of
  random or deliberately perturbed instances. They check the instances they run, not the general
  statement. Example: `checks/check_identity.py` verifies the whole-block identity of Lemma 3.4 on
  random energy-conserving devices, for one step and for two-visit schedules with an adaptive
  observer, checks global purity with a mixed device and its purifier, and confirms that it fails for a non-conserving unitary, and
  `checks/check_fiber.py` evaluates the robust lower bound of Lemma I.7 on devices whose gates have
  been deliberately perturbed, using only the observers that the proof itself uses.
* **Formal proofs** (`parts/*/lean/`) are complete Lean 4 proofs of the lemmas named in the paper's
  Table 7; each file is audited with `#print axioms` and uses only `propext`,
  `Classical.choice` and `Quot.sound`. They need Lean 4.30.0 and Mathlib v4.30.0:

  ```sh
  cd parts/law/lean && lake exe cache get && lake build      # and likewise for module, channels, batch
  python verify.py --lean
  ```

* **Not checked by machine**: the attainability half of the schedule law (Appendix A), the physical
  module (Appendix F), the general accounting arguments, and the robust release lemma are proved in
  the manuscript only. The pointwise smoothing lemma (Lemma G.6) and the zero-Hamiltonian closure theorem used in
  Step 1 of the undecidability proof are used from our earlier preprints (class Earlier preprint in
  the paper's Table 7).
  The pretty-good-measurement bound used in Lemma I.7 is cited (Barnum and Knill 2002) and
  tested numerically on random ensembles in `checks/check_fiber.py`.
  The undecidability theorem combines arguments in the manuscript with cited results of Fu, Miller
  and Slofstra, Kim, Paulsen and Schafhauser, and Musat and Rørdam; only its exact filters are
  checked here.
  The order prices of the crossing pair in Section 11, one ebit for the BB84 task and the coherence
  lower bound for the CNOT process (Appendix C), are proved in the manuscript only;
  `parts/law/check_beyond_thermo.py` enters them as constants and checks the CNOT process itself:
  its identity, its one-way protocol without entanglement and its one-|+> circuit.

## If a check reports BLOCKED

A row marked **BLOCKED** means the script could not import a dependency (most often `cvxpy`, used by
the semidefinite programs in `parts/batch/` and some of `parts/module/`); it is not a mathematical
failure. Install `requirements.txt` and rerun that row with `python verify.py --select <path>`.
Rows that do not need `cvxpy` still run and report normally on a machine without it.

## Rebuilding the PDF

`python ../paper/build.py` fixes the PDF date and trailer identifier, so two builds with the
same TeX installation produce byte-identical files. Different TeX versions produce the same text and
numbering but not the same bytes.

## Negative controls

`python verify.py --negative` runs five deliberate corruptions and requires each to be caught:

| Corruption | Expected diagnostic |
|---|---|
| `checks/check_identity.py --perturb`: a generic (non-energy-conserving) unitary | the whole-block identity fails on every random device |
| `checks/check_classes.py --perturb`: the real-time price is replaced by the naive class count | the constant-answer and fiber prices fail |
| `checks/check_fiber.py --perturb`: the question carrier is not dephased, and the steering observer alone is taken to force the price | trace distance 1/2 from the target; a device that serves only the steering observer pays 0.918 < log2 3 bits |
| `checks/check_span_criterion.py --perturb`: "unbalanced implies strict excess" | fails on the Hadamard gate, where B equals the capacity |
| `checks/check_protocol_numbers.py --perturb`: the protocol bound 1 - h2(δ) replaced by 1 - δ, the embezzling distance by 1/n, and the graded-control cost h2(η) by 2η | all three must fail, or the control does not fire: the quoted 0.71 and 0.92, the trace distance computed from the vectors, and the quoted 0.081, 0.469 and 0.811 |

Several scripts in `parts/` also contain their own built-in controls (perturbed devices that must
violate a bound, batch devices on which a real-time bound must fail); see the docstring at the top
of each script.

## Layout

```
verify.py                 runner; writes SCORECARD.md (or SCORECARD-NEGATIVE.md)
requirements.txt          Python dependencies
checks/check_identity.py  Lemma 3.4 (whole-block identity): one step and two-visit schedules; global purity   [new]
checks/check_protocol_numbers.py  Section 10 protocol numbers, record-export, joint-record and blank examples, timing, graded control, held-arm camera frame, endpoint rule, confidence endpoints, fresh probes, per-stroke variance, flipped loan; Prop. 9.1(d) heat form with randomized settings; Figure 3; Section 5 Gibbs-qubit reset; Section 2 example   [new]
checks/check_classes.py   Theorem 7.1 prices, Proposition I.9, record transfer             [new]
checks/check_fiber.py     Lemmas I.1-I.8: dephasing, distinguishable records, information flow, robust bound   [new]
checks/check_span_criterion.py  Theorem 4.3: the span condition is sufficient, not necessary   [new]
parts/law/                Sections 5, 9, 11; Appendices B--E (certificate, release rank, release lemma, collision model)
parts/module/             Appendix F (processes with memory; the physical module)
parts/channels/           Appendix G (memoryless channels; free set; undecidability filters); Section 12 (repeatable channels)
parts/batch/              Appendix H (returned clock; batch law; clock size; time reverse; noise horizon)
parts/*/lean/             formal proofs (Lean 4 + Mathlib)
parts/*/qtools.py         shared numerical helpers used by that part's scripts
```

Each `parts/*/README.md` lists, script by script, what is checked and what the manuscript proves
only in text, with the theorem numbers of that part.

## Reading the scorecard without the code

Open `SCORECARD.md`. Every row is a script and the claim from the paper that it checks. If the row says PASS, the finite
content of that sentence was recomputed on this machine from scratch, deterministically, with the
random seeds fixed inside the scripts. If a row says FAIL, the script prints which sub-check failed
and the numbers it saw; that line is reproducible and is the right thing to quote in a report.
