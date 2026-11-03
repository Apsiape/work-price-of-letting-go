# Changes in version 1.1.0

Version 1.1.0, November 2026.

- Incorporates *The heat price of precision*: the separate game-preparation and
  answer-release reset contract, local/joint reset sandwich, prescribed
  precision coefficient, quantum/classical recovery tradeoff, exact sectors,
  paired heat gap, magic-square floor, access obstructions, weighted observers,
  multiphase calibration and approximate-matching limitations in Appendices L-O.
  Earlier appearances and all game-demand inputs are explicitly attributed.
- Applies all 35 ranked items from the first audit round: clarifies the fixed
  game versus growing strategy hardware; separates reset and schedule contracts;
  corrects import and priority accounting, cited metadata, answer-port wording
  and bound-variable names; expands the scope tables, glossary and finite-check
  documentation; and isolates the standalone TeX upload. Existing mathematics
  and result numbering were preserved.
- Applies all four ranked items from the second audit round: physically removes
  `paper/build/**` from the release tree; replaces reader-facing review chronology
  with author roles, AI disclosure and verification scope; fixes the CFF
  preferred-citation title synchronizer for field-order independence; and removes
  the duplicate contract sentence after Corollary 8.1.
- Adds Muruga, Ginot, Loos and Bechinger, *The extraction of work from hidden
  degrees of freedom*, Nature Physics (published online 16 October 2026),
  DOI [10.1038/s41567-026-03442-w](https://doi.org/10.1038/s41567-026-03442-w).
  The discussion distinguishes their experimental use of environmental memory
  from this paper's complete controller-return contract. Bibliographic data
  were checked against the publisher's record.
- Adds a bounded formal-verification subsection, matching README descriptions
  and an abstract sentence. The frozen selected round-28 development certifies
  `ScheduleLaw.Blueprint.work_law_for_schedules` in both `WorkLaw` and
  `WorkLawBits`, including the physical compiler, corrected joint tangent and
  finite factory/cache/phase constructions. Its root closure has no admissions
  and uses only `propext`, `Classical.choice` and `Quot.sound`; identical exported
  proof bytes were accepted by Lean 4.30 `Environment.replay` and independent
  Rust nanoda in the original certification.
- Packages the selected source graph under `verification/lean/` with exact
  Lean 4.30.0, Mathlib v4.30.0 and dependency pins, licences, SHA-256 manifest,
  runtime checker sources and clean-replay instructions. Build artifacts and
  the large proof export are excluded. A fresh replay from this package rebuilt
  all 58 vendored and 359 owned modules, and both kernels accepted the new
  export; the record is `verification/lean-clean-replay.json`. The repository
  now stores every file byte for byte, so the package manifest verifies from a
  fresh clone.
- States the formal scope explicitly: finite-dilation targets; general abstract
  finite-strategy dilation equivalence is not proved in the selected graph.
  The current Lemma 3.4 is the whole-block identity; the joint tangent is Lemma
  A.8 and already has the certified `for each s, there exists q_s` order. No
  mathematical text change is required. Complete Theorems 4.1-4.4, 6.1 and 7.1,
  Corollary 8.1, heat/reset Appendices L-O, imported theorems, experiments and
  all other statements outside the selected graph are excluded from this
  certificate; older finite Lean checks remain separate.

The strict build now prioritizes its fresh bibliography output over the checked-in release copy and waits for undefined-reference reruns before checking the final log. This fixes stale citation resolution when a bibliography entry is added.

The existing theorem, definition, remark and proof environments, main law
section and full schedule-contract appendix are unchanged.
