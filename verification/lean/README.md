# Selected schedule-law certificate

This package contains exactly the frozen selected round-28 proof sources:
359 owned Lean modules and 58 selected Physlib dependency sources, with no
historical Challenge/admission graph, oleans, .lake directory or build products.
`selected-sources.json` binds every owned source to the successful round-28 audit.
`certification.json` describes that historical certificate; a clean release
replay is separate evidence in the release-preparation READY report.

The seven roots, all in `ScheduleLaw.Blueprint`, are:

- `work_law_for_schedules` (both `WorkLaw` and `WorkLawBits`)
- `pointwise_physical_compiler`
- `corrected_joint_tangent`
- `finite_factory_of_small_residue_coding`
- `source_factory_circuits`
- `cyclic_cache_protocol`
- `finite_conserving_phase`

The selected root closure has no admissions and uses only `propext`,
`Classical.choice` and `Quot.sound`. The source comment in Blueprint referring
to pending admissions is historical; source bytes are deliberately preserved.
The formal target is a finite unitary dilation. Equivalence with every abstract
finite strategy is not proved here. The current paper's Lemma 3.4 is the
whole-block identity; the joint tangent is in Appendix A. Both the printed
joint tangent and the frozen Lean theorem choose q separately for each s.

This certificate does not cover complete Theorems 4.1-4.4, 6.1 or 7.1,
Corollary 8.1, heat/reset Appendices L-O, imported game-demand or smoothing/
closure theorems, abstract finite-strategy dilation equivalence, experiments,
efficiency, or anything outside the selected graph. Older finite Lean checks
in the parent verification package are separate.

## Pins and manifest

Lean 4.30.0: `d024af099ca4bf2c86f649261ebf59565dc8c622`.
Mathlib v4.30.0: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
Physlib: `f5242c99d796b59a390d26cd7d1a8057e04c46b5` (selected, ported sources).
`dependency-pins.json` records all Mathlib transitive revisions, source and
configuration hashes, adaptation provenance and exact kernel-tool hashes.
The source notices and licences are retained. Historical local paths in frozen
proof sources/notices identify original provenance, not replay dependencies.

`MANIFEST.sha256` lists SHA-256 for every other package file, with relative paths.
The manifest cannot hash itself; its own SHA-256 is recorded in the external
release-preparation package summary. Verify it before replay. No file exceeds
50 MB. The 638 MB historical proof export is deliberately not shipped; replay
regenerates it in scratch. Native exporter/checker executables are built from
source in scratch because they exceed 50 MB.

## Clean replay (Windows x64)

Requirements: Python 3.10+ with `psutil`; the pinned Lean installation including
`leanc`; and a separately provisioned Mathlib v4.30.0 checkout with its pinned
compiled dependency cache. No git or network commands are run by this package.
The Mathlib checkout is read-only during replay; its manifest, lakefile and
toolchain must match the packaged pins. A clean replay rebuilds **all** 58
packaged vendor modules and all 359 owned modules, and never reads historical
project oleans. Provisioning Mathlib itself is a separate prerequisite; this
runner is not a clean rebuild of Mathlib or the Lean compiler.

Run, substituting paths to those dependencies and an empty scratch directory:

```text
python -B replay.py --mathlib MATHLIB_PATH --lean-root LEAN_430_ROOT --work-dir EMPTY_SCRATCH_PATH
```

Scratch must lie outside this package. The runner copies the packaged source
tree there and writes all generated files only in scratch. It compiles sources
in dependency order with `LEAN_NUM_THREADS=1`, `-j1`, `-M6144`; monitors the
subprocess tree against a 10 GiB RSS cap. With `--wait-for-other-lean` it also
waits for other Lean/lake processes before each stage and stops its own stage
if one starts; it never stops other jobs. Other Lean builds compete for memory,
so avoid running them at the same time. `--resume` reuses only successful receipts
with matching source and object hashes after a stopped attempt.

After source compilation, the runner compiles and links the supplied exporter
and Lean checker against **Lean 4.30 only**. The exporter/parser are byte-identical
source ports from the companion Lean FRO distribution and are outside the proof
import graph. Generated Windows executables receive only a 128 MiB PE stack
reserve adjustment, matching round 28. The supplied Rust nanoda binary is the
hash-pinned independent checker with that same stack-only adjustment.

The runner exports `Round28Audit`'s seven roots plus the required primitive
closure as lean4export NDJSON format 3.1.0. It runs Lean 4.30's actual
`Environment.replay` in a fresh empty environment, checks exact standard-axiom
signatures, rejects unsafe/partial constants and checks regenerated quotient
constants. It then runs Rust nanoda with one thread and hard rejection of all
axioms except the three named above, on the identical export. Export hashes
are checked unchanged after each replay. Source and core runtime hashes are
guarded as well. `clean-replay.json` is written only after both kernels pass;
`receipts.json` has stage wall times and peak tree RSS. `stopped.json` records an
interruption or failure and is not a successful certificate.

Inspect `logs/owned_Round28Audit.log` for the freshly compiled axiom audit.
The historical round-28 export accepted 73,310 constants and has SHA-256
`FCCCCD6EA210475EA11C599E3A0A0F982215EF998B5360C7F73EB09DC4FA5B94`.
A fresh compiler/tool build may produce different bytes; both kernels must
accept its same unchanged export, independently of that historical digest.
