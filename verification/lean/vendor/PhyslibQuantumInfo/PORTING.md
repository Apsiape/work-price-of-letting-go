# QuantumInfo from Physlib at the exact relay pin

Canonical dependency source: leanprover-community/physlib,
revision `f5242c99d796b59a390d26cd7d1a8057e04c46b5`.
This is the continuation of Timeroot/Lean-QuantumInfo, whose original
MIT revision `56e83a9288a3c616285038748e273b3c0e1a36bf` was inspected first.
The successor revision uses **exactly** Lean 4.30.0 and Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, matching this project.
No toolchain migration is needed.

The successor root LICENSE is Apache 2.0. All individual copyright and licence
headers are retained. The selected LiebConcavity.lean still has an MIT header;
its MIT permission text is retained separately as
LICENSE-MIT-from-Lean-QuantumInfo. This is a mixed-notice source selection,
not a blanket relicensing of MIT-marked code. The original MIT source and licence remain in
`../QuantumInfo/` as a superseded port attempt; that tree is not on LEAN_PATH.
Attribution: Alex Meiburg, Leonardo A. Lessa, Rodolfo Soldati and the named
source contributors; the HayataGroup operator-inequality files credit
Kei Tsukamoto, Kento Mori and Hayata Yamasaki. Their Apache 2.0 notices are
retained as well.

Only the 58-module import closure of `QuantumInfo.Entropy.SSA`, `.Relative`
and `.DPI` is selected. One unrelated admitted wrapper,
`qRelativeEnt_joint_convexity`, and its meta-only `Physlib.Meta.Sorry` import
were removed. Nothing depends on that wrapper in the selected closure.
Placeholder keywords inside non-executable comments in Misc and CFC were
replaced so that a lexical scan is unambiguous. No theorem was replaced with
an assumption. No library axiom module is imported.

Sources came from immutable GitHub archives. No Git command was run.
`lean/build-vendor.ps1` builds the exact topological list in
`lean/vendor-modules.json`, sequentially with `lean -j1 -M4096`.
The build log for each module has a `physlib-` prefix under `logs/round2/`.
`lean/LibraryAudit.lean` is the separate theorem-type and axiom audit for the
requested roots. Source presence alone is not a proof certificate; consult
RESULT-2.md for the actual build and audit status.

One compatibility adjustment in HermitianMat/Rpow.lean replaces an expensive
simp invocation by the corresponding explicit equality rewrite and raises the
local heartbeat allowance for that private trace-power proof to 2,000,000.
The theorem statement and resource allocation limit are unchanged.

LiebConcavity.lean also has a local instance-search heartbeat allowance of
200,000 for the continuity bridge. Its mathematical statement is unchanged.

The runner uses default elaboration allowances of 2,000,000 heartbeats and
200,000 instance-search heartbeats for the entropy roots. These address
Euclidean-space instance-search timeouts; the thread and allocation limits
remain -j1 -M4096. No theorem hypothesis or axiom is added.
