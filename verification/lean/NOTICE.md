# Source provenance

`Gibbs.lean`, `Factory.lean`, and `Lift.lean` are unmodified copies from
version 1.0.0's `verification/parts/module/lean/`.
Copyright (c) 2026 Seth Douglas and Nidhal Mghirbi; the supplied MIT license is
retained as `LICENSE-MIT.txt`. Exact source/copy SHA-256 records are in
`../logs/reused-source-hashes.json`.

`EntropyBridge.lean` adapts four proofs from LionSR/QICLean revision
`820533fa68cf37999aa9e56d3e44b9423c4d0325`, file
`TNLean/Analysis/Entropy.lean`, copyright (c) 2025 TNLean contributors.
Its Apache 2.0 license is retained as `LICENSE-APACHE-2.0.txt`, and modifications
are marked in the source. The declaration correspondence is:

| Upstream declaration | Local declaration |
|---|---|
| `vonNeumannEntropy_eq_charpoly_roots` | `ScheduleLaw.entropy_eq_charpoly_roots` |
| `charpoly_roots_negMulLog_re_mul_comm` | `ScheduleLaw.charpoly_entropy_mul_comm` |
| `vonNeumannEntropy_mul_comm` | `ScheduleLaw.entropy_mul_comm` |
| `vonNeumannEntropy_transpose` | `ScheduleLaw.entropy_transpose` |

`ScheduleLaw.pure_complement_entropy` adds the pure-state partial-trace
calculation. No other TNLean module or axiom is imported.

ChannelPresentation.lean adapts the private Kraus-normalization calculation
from Physlib QuantumInfo.Channels.CPTP at
f5242c99d796b59a390d26cd7d1a8057e04c46b5, copyright (c) 2025 Alex Meiburg,
Apache 2.0. The adaptation is identified in its source header.

The canonical QuantumInfo dependency is selected from that Physlib revision,
which uses the exact same Lean and Mathlib pins. Its root Apache 2.0 licence,
per-file MIT notice on LiebConcavity.lean, original MIT permission text and
all named author notices are retained under ../vendor/PhyslibQuantumInfo/.
See that directory's PORTING.md for source selection and compatibility changes.
The original MIT Lean-QuantumInfo pin 56e83a9288a3c616285038748e273b3c0e1a36bf
and its licence are retained as non-imported references under ../vendor/QuantumInfo/.

The other new Lean source files in this directory were written for this relay.

Mathlib is a read-only external build dependency, pinned to
`c5ea00351c28e24afc9f0f84379aa41082b1188f` (v4.30.0). Its own Apache 2.0 and
dependency notices remain in the existing dependency checkout.


Round 6 purification/isometry ports
---------------------------------

PurificationGramFacts.lean, PurificationSupport.lean, PurificationExtension.lean
and PurificationMatrix.lean adapt the corresponding GramFacts, PartialIsometry,
ReferenceExtension and GramFactorization files from the read-only companion's
vendored Lean-QIT tree. The paddedBurstAmplitude and
exists_padded_burst_isometry declarations in PrefixPurification.lean adapt the
single-step construction in QIT/HigherOrder/Comb/Realization.lean. All retain
copyright (c) 2026 QuAIR, Authors: QuAIR Team, under Apache 2.0. The full licence
is already retained as LICENSE-APACHE-2.0.txt. Namespace/imports and the
orthogonal-projection API were adapted to Lean 4.30; the reference isometry is
expressed directly as a matrix equality. The former private embedding helper
is public so it also has an explicit axiom audit. No complete QIT library or
new toolchain is imported. Original snapshot paths and SHA-256 hashes are in
logs/round6/purification-port-provenance.json; original source reference copies
are in work/round6/*.lean.reference.txt. No repository commit is inferred from
the companion's modified vendored snapshot. Other round-6 code is new for this
relay.

Historical paths above describe source provenance in the original development; replay uses only the packaged selected sources. Dependency revisions and source hashes are in dependency-pins.json.
