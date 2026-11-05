# Round 4 split-module type audit

## Observed failures and evidence

Run 41940428570 at 9040148b7372eafc224e945b6fb902a2b4463351 failed the
old R4 defining-module count: PairedV2Batch4To64 expected 207, observed 17.
Its 224 exported declarations and final bridge retained byte-identical complete
types from successful pilot run 41762528251. All 64 moved source proof blocks
were byte-identical; all sixteen selected production source hashes matched the
actual run receipt. The other three original source modules were unchanged.

The first strict migration contract predicted 475 owned declarations. Real run
41951293351 at 07fc3bd5b5171faf996589c61bdb60f37c709a02 instead observed
597 owned declarations, 902 serialized occurrences and 305 shared occurrences.
The Lean audit completed with exit code 0. The Python contract then rejected
exactly 122 unlisted private declarations, with no missing expected names.
They are LowerSum and UpperSum's additional rowIndices.match_1 helpers: each
module contributes eq_1 through eq_60 plus splitter. These are 120 theorems and
two definitions. The earlier estimate omitted those two generated groups.

All 597 actual complete type strings were independently compared byte-for-byte
against their corresponding original pilot types, including all 414 historical
records and all extra copies. Their names, owners and kinds match the explicit
mapping. Rechecking the entire published parser with that exact597 mapping
also passes every owned/serialized partition, occurrence, safety, raw-dependency
and bridge check. Axiom unions remain propext, Classical.choice and Quot.sound.
The failed run's exact-overlay state and audited input hashes were unchanged
before and after the export.

Evidence artifact SHA256:
c2b4752727602937c9c84e468a67ce03878e56c9b678bea439492e18bde7ab01

## Exact historical correspondence

The immutable baseline retains every one of the original 414 names, kinds,
defining modules and complete type SHA256 values. No type text is rewritten,
normalized or truncated before hashing.

- 224 records keep their names and owners.
- 64 source-level proof records keep their names and move to twelve split
  modules.
- 65 public generated equation records keep their names and have individually
  specified owners.
- 61 old module-private matcher helpers map individually to GeometryChecked's
  exact private names. Each has three further explicitly listed counterparts
  in CertificateInputs, LowerSum and UpperSum, with the same complete type hash
  and kind. No wildcard private-name matching or prefix stripping is accepted.

This is exactly 414 mapped historical records plus 183 specified additional
copies, for 597 current owned declarations. The consumer rejects every missing
or extra name and prints the complete difference. All 414 historical types are
covered through explicit mappings; it does not claim all 414 original names
still exist. The original historical type hashes remain unchanged in schema v2;
only the explicit duplicate-name records and observed evidence are expanded.

## Checks and unchanged scope

The Lean audit still examines the sixteen modules and every raw serialized
ConstantInfo. Its checking logic is unchanged from the previous published R4
version; only its explanatory comment is updated. The exact owned census must
match the owned serialized partition and exported declarations. Shared theorem
copies retain all type/universe/kind/owner/theorem-all checks. Their own raw
bodies and types are checked for dependencies, rather than relying only on the
owner theorem's cached axioms. Unsafe, partial, axiom, missing-dependency and
self-referential theorem records fail.

The final bridge remains separate, retains hLower and hUpper, and must match
its original complete type hash. All sixteen production sources and the new
baseline remain hash-pinned. The prior exact-overlay verifier, pinned bundle,
three-file difference, dependency HEAD/blob/mode/index/bytes checks and R4
pre/post receipts are unchanged. The receipt continues to identify the exact
historical patched dependency, not original fixed source.

No production mathematics, dependencies, pins, overlay, R3, R6, workflow or
runtime settings are changed. The change is limited to the exact R4 generated
name inventory, its pinned baseline, regressions and explanatory text.

## Validation boundary

The revised unmodified parser passes the real run41951293351 stdout. Synthetic
regressions additionally mutate or remove every new122 name/type/owner/kind and
exercise serialized safety checks. This does not change the prior overall CI
failure into success. A fresh full workflow remains necessary to confirm the
revised pinned baseline and wrapper together. No new Lean run is implied by the
local parser or unit-test results.
