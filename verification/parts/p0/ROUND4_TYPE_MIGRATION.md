# Round 4 split-module type audit

## What failed and what is already evidenced

Run 41940428570 at commit 9040148b7372eafc224e945b6fb902a2b4463351
completed the full build, kernel replay, root axiom gate, R3, R6 and exact
historical dependency-overlay checks. R4 alone failed its old defining-module
count: PairedV2Batch4To64 expected 207, observed 17.

The failed R4 stdout contains 224 declarations. Each is one of the successful
pilot run 41762528251's 414 declarations, and all 224 complete type strings are
byte-identical. The final bridge's complete type is also byte-identical. This
is evidence for those 224 declarations and the bridge only.

The old Batch4To64 module now imports twelve split modules. All 64 moved source
proof blocks (60 row checks, geometry_checked, certificate_inputs, lower_sum,
upper_sum) are byte-identical to the successful pilot's original proof blocks.
The other three original audited source modules are unchanged. All sixteen
current production source hashes were checked against the failing run's actual
pre-export receipt and are frozen by this checker.

## Historical correspondence, not a reduced census

The immutable baseline records every one of the pilot's 414 names, kinds,
defining modules and complete type SHA256 values. It adds explicit current
names and owners. It never rewrites, normalizes, truncates or weakens the type
text before hashing.

- 224 records keep their names and owners.
- 64 source-level proof records keep their names and move to the twelve split
  modules.
- 65 public generated equation records keep their names and have individually
  specified expected owners.
- 61 old module-private rowIndices.match_1 helpers (eq_1 through eq_60 and
  splitter) map individually to GeometryChecked's exact private names. An
  additional explicitly listed CertificateInputs copy of each is required,
  with the same complete type hash and kind. No wildcard private-name matching
  or arbitrary prefix stripping is accepted.

The proposed exact set therefore has 475 owned declarations. This is a
fail-closed assertion pending a new Lean/CI run, not a previously observed
compiler result. In particular the 190 migrated historical records' actual
new owners/types, the private names and the extra 61 copies remain to be
verified. A mismatch reports full missing/extra name sets and fails; it must
not be corrected by silently discarding records or lowering the baseline.

## Checks

The Lean auditor uses the successful R3 serialized-occurrence checking logic
with the sixteen concrete R4 modules. The complete owned name/index census
must equal the owned serialized partition and exported declarations. Every
serialized ConstantInfo is audited, including same-name shared generated
proofs. Shared copies require exact type, universe, kind, owner identity and
theorem-all checks. Their own raw type/body dependencies are checked rather
than trusting only the cached owner theorem's axiom set. Missing dependencies,
self-referential theorem bodies, unsafe/partial/axiom declarations and forbidden
transitive axioms fail the audit.

The Python consumer requires exact serialized occurrence coverage and the
entire 475-name correspondence with original complete type hashes. The bridge
is separate, retains hLower and hUpper, and must match its original complete
type hash. All 414 historical types are covered through explicit migration
mappings; this does not claim all 414 original names still exist.

The prior read-only exact-overlay verifier and its pinned bundle, three-file
delta, dependency HEAD/blob/mode/index/bytes checks are unchanged. R4 still
verifies the exact patched dependency before and after export, and the receipt
explicitly says this is the historical patched dependency, not original fixed
source. R3, R6, workflow, mathematics and dependencies are not changed by this
patch.

## Validation boundary

Lightweight tests use synthetic compiler occurrence records and temporary Git
fixtures. They do not establish Lean elaboration, actual current generated
names/owners, raw compiled-body contents or successful CI. A fresh authorized
full workflow is still required. The old successful pilot artifact must not be
reported as verification of this new R4 checker.
