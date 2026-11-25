# Reused original owner repair evidence

This package preserves historical proof-repair evidence from P1 commit
`99c1f8ba1dc453b21f47e30b667db0de93d73387`. It grants **no new P2
compilation, independent kernel replay, or ownership acceptance**. The new
P2 owner/core graph must be validated separately against its actual source
and dependency bytes. Root records that execution separately.

## Existing donors

| Donor | Historical batch | Owned declarations | Reuse scope |
|---|---|---:|---|
| `OriginalDescendingFifteenCellOwnership` | 48 | 47 | Existing explicit positivity chain |
| `P4ASlot19ChargedFrontier` | 48 | 21 | Existing finite mask sum expansion |
| `OriginalAscendingThirteenCellOwnership` | 58 | 50 | Existing finite-order monotonicity proof |
| `OriginalDescendingFifteenLiteralAffineRows` | 58 | 113 | Applicable proof hunks only |
| `OriginalAscendingThirteenLiteralAffineRows` | 80 | 18 | Applicable proof hunks only |

All five donor source hashes match both the pinned Git commit and their
historical validation records. Historical normal compilation, independent
`leanchecker`, and full environment-owned declaration/type/axiom audits
returned exit code 0. The **249** owned declarations here are the old donor
inventories, not additions to P2's accepted union.

The two `LiteralAffineRows` donors must not overwrite current refactored
owners wholesale: definitions moved into cores must keep one owner. Only
existing proof hunks are eligible for transplantation. The resulting merged
source will have its own source hash and dependency context.

## Preserved evidence

- `donor-sources/*.lean.txt` preserves the exact historical source bytes as
  evidence; these files are not active Lean modules.
- `historical/` contains byte-for-byte copies of source comparisons, normal
  and kernel commands/logs, after-normal and after-kernel source/output
  fingerprints, and the original batch validation and release records.
  Original paths, immutable Git blobs, byte sizes and SHA256 values are in
  `MANIFEST.json`.
- `SUMMARY.json` gives exact per-module source, object, command, log and
  owned-inventory bindings and separates historical credit from P2 context.
- `SELECTED_OWNED_EXPORTS.json.xz` is a clearly labelled derived selection:
  it keeps every complete JSON record for all five donor modules, including
  expanded types, expression trees, names and transitive axioms, together
  with the original full-export hash and each record's original index.
  It is not represented as an original full-export byte stream or new audit.
  Full batch audit logs and exports are referenced by their immutable Git
  paths and hashes rather than duplicating unrelated declarations.

## Block03 export lookup

`BLOCK03_LOCAL_EXPORT_LOOKUP.json` records the bounded local P1 search.
All 31 archive files were inspected recursively through 5,429 member names,
without errors. No Block03 numerical receipt/archive or scalar audit member
was found. Text lookup found only candidate source hashes in
`seed-terminal-integration/SOURCE_UPDATE.json`. This is not a claim about
unqueried live environments. Root's newer remote Block03 audit result
requires evidence export; it does not require numerical recompilation.

No active Lean file was changed and no compiler or remote job was invoked
while collecting this package. `BYTE_VERIFICATION.json` records the local
copy/hash/inventory checks only.
