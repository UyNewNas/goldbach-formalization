# Batch15 verified acceptance evidence

Twelve exact-source owners completed normal compilation, independent named kernel checking, and the original full environment-owned type/axiom audit at source and driver commit `95b96cb5fe1a26322b7ecbdc66f15c2775035138`. Offline verification of the complete exported records confirms **392 owned declarations: 213 public and 179 private**. All owned records include their complete printed types, raw type expressions, universe parameters and transitive axiom lists.

The fourteen-target run retained two actual normal failures. Each group's successful owners still reached its completed audit, and both failures are excluded from the accepted owner set. This archive does not establish completion of the four original P1 roots, the complete P1 closure or density acceptance.

## Actual result

| Group | Normal targets | Accepted owners | Owned | Public | Private | Overall task exit |
|---|---:|---:|---:|---:|---:|---:|
| wire-five | 5 | 4 | 71 | 71 | 0 | 1 |
| ordinary-five | 5 | 4 | 106 | 106 | 0 | 1 |
| interiors-four | 4 | 4 | 215 | 36 | 179 | 0 |

All three successful-owner audit commands exited zero. The Wire and ordinary task exits remain nonzero because each has one failed normal. The Interior task exited zero after all four normal builds and its complete audit.

| Accepted owner | Owned | Public | Private |
|---|---:|---:|---:|
| `ImbalancedChen.P1ActualVariableFifthGlobalSourceAssembly` | 18 | 18 | 0 |
| `ImbalancedChen.P1OriginalFifthMiddleShellBinMoment` | 20 | 20 | 0 |
| `ImbalancedChen.P1OriginalFifthRawBoxSelectorEquivalence` | 16 | 16 | 0 |
| `ImbalancedChen.P1OriginalOld15Majorant` | 17 | 17 | 0 |
| `ImbalancedChen.P1OriginalVariableFourthActiveOnly` | 16 | 16 | 0 |
| `ImbalancedChen.P2OriginalLowerCompactStartCapConstructor` | 84 | 84 | 0 |
| `ImbalancedChen.P4BCompactSmoothMassPrecision` | 2 | 2 | 0 |
| `ImbalancedChen.P5ActualHBMediumRoleSupports` | 4 | 4 | 0 |
| `ImbalancedChen.P4AOriginalFull87DescAscPairInteriors` | 80 | 12 | 68 |
| `ImbalancedChen.P4AOriginalFull87H3Interiors` | 38 | 7 | 31 |
| `ImbalancedChen.P4AOriginalFull87H5H7Interiors` | 50 | 9 | 41 |
| `ImbalancedChen.P4AOriginalFull87SeedNineFiftyInteriors` | 47 | 8 | 39 |

The actual remaining failures at this source commit are:

- `ImbalancedChen.P1ActualVariableFifthPositiveCellLimit`, line 321: the weighted difference supplied by `IntegrableOn.sub` did not simplify to the retained `variableCellKernel` goal.
- `ImbalancedChen.P2OriginalAdaptiveSourceSplit`, line 131: the expanded compact-region result did not simplify to the retained `rootCell`/`List.map rootCell` goal.

Their complete normal logs and command receipts remain in the archive. No `NORMAL_PASS.json` or accepted audit owner is credited to either failed target. Subsequent repairs belong to their own source commit and evidence batch.

## Export and source provenance

- Export task: `job_46f4314f2dee4866899e035dab37a3c0`.
- Source/driver commit: `95b96cb5fe1a26322b7ecbdc66f15c2775035138`.
- Driver SHA256: `364bc26c294293afc06a05513de1f7a7114743dfe8d1969788cf26f22f951278`.
- Source manifest SHA256: `13034d8b171c6e3a51faeff1ac337f386085cf947028f5998648d69ee415cf49`.
- Archive: `verification.tar.xz`, 362,196 bytes, SHA256 `93660ef8b749c794f3239d3b27cda4551f63089c4c32a25b28c151c4ef45670e`.
- Uncompressed tar SHA256: `220a53e618b1f0c1e04b2f31c3da53fbdea2c63f3bf8ab67d47674fc4b2aed93`.
- Embedded `ARCHIVE_FILES.json` SHA256: `a1dadf041d22786856256c456807d33a1dbf62627f4de386b25cfea69338c33c`.

All 495,974 bytes of the completed export task output were retrieved in 16 contiguous base64 pages, with a maximum request size of 32,000 bytes. The final page reached EOF; no output was truncated. Decoding the archive and checking its compressed/uncompressed hashes succeeded. All **334 indexed payload files** matched their recorded sizes and SHA256 values; the archive additionally contains its independent index, giving 335 extracted regular-file members. Member names were checked for absolute paths, traversal, duplicates and nonregular entries before extraction.

The archive contains the three actual group roots and their three existing-object bootstrap directories. `EXPORT_SUMMARY.json` retains the observed existence records for all six proposed bootstrap paths: the three earlier fetch-only bootstrap directories did not exist. The bootstrap records bind the unchanged published driver, verified Git object import receipt, and original dirty Git HEAD/status. Before/after task records agree for all three groups.

## Independent local verification

`LOCAL_VERIFICATION.json` records the verified owner-by-owner evidence, source Git blob/SHA, closure size, normal log and command bindings, kernel commands, all six source/output fingerprints, exact declaration counts and prior receipt catalogue.

The local review checked:

1. All 72 archived command records against their complete raw logs, hashes, paths, exit codes and expected arguments. Each of the fourteen selected targets had exactly one actual normal attempt. Each successful normal's actual project `Built` set was exactly that owner, with no unexpected compiled project module.
2. Every normal command copy and durable receipt, its complete Git95 project-source closure, dependency `.olean`/`.trace` fingerprint scope, source configuration, actual runtime configuration and unchanged guard/serializer/runtime bindings. Common dependency-object fingerprints agreed across the observed contexts.
3. Each successful owner's source plus five compiled-facet fingerprints across `NORMAL_PASS.json`, `BEFORE_KERNEL.json` and the final audit receipt. The source hash and byte length match the exact Git95 object.
4. A zero-exit guarded `leanchecker --verbose` command and exact named replay for every accepted owner. Guarded stock `lake --no-build build` checks succeeded before and after auditing.
5. Frozen audit plans, original normal-log reuse, exact source maps, original e9 runner/template bindings, the existing lane0 serializer lock receipt and chronology. Only the populated lane0 was executed; lane1 retained its empty module list.
6. Every raw `AUDIT_RECORD`, the full environment-owned name inventory, per-module emitted counts and `OWNED_EXPORTS.json`. All names are unique and belong to the selected owners. Declaration counts were recomputed from these records; private declarations were included. No axiom declaration or `sorryAx` was accepted, and transitive axioms are limited to `propext`, `Classical.choice` and `Quot.sound`. Printed types and raw type expressions are present without elisions.
7. The generated auditor body against an existing accepted auditor, allowing only the intended owner imports and module array substitutions. Source preimage backups, exact Git postimages, source-install scope and protected original-root bindings were also checked.

The original exporter retains compiled-artifact **metadata** in the evidence records; compiled binary payloads are excluded. Consequently, the local six-facet verification establishes agreement of the recorded source/output fingerprints across the actual normal/kernel/audit chain. It does not perform a fresh rehash of live cloud objects or a new kernel run. No compiler, Lean, Lake or new cloud task was invoked by this local review.

## Deduplication and claim boundary

The prior owner catalogue was read from the already accepted archives: Batch10 has 71 owners, Batch11 has 4, Batch13 has 3, Batch14 has 2, and the G3 C pilot has 1. Their precise receipt members and SHA256 values are preserved in `LOCAL_VERIFICATION.json`.

Both the **twelve accepted owners** and **all fourteen actual normal targets** have empty intersection with those existing 80 + C owners. The prior receipts were used to establish identity and avoid repeated compilation; this review does not repeat their acceptance checks. Successful B15 normal builds were reused by the kernel/full-owned audit. The twelve new acceptance records do not imply that downstream P1 roots, all project modules, the remaining G3 units or density conclusions are complete.

## Files

- `verification.tar.xz`: complete original indexed logs, command receipts, bindings, source preimage backups, exact executed helper copies, normal receipts and full-owned audit records.
- `EXPORT_SUMMARY.json`: original exporter summary and actual bootstrap existence records.
- `LOCAL_VERIFICATION.json`: independent offline verification findings, exact twelve-owner catalogue, per-owner declaration counts and source/output bindings, retained failures and prior-owner deduplication evidence.
