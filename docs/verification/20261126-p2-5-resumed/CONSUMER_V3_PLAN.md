# Cell00 consumer v3 preparation plan

**Goal:** Prepare the five unchanged consumers to use a future accepted attempt005 explicit FieldDecode receipt, retaining v2 and all failed history.

**Architecture:** Adapt v2 into a new file. Reuse its exact accepted-object, gate, audit and context helpers. Extend its receipt adapter to preserve failed attempt004 separately and overlay the published explicit source row onto the two existing immutable source selections.

**Constraints:** No Lean execution, cloud calls, pushes, new proof sources, or changes to accepted dependency gates. Both the successful Field RESULT SHA256 and its full publication commit stay unset until actual acceptance and root publication are available.

## Steps

- [x] Add focused tests for failed004 preservation, exact explicit source override, missing result pin, and missing publication.
- [x] Run new tests against v2 and observe missing interfaces/publication guard fail.
- [x] Create v3 with the smallest receipt/source-selection adaptation.
- [x] Verify 45 source rows, five target closures, 20 public consumer declarations, 40 dependency objects, and unchanged rigorous helper ASTs.
- [x] Record the exact driver hash and pending inputs for root review.

## Fixed scope

The five owners are Decoded, OriginalParse, OriginalFloors, OriginalArithmetic, and OriginalSourceFacts. There are no new theorem statements. The original ecfc and split owner dictionaries retain their original publications; failed attempt004 retains its failure source and normal log. Failed histories are never successful containers.

## Review focus

A missing publication must stop before output creation just like a missing receipt SHA. The future accepted field source graph must equal the original 22-row field graph with only its final source row changed by the frozen explicit override. The final 45-row consumer graph changes no other source, imports, or public API. The actual future successful receipt remains a required input.

## Verification ledger

The test-first run against v2 produced 11 expected failures out of 12 tests. The v3 run passed all 12. Ten prior top-level helper ASTs and all 15 nested helper ASTs are unchanged; the original source-overlay adapter changes only the two final-source checks to refer to its predecessor. All 45 source hashes/imports/public names and five closures match. No Lean or remote task was invoked.

Root subsequently supplied actual attempt005 publication `b667409e7e7f23094637dfccfdceec6e6d34ee68`; this is pinned. `FIELD_RESULT_SHA` remains `None` until actual accepted evidence is delivered and reviewed.
