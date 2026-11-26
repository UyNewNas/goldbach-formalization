# Existing P1 successors: source reuse inventory

This package is restricted to the 10 P1 modules in the 38 round-6 failed/blocked modules after excluding the four round-7 repairs. It contains no new proof and has not run Lean or changed production/round-7 files. All five candidate postimages are byte-identical to existing donor sources.

| Module suffix | Historical evidence | Placement |
|---|---|---|
| ProducerAttainedRowBinding | blue batch79 exact baseline/postimage; normal, kernel and all-owned PASS | after/ |
| VariableFourthCellTestLimit | blue batch76 final revision; exact baseline/postimage; normal, kernel and all-owned PASS | after/ |
| VariableFourthSourceCoefficient | blue batch85 exact baseline/postimage; normal, kernel and all-owned PASS | after/ |
| VariableFourthRowModulusTransfer | exact public proof-only repair; later successful owned audit binds it as a dependency; no standalone target receipt located | after/ |
| FifthAttainedRowBinding | batch5 individual normal success, then batch8 next17 exact-source kernel/all-owned PASS; added import lies outside the current 377-module graph | scope-review/ |

The normal command containing FifthAttainedRowBinding exited 1 because the wider batch had failed targets. The manifest preserves this and uses the explicit successful module header plus the later completed audit that binds that exact source and normal log. It does not call the whole batch successful.

All 36 existing theorem headers and all four definition blocks are unchanged. The first four candidates also preserve imports/options. FifthAttainedRowBinding adds ActualUpperPolicyDensity and therefore must not be installed through an unchanged-import/377-module selection. The manifest identifies the already-existing lower-level parity composition for later review; this package does not implement a new alternative.

Five other examined P1 modules are already byte-identical to the donor and have no candidate copies. Apply a candidate only when the current run exposes its corresponding error, then use the unchanged current normal/replay/owned/source-context gates. Historical objects and receipts do not constitute current P2 acceptance.

SOURCE_REUSE_MANIFEST.json contains exact source hashes, original receipt locations, verified log hashes, scope conditions and the full file inventory. CENSUS.json records the bounded search. Normal/audit logs are losslessly compressed; each compressed entry records both file SHA and uncompressed SHA.
