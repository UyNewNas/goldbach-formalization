# S01 Yellow Reuse Map

This is a read-only source and evidence inventory for all 33 yellow nodes in the authoritative tracker. It does not make mathematical closure judgments or alter tracker colors.

## Inputs and method

- Authoritative tracker: `E:/timot/Documents/FilesForGPT/Myath/1_+_1.748_lean_proofs/main.md`, SHA256 `eda2afd45edaa3d00072bb677dd5eb3c9937c40d63ac23149ebbe3581cbeaca9`.
- Frozen R source batch: `docs/source-only/20261102-resume-30r`; manifest SHA256 `cdfc42fe572d5ef5c006b6885f02a3960f3eb88433c032d3d136982744b37ab7`.
- `MAP.json` lists each yellow tracker line verbatim, its containing yellow scope, its nested yellow descendants, every descendant blue/green row, and exact source-group registry/report hashes. Each referenced source record retains its path, intended module, raw source SHA, direct exported declaration names/lines, and original registry entry.
- Search covered production sources, all `docs/source-only` including ignored files, hidden `.lake/proof-continuation/source-reviews/drafts`, and local workflow/proof-continuation metadata. Hidden/ignored Lean-file enumeration observed 114,554 `.lean` paths.

## Proof evidence findings

New source modules contributed from frozen R remain source-only, uncompiled/unverified, and at zero formal credit. A deterministic scan compared 368 candidate source module records against 403 local historical proof receipt files. It found 23 exact-source receipt bindings (16 PASS, 7 FAILED) for five reused prerequisites: ActualExtendedThirdIdealCap, PowerErrorBudget, Part3CommonSmoothCutoff, FinitePrimeGeometryCore, and ActualSmallRoughAttachment. Passing receipts match the current lean-toolchain, lakefile.toml, and lake-manifest.json SHA256 values. Their scope says normal-trust development compilation only; these are reusable prerequisite evidence, not full yellow-node or kernel/axiom acceptance. Exact paths, direct-source hashes, pins, outputs, and failed attempts are in HISTORICAL_EVIDENCE.json; MAP.json cross-references these sources to R source groups and yellow scopes.

Read-only GitHub commit queries for e2a05f73d5f169fff847d72dcfcc66ec54ad4f87 and 9d4c3a4010d42aedd9e7231bf94386019cfffccc returned no PR-associated workflow runs or combined statuses. The connector exposes only PR-triggered runs; a direct public Actions API request was rate-limited (403). No global historical push/dispatch inventory or numeric workflow ID was obtained.

The remotely fetched default .github/workflows/lean.yml (name Lean verification, blob SHA 52d7be7e21221f466fb1a695a9927e1760a7a2e4) supports workflow_dispatch, a full lake --wfail build, project checks and theorem leanchecker, and uploads lean-build-timing artifact. The local branch .github/workflows/lean.yml is different (name Lean core verification) and retains broader stage/type/axiom logs. The exact branch-specific workflow must be selected for any remote run; no run was dispatched here.

Existing sources that must be reused include the hidden actual full cusp Hilbert basis, native graph/operator Parseval, smooth eigenprofiles, normalized-cusp Fourier ODE, and real/imaginary K-shapes. R22-R24 reports/registries record their paths and distinguish these existing sources from still-open classical trace, full continuous/holomorphic realization, A/J/regular/gap, and total-cost obligations. This inventory does not re-prove or close those targets.

## Scope graph and status

The 33 yellow rows are stored as Y01–Y33 in `MAP.json`, with exact original tracker text and indentation-derived containment edges. The map marks each as `OPEN_IN_AUTHORITATIVE_TRACKER`; source references are evidence pointers only. No source was duplicated and no proof/check was run.

## Delivered files

- `MAP.json`: machine-readable yellow-node map, source declarations, source hashes, source-group REPORT/REGISTRY hashes, and evidence search result.
- `REGISTRY.json`: hashes for this report, map, generator, authoritative tracker, and frozen manifest.
- `build_map.py`: local source-text/JSON inventory generator; it does not invoke Lean, Lake, guards, numerical producers, or replay.
- `audit_history.py` and `enrich_history.py`: exact-source receipt and pin audit scripts; neither runs a compiler or replay.

