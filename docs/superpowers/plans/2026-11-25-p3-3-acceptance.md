# P3.3 implementation and acceptance plan

**Goal:** finish the existing P3.3 node, large gcd / large supported branches and the small-core finite frequency window.

**Architecture:** integrate existing byte-identical proofs into P3 continuation `ef1479c272bdd6b24800fa10409d793f0a2fe95c`, verify reusable historical evidence, and publish an independent branch. Preserve all pinned dependencies.

**Spec:** user instruction 2026-11-25; node P3.3 at `7f5330cace31383f5626da526b476dd4b0f43376`; manuscript `chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e` (1106).

## Constraints and review focus

- Reuse reliable existing work. Do not repeat successful unchanged proof compilation or rewrite existing proofs.
- No new axiom, sorry, admit, native_decide or unsafe proof code; keep explicit analytic inputs.
- Preserve original complex sums, equality endpoints, CRT gates and both outside second moments.
- Fixed eta > 0 finite windows do not assert a uniform-in-eta threshold, a Gevrey identity or the precise log^5 window.
- Match sources, exact replay logs, serialized/environment inventories, complete target types and transitive axioms. Missing repository imports must fail verification.
- Disclose inherited dependency evidence separately. No full-P3 completion claim.

## Task 1: integrate existing proofs

- [x] Read the board, manuscript and target declarations; independently review the exact P3.3 scope.
- [x] Identify 13 targets / 93 repository sources; compare current P3: 55 equal, 38 missing, no conflicts.
- [x] Run the pre-integration check: 11 target modules absent, exit 1.
- [x] Integrate 38 unchanged sources; presence and source closure checks pass.

## Task 2: evidence and publication

- [x] Preserve the 46-module historical receipt subset and independent core CI archive.
- [x] Add a fail-closed offline verifier and complete 469-record / 468-name target export.
- [x] Run positive verification and six negative controls; repeat outputs byte-for-byte.
- [x] Obtain independent final review: no Critical/Important findings. Clarify fixed-family / A > 0 quantifiers and separate comparison of published derived files.
- [x] Document 46 full historical modules, one exact baseline interface object, and 46 same-source CI prerequisites without upgrading their evidence claims.
- [ ] Publish the exact verified tree to GitHub and read back its ref/tree.
- [ ] Update only the P3.3 board node and its derived counts while preserving concurrent updates.

## Execution ledger

- No new Lean compilation: both selected and fallback MCP returned HTTP 429. Existing accepted byte-identical proof evidence is reused.
- The 38 missing proof sources were copied unchanged, not newly proved.
- A scratch-storage failure removed the initial isolated worktree before publication. The same sources and evidence were recovered into `/workspace/projects/p33-recovery`; this did not restart proof development or alter mathematical declarations.
- Final review accepts the node scope from literal signedError through deletion and fixed-positive-eta finite-core reduction. Later spectral bounds and final P3 assembly remain open.
