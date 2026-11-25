# P2.4 original compact proof implementation plan

> **For agentic workers:** Execute the existing manuscript proof and use the source-selection manifest to avoid duplicate formalization. Keep compilation and independent kernel replay as separate evidence.

**Goal:** Close the four P2.4 obligations for the original compact third-layer adaptive tree, its ordered charges, every leaf integral enclosure, and the archived total.

**Architecture:** Reuse the existing L/K/N/O source chain and the reviewed P namespace repair. Install missing modules in an isolated worktree, fix only compiler-demonstrated interface or proof-script defects, and preserve the original domain, kernel, rounding, tail and constants.

**Tech stack:** Lean 4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; Cloud Compile Private 8e1da5a7.

**Spec:** User's P2.4 instruction; chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e, paper/release-20261106/en/numerical-appendix.tex and verification/data/certify_extended_prefix.py; existing docs/source-only/20261102-resume-30p/reviews/t23_review_compact_s16.md and 30q/reviews/q23_review_data_trace.md.

## Global constraints

- Reuse local, remote and external reliable work; do not re-prove completed work.
- Formalize manuscript mathematics only. Do not add axioms, sorry/admit, unsafe declarations or native_decide.
- The exact compact charge is 144590669409566793572719 at scale 2^80. The complete forest has 2000021 leaves; 1852040 is active heap occupancy and cannot replace the forest.
- The supported whole archived upper is 1230679674488580033396846301/180734410032387061618573312, below 681/100. The old 6809/1000 stopping target was not reached.
- Existing whole-Python operational equivalence is distinct from the four mathematical obligations. A conditional checked-table lemma is not an unconditional endpoint.
- The user has authorized implementation, compilation and GitHub submission. Preserve other worktrees and their uncommitted files.

## Review focus

- Frozen sources must match their source-selection hashes; no unrelated candidate overwrites.
- Compact and original tail are each included once, with the original factor 4 and strict/closed boundary identity.
- Full source forest and ordered leaf multiplicity must be used, including empty/exact leaves.
- Finite guards must actually return true in kernel-checked proofs; source-only rfl bodies receive no credit before evaluation.
- Source, object, dependency signatures, toolchain and final declaration axioms must agree.

## Task 1: Install and compile existing proof closure

- [x] Select all missing project imports from the pinned source-only records; record sources and hashes in verification/part2/p24_source_selection.json.
- [x] Reuse the reviewed transparent abbreviation repair in Part4ActualThirdOriginalClosedSplitAggregation.lean.
- [ ] Run existing verification/part2/run_winner9_private_checks.py on ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint using isolated outputs and valid inherited compilation records.
- [ ] Read every failed module log, classify the cause and repair the exact source without weakening statements. Re-run the affected closure.

## Task 2: Verify finite calculations and full endpoint

- [ ] Evaluate the original table, cached run, complete leaf/charge guard and fixed-source rational equality; retain truthful status if a guard fails or resources prevent completion.
- [ ] Check the full no-argument endpoint type and trace it to the original manuscript functional.
- [ ] Independently replay accepted modules using leanchecker and audit complete owned declaration inventories and transitive axioms.

## Task 3: Review and publish

- [ ] Have an independent agent review scope, source provenance, proof assumptions and verification evidence.
- [ ] Commit exact code and verification receipts to work/p2-4-compact-proof-20261125, push, and verify the remote SHA.
- [ ] Report only observed completion, with exact remaining obligations if any. Do not label P2.4 green from source coverage alone.

## Execution ledger

- Baseline: a929011ec95843553fc2e10b7291c8077e0952c0 on work/p2-formal-proof; isolated local worktree /workspace/scratch/daaa8ebc2a3f/goldbach-p24.
- Remote P2 baseline /workspace/goldbach-p2 remains at 8657cfffef159185f73c6a04ae4d31c846c0d0a9. Existing /workspace/p2-private-20261124 contains unrelated uncommitted work and will be read only for validated cache reuse.
- Ruling: proceed with the already authorized task without a new design-approval pause; acceptance is fixed by the manuscript and existing P2.4 obligations.
- Published source installation: `1af39633da1e6274d4e338edc44316b9e9c6d7ff`. Published six exact later CI overlays: `543643fd074ca989e7b21d3b2f749531bb0e89c8`. Published exact later serial-queue/heap overlays and manuscript semantic review: `2dbe821e7f6eabc4fd7ec4de793d4e243c1df02b`. These are source checkpoints, not current combined-closure acceptance.
- A local transient-workspace reset was recovered by cloning the already published branch. The current local directory is now an independent checkout at the same absolute path, rather than the original linked worktree.
- P2's initial symbolic build job `37583cbeb3454f0892bdaea181f72ff2` was cancelled while still queued: inspection showed its command omitted the explicit native dependency snapshot required by the existing verifier. No Lean result is claimed from that job. Read-only discovery job `09582ca9043240a98d564e2a491002e3` checks for existing qualified snapshots.
- Temporary P1 use is restricted to a separate directory because the P2 queue is congested. Setup job `job_c2dc0dc74dbd4a39ab74edd392d6fd1f` succeeded and created `/workspace/p24-original-compact-20261125` at `2dbe821e7f6eabc4fd7ec4de793d4e243c1df02b`, plus clean source baseline `/workspace/p24-accepted-baseline-8657`. The pinned Lean/Mathlib versions match P2. Shared blue build/package directories are read-only inputs for this task.
- P1 inventory job `job_5f86596ef9634787a90a36cf8a7aa597` found 262 source/import-matching object candidates for the earlier 337-module snapshot; source-compatible project ancestry reduces that set to 253. These counts are only an inventory. Original inputs, current source changes, native dependencies, and runtime still require qualification before cache acceptance. Diagnostic compilation, if used to locate interface failures first, must remain explicitly separate from acceptance.

- Published 22 exact successful shared dependency overlays and the diagnostic driver at `67e0791e62db299690d29f19440bcf579e5e1492`. Full CI candidate reuse audit is complete: 84 manifests, 89 workflows, 163 runs; all 30 successful candidate versions intersecting the then-current closure are reused. DirectedLog has no successful strict-audit source candidate; its total-recursion repair was published at `63fcd8691951b552078d928bb840c5eef46d0221` and remains pending fresh compilation.
- Actual P1 diagnostic `job_bd7fe422f9fd4031abc8debc0a85d8c2` ran 60.73 seconds, exit 1, peak 4,205,551,616 bytes. Three fresh modules passed; two modules failed on transparent-abbreviation rewrite matching and unused tactics. Inputs were stable. This is diagnostic evidence only, with all acceptance credits false; the exact stdout is retained in `docs/source-only/20261125-p24-original-compact/p1-structure-01.log`. The failed 24 GB request `job_0c247ec74a9946c5aa1aaf52e3314dbf` never started and carries no proof result.
- Prepared minimal proof-body fixes for the observed structural failures and adaptation of the three forest consumers to explicit existing splitCount equations. The latter adaptation is proactive, not a compiler-observed failure. The original theorem statements remain unchanged.
- Extracted the exact 7,708-byte generic reciprocal-rounding block into `P2GuardedReciprocalRoundingCore`, preserving the existing wrapper and U8 suffix. Q80 changes only its first import. Independent static review confirms byte identity, and the real graph shrinks from 339/26/826 project/direct-native/native modules to 322/22/515. All 515 native sources have matching original CP provenance; this is still not input qualification. The endpoint bytes and mathematics are unchanged.
- The P2.4-specific native qualification adapter passes 15 focused tests and independent static review. It retains Architect.Command quarantine until the already completed fresh leaf receipt is obtained and physically rebound. Read-only P2 export `e089927fd02e4b45901a67da1dadd369` is queued. The old P2 task `77e605315ba246b4a2c30811d34fe812` reports that leaf's fresh compilation success, while its overall qualification job exited 2 because other providers were blocked.

- P2 discovery has now returned an existing complete attempt-003 native snapshot (515 providers, qualified, zero blocked) and 619 project records. Exact local set/identity comparison in `p2_snapshot_scope_match.json` confirms equality of the required 515 module names and all recorded source identities/pins with the existing P2 REQUEST and census. The actual current physical snapshot check is queued as `a49373261d704020a7d9357328fc8b2c`; existing records are not automatically accepted. Root cancelled its still-queued P1 native job `job_08f306af132d4f1bb06fd730d4ce8030` to reuse this complete P2 work.
- P2 Architect export `e089927fd02e4b45901a67da1dadd369` completed, but its 2 MiB stdout cap discarded 321067 bytes. The emitted archive is incomplete and cannot be used for transport. No fresh leaf migration is currently required for the P2 snapshot route.
- Independent fixture review found and repaired two diagnostic donor issues: new external roots could differ from old recorded roots, and a failed copy could leave a consumable partial donor. The helper now binds ordered physical external roots, toolchain, all loadable facets and evidence; an INCOMPLETE marker blocks consumer selection until the receipt is complete. Ten focused filesystem/Git fixtures pass, including the demonstrated failure cases. All diagnostic acceptance credits remain false.
- P3 and backup services became reachable after earlier connection failures. Read-only P3 inventory confirmed the locked Lean/Mathlib versions and that the five-module arithmetic chain has no existing local project objects. Root queued an isolated direct-Lean diagnostic of that existing chain as `4f24c1d1238b4071bb317725a2eb201a`, without changing the shared P3 checkout. P2 remains the selected existing qualified environment for combined-closure acceptance.
