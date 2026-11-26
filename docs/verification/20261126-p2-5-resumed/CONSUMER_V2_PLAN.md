# Cell00 consumer receipt continuation implementation plan

> **For agentic workers:** Execute this scoped adaptation inline with the executing-plans and verification-before-completion skills. The root agent controls publication and remote execution.

**Goal:** Reuse the accepted final FieldDecode owner from attempt004 in the five existing Cell00 consumers, preserving all original owner provenance.

**Architecture:** Retain the frozen five-consumer driver and source selection. A new driver validates the successful one-owner final receipt together with the unchanged failed attempt003 and attempt001 receipts. Its source graph changes only the final FieldDecode row, selected from the frozen final package.

**Tech Stack:** Python standard library; the existing strict Lean/leanchecker/full-owned audit pipeline.

**Spec:** Root delegation for the continued P2.5 finite pipeline; existing `cell00-field-final/RUN_PLAN.json` and `cell00-five-consumers/RUN_PLAN.json` in the 20261126 continuation directory.

## Global constraints

- Only create the resumed consumer driver, its focused structural tests, and small preparation records. Do not edit existing runners or Lean sources.
- Preserve the five selected consumer modules, 45-module graph, 40 reused objects, 20 public consumer declarations, and all strict compiler/audit flags.
- No accepted normal/replay/audit gate is rerun. No failed final object is reused or failed aggregate relabeled.
- All three ecfc and ten split owner dictionaries retain their original receipt and publication. The final owner retains the attempt004 publication.
- The actual successful attempt004 receipt hash is required before any runner filesystem mutation or gate. Until supplied, the draft must fail at its first guard.
- No remote calls, pushes, or publication by this worker.

## Review focus

- A failed split aggregate must remain failed even though thirteen of its owners succeeded.
- Relabeling an old owner as an attempt004 product must be rejected.
- A field source override may change only the selected final owner path/hash; its imports and public API remain identical.
- The final receipt's 21 dependencies must resolve to exactly the objects checked from the historical branches.
- A missing successful receipt pin must block before output creation, Git, or compiler invocation.

## Task 1: Adapt and verify the receipt consumer

**Files:**

- Create `run_cell00_five_consumers_v2.py` in this directory.
- Create `test_cell00_five_consumers_v2.py` in this directory.
- Create `CONSUMER_V2_PREPARATION.json` in this directory.

**Interfaces:**

- `validate_field_history(field, split, prior)` checks the one-owner success plus preserved failed history without filesystem effects.
- `select_sources(selection, final_selection)` returns the exact 45-module graph with only the final source row overridden.
- `main()` retains the original one-publication argument and exact-byte publication binding.

- [x] Write structural tests for preservation, failed aggregate rejection, changed owner rejection, exact source overlay, and the missing-pin guard.
- [x] Run those tests against the frozen original driver; observe missing continuation interfaces fail without running its `main`.
- [x] Implement the new driver by minimally adapting the frozen `4f12d9bc` driver.
- [x] Run the focused tests and compare unchanged helper ASTs and original file hashes.
- [ ] Once actual successful attempt004 evidence arrives, inspect it and pin its result hash; otherwise retain the hard stop.
- [ ] Report the exact invocation, files, validation evidence, and any remaining blocker to the root agent for independent review and publication.

## Execution ledger

- Initial scope: parent created an isolated checkout at `4e69759e3d27495c0e7bccfee23b7a0b42c48ea6`; the historical dirty checkout is read-only.
- Ruling: the original large source selection stays immutable; a checked, single-row overlay avoids copying a second 45-module manifest and makes the actual source delta explicit.
- Ruling: run only focused structural and artifact checks locally. Remote compiler gates remain root-controlled, and a broad Lean rebuild would repeat accepted work contrary to the task.

- Verification: 8 focused structural tests passed; the original driver produced 7 expected missing-interface failures. All 9 top-level and 15 nested existing helper ASTs match the frozen original. All 45 source hashes, imports, public names, and five closures match the selected graph.
