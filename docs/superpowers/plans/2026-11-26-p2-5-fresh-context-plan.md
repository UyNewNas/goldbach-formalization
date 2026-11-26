# P2.5 Fresh Context Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox syntax for tracking.

**Goal:** Resume the four Cell00 consumers using exact recovered accepted bytes and a new honest current-context receipt.

**Architecture:** Keep v7, recovery and historical evidence immutable. A separate v8 driver records the five bounded archive gaps, captures current context, normally rematerializes only missing exact objects, then applies the unchanged four-consumer acceptance gates.

**Tech Stack:** Python standard library; existing pinned Lean, leanchecker, mathlib and Git publication bindings.

**Spec:** `docs/superpowers/specs/2026-11-26-p2-5-fresh-context-design.md`.

## Global Constraints

- This is the root assistant's implementation choice under existing authorization, not user approval of new documents. Root handles implementation/publication/execution; this task creates documentation only.
- Keep old runners, selections, receipts, proof sources and five missing snapshot identities unchanged. No fabricated old time values or old v7 success claim.
- Keep nine ordered providers, exactly 5,312 resolved external modules and 10,624 companions, all 15,940 runtime pins, 14 witnesses, and exact source/owner/project-object identities.
- Reuse 31 available objects; normally build only the unresolved subset of the unchanged ten-module whitelist. Require each output's original SHA256; stop on mismatch without expanding replay scope.
- Keep the spec's exact strict flags, 600-second stages, 320-MiB startup/256-MiB per-stage reserves, full post-stage freeze checks, and all four-consumer normal/kernel/owned gates. `Q96_proved = P2_5_proved = false`.

## Review Focus

- A sixth missing historical file or a wrong tuple masquerading as an allowed envelope must fail (Task 1).
- Correct module counts with a shadow provider, changed companion or changed bytes must fail (Task 2).
- A cached object selected for compilation, or a mismatching new object offered for reuse, must fail (Task 3).
- Mutated linked input after a stage, or an incomplete private/generated inventory, must fail (Task 4).
- Reused historical success, new normal work, archive gaps and new acceptance must remain distinguishable in the receipt (Tasks 3–5).

---

### Task 1: Bind the narrow historical exception

**Files:** Create `docs/verification/20261126-p2-5-resumed/run_cell00_four_consumers_v8.py`, `docs/verification/20261126-p2-5-resumed/cell00-fresh-context/FRESH_CONTEXT_SELECTION.json`, and `docs/verification/20261126-p2-5-resumed/cell00-fresh-context/test_fresh_context.py`.

**Interface:** `validate_history(selection: dict) -> dict` returns the original validated owner/receipt data and the exact missing-envelope tuples. It reads published inputs and never repairs receipts.

- [ ] Pin the unchanged v7/recovery sources and selections, original receipt/source/owner/object/log/inventory identities, and exactly five path/size/SHA exceptions from `EXTERNAL_SNAPSHOT_BLOCKERS.json` into the new publication-bound selection.
- [ ] Port the complete historical acceptance checks. Separate only absent envelope availability/content checks; validate their expected descriptors and all remaining metadata/available-object pins. The ten approved missing objects remain pending Task 3; any other missing non-object input stops. Preserve failed/pending aggregate and owner statuses.
- [ ] Keep `strict_commands`, `modern_owner`, `legacy_owner`, `verify_reuse_validation`, `verify_container_objects`, the 296 private scoped-simp bindings and exact 544-name Payload inventory. Preserve the full `read_audit` contract.
- [ ] Add targeted offline regressions that accept precisely the five known absent envelopes, reject a sixth missing file or wrong hash/path, and reject altered old owner commands/declarations. Record the exact retained-check/exception mapping for independent review.

### Task 2: Capture an actual isolated current context

**Files:** Extend the new runner/selection/test file from Task 1; runtime outputs stay under fresh `p25-cell00-four-consumers-attempt008`.

**Interface:** `capture_context(selection: dict, output: Path) -> dict` returns the newly written snapshot descriptor; `check_context() -> None` rejects any frozen-input or resolution change.

- [ ] Verify clean exact publication, absent output root, real pinned toolchain and space. Keep plan mode read-only; only execution captures all nine provider roots, exact 5,312 module resolutions/10,624 companions, sources, witnesses and available historical pins with real current timestamps.
- [ ] Compare every current module/object/companion record with the preserved accepted upstream inventory and old frozen hash dictionaries. Runtime hash matches do not replace provider/companion resolution. Keep archive gaps separate and do not list their unread old paths as verified new frozen inputs.
- [ ] Test duplicate providers/shadow objects, changed companion sets, equal-count wrong module sets, and a missing runtime pin. No Lean is needed for these boundary fixtures.

### Task 3: Rematerialize only missing historical objects

**Files:** Extend the same new runner and targeted tests.

**Interface:** `rematerialize_missing(selection: dict, context: dict) -> list[dict]` records only new normal stages; existing accepted owner dictionaries remain separate and unchanged.

- [ ] Use the completed P3 inventory and actual restored files to select the unresolved subset of the ten pinned modules. Link every available exact object into the isolated library; no accepted available object may be a compiler output target.
- [ ] Traverse the full 41-object DAG topologically before filtering to missing modules; retain dependency checks through available intermediate objects. Use exact sources/strict commands. After each successful normal stage, recheck the full context and require original output SHA256/empty companion identity before freezing or admitting that object.
- [ ] Test cached-owner compilation rejection and a mismatching output: stop before installing/admitting it, preserve its failed new-stage record, and do not enqueue wider replay work. Preserve no-overwrite and symlink checks.

### Task 4: Retain all four consumer gates

**Files:** Extend the new runner/tests; add `docs/verification/20261126-p2-5-resumed/cell00-fresh-context/INDEPENDENT_REVIEW.json` after actual review.

**Interface:** Existing v7 `read_audit`, helper checks, closure checks and stage semantics remain the acceptance contract, with attempt008 output paths and the new context descriptor.

- [ ] Run the four original selected consumers in order with normal, stock independent kernel, and complete owned-audit stages. Keep all private/generated declarations, exact inventories/closures, the Parse helper checks and the original allowed-axiom set.
- [ ] Recheck all frozen inputs and resolution after every stage and at finalization. Record actual commands/logs/exits/timeouts and new dependency normal work separately from historical reused gates. A zero dependency-compilation counter remains valid for the consumer phase only; the aggregate records the rematerialization stages.
- [ ] Add focused failures for post-stage linked-byte mutation and a missing private/generated declaration. Obtain independent comparison against all old checks, including final assertions that must now truthfully record the new normal stages.

### Task 5: Publish and execute the concrete delivery

**Files:** Publish only the new reviewed code/selection/evidence and the two documents; store actual receipts/logs under a fresh verification evidence directory after execution. Existing compiled object payloads remain external.

- [ ] Root checks out the exact new publication on P3, uses existing bootstrap/exact payload delivery as needed, and runs the unchanged published recovery `--restore` in a new recovery directory. Validate its new receipt; the five unavailable envelopes remain explicit.
- [ ] Run the new driver's read-only preflight/plan first. Require no unresolved non-object input beyond those exact envelopes, at most ten approved missing objects, exact current context, enough disk, and a nonexistent attempt008 root.
- [ ] Execute published exact v8 bytes with pinned runner/selection SHA values. On any mismatch or failed stage, retain the truthful partial evidence and stop; on full success publish the new receipt and bounded consumer status only. Never announce v7 recovery or P2.5 completion from this attempt.

## Verification scope

Do not rerun settled recovery tests, remote inventory scans, accepted compilation,
or accepted replay/audit merely to implement this adaptation. Run the targeted
new boundary tests and the required new cloud stages. Final handoff includes
publication/runner/selection hashes, actual restored/rebuilt/reused counts,
the five archive gaps, new context hash, stage receipts and remaining blockers.
