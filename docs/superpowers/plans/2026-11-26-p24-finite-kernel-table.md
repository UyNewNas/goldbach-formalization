# P2.4 finite kernel table Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox syntax for tracking.

**Goal:** Prove the unchanged archived-total equality using a privately computed table whose total lookup is proved equal to the original Q80 source table.

**Architecture:** A Std.TreeMap.Raw stores the same nodeUpdate outputs at explicit increasing natural keys. Generic WF and total lookup invariants justify replacement only inside the proof. The original Array source, all public theorem types and the final canonical checker remain unchanged.

**Tech Stack:** Lean 4.33.0-rc1 at 62eed1db4d67327ec8120be05f1a1b0847d74561; locked Std.TreeMap.Raw; existing Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**Spec:** docs/superpowers/specs/2026-11-26-p24-finite-kernel-table-design.md

## Global Constraints

- Existing authorization is to continue and complete P2.4; this is a reversible internal proof repair.
- Keep the full 324-module project closure and ordered fingerprint c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f.
- No changed numerical constants, original computational definitions, public theorem types, resource gates or accepted prerequisite sources.
- No sorry, admit, new axioms, native_decide, unsafe proof or stored numerical evaluator.
- First update index 1; default initialNode; full 12 * 16384 updates.
- P2 task31eb22ecec1844cba7f6745d8c318e49 stays intact while the generic proof is prepared.
- Prototype work is isolated and carries no production acceptance.
- The original A gate and complete later owned inventory audit decide acceptance.

## Review Focus

- Query indices outside the inserted prefix must retain the original default; the refinement is a total function equality.
- Insertion comparison is compare next i, whereas sourceState tests i = next; prove the orientation explicitly.
- The explicit index advances exactly once per insertion; no map size is used.
- Closed proof transport must use generic function equalities before specialization, avoiding original Array reduction.
- Raw map WF, all private/generated declarations and native runtime bindings remain subject to the existing checks.

### Task 1: Generic representation invariant

**Files:** Create isolated Generic.lean under a new owned P3 diagnostic directory; preserve a copy in the recovery workspace and repository evidence area.
**Consumes:** Raw.getD_emptyc, Raw.getD_insert, Raw.WF.emptyc, Raw.WF.insert, Nat.compare_eq_eq.
**Produces:** For arbitrary type, initial value and update function, a tail-recursive map builder with WF and total reader equal to the corresponding functional Nat recursion.

- [ ] Write the complete generic theorem statements and proofs, with no placeholder proof bodies.
- [ ] Compile the isolated source with the pinned Lean, -t0 -j1 -M4096 -DwarningAsError=true -DmaxRecDepth=50000 -DmaxHeartbeats=40000000.
- [ ] Repair only actual diagnostics; retain every attempt and exact output.
- [ ] Independently review the arbitrary-index and successor-count cases. A successful compile here is diagnostic evidence only.

### Task 2: Private A proof integration

**File:** ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.lean only, plus required source-evidence documentation.
**Consumes:** Task1's generic representation theorem, original nodeUpdate/sourceState, accepted tableArray_lookup.
**Produces:** Private kernelTable lookup = sourceTable and a generic fixedUpperOfD10 transport.

- [ ] Instantiate initialNode and nodeUpdate at the original grid; identify the generic functional state with sourceState.
- [ ] Define the closed map at the unchanged full update count.
- [ ] Parameterize only the dInteger10 slot in the existing tail/fixed formula, preserving literal operation order.
- [ ] Prove the formula equality with arbitrary Array input before specializing.
- [ ] Compare both original public theorem headers, archived definition, options and transport proof against the original source; retain hashes.
- [ ] Compile a bounded isolated full-source copy at original limits before promoting source. Keep all credit flags false for isolated probes.

### Task 3: Original gates and final evidence

**Files:** Existing remote-task IDs, exact task receipts, execution plan and review log.
**Consumes:** Reviewed private helpers and the actual result of direct A attempt02.
**Produces:** Only the acceptance actually established by unchanged original checks.

- [ ] If direct A succeeds, retain it and do not replace its proof merely to use the fallback.
- [ ] If fallback is needed, publish a source-only commit atomically without altering the checker, baseline or native snapshot.
- [ ] Run the original 321-symbolic prerequisite at the exact new pin, then original A with 3000-second scheduling budget and 3600-second hard limit.
- [ ] Require A 102/102, exit0, empty failed/pending and completed native postcheck.
- [ ] Continue the previously recorded B, W and complete owned-audit sequence; never substitute a prototype result for any gate.
