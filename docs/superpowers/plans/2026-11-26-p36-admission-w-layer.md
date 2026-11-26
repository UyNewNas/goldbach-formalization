# P3.6 Full-word Admission and W Layer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [x]`) syntax for tracking.

**Goal:** Accept the existing original-U5 complete-word square/RootV/endpoint chain and formalize the complete W layer on the same original policy.

**Architecture:** Reuse seven existing owner modules and add one direct exact-layer module. Root freezes source and schedules one original multi-owner strict/replay/inventory gate. A small evidence adapter retains every original guard and the existing exporter bytes.

**Tech Stack:** Lean4.33.0-rc1; pinned mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; Python3; existing P3.6 verification and compiler MCPs.

**Spec:** `docs/superpowers/specs/2026-11-26-p36-admission-w-layer-design.md`

## Global constraints

- Base b3f306cc3b430fc40c3b3ec4110d323443d2f609; preserve prior27 accepted owners/414 records and their raw evidence.
- Frozen manuscript commit3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e, release2026-11-06.
- Local source authoring only; frozen cloud execution; root owns cloud scheduling.
- No new axiom/sorry/admit/native_decide/unsafe, no weaker strict lint, original driver or original inventory audit.
- Preserve original selectors, marks, policy, coefficient, signs, masks, witness order and full physical modulus.
- The numerical L5 certificate does not supply an unproved selected-policy signed-density bound.
- whole_p36_closed=false and currentVerified=false; no closed-node PR inclusion.

## Review focus

- Boundary equalities in the full W layer must be retained; universal exact iff statements cover them.
- Original pair support includes target exclusion and ordered multiplicity; finite-set identity must use that literal support.
- Fixed W changes no policy or rho; exact policy equality and signed partition retain the complement.
- Complete word squares, root V inputs and coarse auxiliary covers must not be promoted to full atom/family (S)/(F) or PP.
- Group evidence must reject missing/extra/reordered owners, mismatched source hashes, stage omissions and runtime binding drift; preserve the original single-owner receipts.

### Task1: Freeze and verify the existing source chain

**Files:** existing seven Lean modules listed in the spec; new `admission-w-layer/source-snapshots/` and `attempts/` evidence.
**Consumes:** current reviewed donor bytes and original compiler cache/report identities.
**Produces:** the same public declarations, repaired only for concrete elaboration/strict diagnostics, and an exact frozen source manifest.

- [x] Record initial source SHA and historical stage evidence. Reuse current repaired AllSource, not the older failed version.
- [x] Inspect each module's assertions against the recorded manuscript scope; retain full square/mask/word conditions.
- [x] Freeze together with Task2 and run Task4. If a diagnostic occurs, assign a bounded proof-expression fix to the responsible source only.

### Task2: Exact full W-layer mathematics

**Create:** `ImbalancedChen/P3OriginalU5FullWLayer.lean`.
**Consumes:** original dictionary `level`, `a`, `h`; original `pairSupport`/coordinates; NativeRootCover `marks`, `native_policy_at`, `actual_root_gates`; literal signed primitive row sum.
**Produces:** exact geometric iff, original finite-set layer identity, literal complement characterization, native policy/rootQ/square-gate transport and exact signed partition.

- [x] Define W through existing B(a), reusing an existing public plateau constant when suitable; prove W=90621/160000.
- [x] Prove `level_eq_wLevel_iff` for a<=u<t<h using t<h<mu and 2a>2W-1. Endpoints are10621/80000 and17293/80000.
- [x] Define `wLayer N` by those two gates on the original pairSupport. For N>=2, prove equality with marks N W.
- [x] Prove literal complement membership: supported pair and (t exponent above the first threshold or pair exponent sum below the second).
- [x] Transport existing native policy and actual root gates to this layer at unchanged b and seed W-2b.
- [x] Split original signedPrimitiveSum exactly into W-layer rows at policyAt W and unchanged original-policy complement rows.
- [x] Independent source/spec review, then original formal gate in Task4. No mirrored unit tests for universal propositions.

### Task3: Reuse proof evidence for an exact owner group

**Create:** `admission-w-layer/export_group_evidence.py` and focused `test_export_group_evidence.py`.
**Read only:** `normalized-density/export_verified_increment.py`, pinned SHA003d628292e0b1d067e9f87d3aad6b2c6f2a64db5b117e06cbe6bbf37743fcf5, and its original pinned helpers.
**Consumes:** original VERIFIED_OWNED group report, source commit, independently hashed exact owner/source manifest and original before/after runtime binding.
**Produces:** complete archive/receipt, explicit group runtime binding evidence and local verification with zero Lean invocations.

- [x] Design the smallest adapter around the previous export/verify/validation functions; leave old bytes and old receipt semantics unchanged.
- [x] Write focused real validation tests for owner omission/extra/ordering, source hash mismatch and group runtime digest drift; use an existing accepted multi-owner fixture where practical.
- [x] Preserve exact strict/replay/inventory checks, complete defining-module attribution, full source/object/import graph and historical lineage validation. Do not broaden old-writer exceptions without specific independent evidence and review.
- [x] Make runtime report/group identity explicit; never present export-time measurements as original runtime hashes.
- [x] Independently review the adapter and run its covering tests before exporting a real group.

### Task4: Original compiler gate and exact evidence recovery

**Files:** frozen source bundle, original task output and reports, accepted-group archive and receipt under admission-w-layer.
**Consumes:** Task1/2 exact source manifest and compatible compiler/cache; Task3 verified exporter.
**Produces:** verified new-owner group with retained full types/axioms and local verification.

- [x] Check available space; preserve original source, cache and run reports/logs. Clean only exact redundant task-owned copies whose durable bytes have been verified, if necessary.
- [x] Run original compile_p36_local.py on all8 targets with --build --strict-owned --verify-owned and pinned environment.
- [x] Require every owned strict compile, exact replay and complete original audit to exit0; independently bind runtime tools before/after and original report SHA.
- [x] Export and recover full bytes; verify locally using original export digests and frozen source commit; no duplicate Lean runs.
- [x] Check all old/new inventories for overlapping full names and count definitions/generated helpers transparently.

### Task5: Integration review and authorized publication

**Files:** owned scope status, next-boundary record, mathematical scope, review/evidence/publication records.

- [x] Update only proven scope and preserve remaining actual-positive-density, sparse, common-Q/complement, complete S/F and PP obligations.
- [x] Commit coherent source/evidence; generate final review package from b3f306c and use a fresh whole-branch reviewer.
- [x] Resolve findings in one bounded final fix wave and scoped re-review if needed.
- [x] Ordinary fast-forward push to the existing work branch under the user's repeated authorization; independently read back the exact remote SHA.

## Execution decisions

The existing dedicated branch is the isolated workspace. Root chooses subagent-driven implementation for the independent W-layer and evidence-adapter tasks, while keeping compiler scheduling and integration centralized. Existing precise statements, frozen manuscript and standing continuation authorization determine the scope; no new user design choice is needed.
