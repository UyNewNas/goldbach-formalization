# P3.1 actual source lanes implementation plan

> **For agentic workers:** Use the existing isolated worktree, local source edits, independent mathematical review, and exact-source verification. Root coordinates compiler and publication actions.

**Goal:** Connect the real finite reciprocal source and existing primary decomposition to the accepted common Poisson kernel lanes.

**Architecture:** Reuse the accepted P3.4 source suppliers with explicit import/owner adapters; recover the original completedPiece source identities; derive the actual medium-carrier common-J dictionary.

**Tech Stack:** Lean 4.33.0-rc1 / commit 62eed1db4d67327ec8120be05f1a1b0847d74561, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, P3 compiler, existing verifier.

**Spec:** `docs/superpowers/specs/2026-11-26-p3-1-actual-source-lanes-design.md`.

## Global constraints

- Preserve the frozen 1106 manuscript and the original declarations' mathematical meaning.
- No sorry, admit, new axioms, native_decide, unsafe, or proof of external analytic inputs.
- Preserve all old baseline sources and the four prior accepted module sources.
- Existing accepted supplier proofs are reuse, even if integration requires recompilation.
- Local code editing only; cloud synchronizes and compiles; never modify another conversation's worktree.

## Review focus

- y=0 keeps all m; m=0 is separated only inside the nonzero-y part.
- Empty carriers and J=0 do not create a spurious source or omit an endpoint.
- Residue sign, y sign, and m sign are independent; negative Fourier arguments remain negative.
- A single J, interval and coefficient family are retained throughout each complete source sum.
- Actual source data are preserved; no new OriginalData stand-in or spectral product identity is introduced.

## Task 1: Reuse the newly accepted P3.4 suppliers

**Files:** selected `ImbalancedChen/Part3LiteralReciprocalSource.lean`, `Part3ActualNonzeroSourceCore.lean`, and the necessary primary-dyadic provider closure; metadata under `docs/part3-distribution/p31-actual-source-lanes-20261126/`.

**Interfaces:** preserve the exact full names for Source, output, weight, beta, carrier,
actualNonzeroSource, keys, block, and finite_source_assembly. Existing repeated declarations
are obtained from their already accepted owners in this branch.

- [x] Compare current branch state and the newly published P3.4 source and acceptance evidence.
- [x] Select the minimal supplier closure and record exact source hashes and ownership adapters.
- [x] Verify all retained supplier theorem bodies and statements are unchanged.

## Task 2: Recover the literal completed source and common lanes

**Create:** `ImbalancedChen/Part3ActualCompletedSourceLanes.lean`.

**Consumes:** accepted completedKernel_eq_m_lanes and the existing literal finite-source APIs.
**Produces:** original completedPiece and its exact source/joint-beta/three-sign identities;
a finite source composition with zero, common positive/negative m blocks and complementary tail.

- [x] Recover original source slices with byte identities; keep original definitions and statements.
- [x] Add only the required composition of those identities with the existing kernel decomposition.
- [x] Review all five mathematical edge cases above and run strict compilation.

## Task 3: Specialize to the actual medium carrier and primary blocks

**Create:** `ImbalancedChen/Part3ActualModeCommonPoissonLanes.lean`.

**Consumes:** actualNonzeroSource(e,D,delta,g,l,Z,residueNegative), its literal raw carrier,
existing primary keys/blocks, and Task 2's completed source identities.
**Produces:** the actual finite completed-source dictionary with its y=0 term and the complete
primary/sign/dyadic sum, each using one explicit J and the original lambda/omega.

- [x] State and prove the exact finite identity with original carriers and explicit zero/tail terms.
- [x] Obtain independent source and mathematical review; resolve concrete findings.
- [x] Compile the integrated target and required adapted providers without rerunning old acceptance.

## Task 4: Exact-commit acceptance and GitHub delivery

**Modify:** `verification/verify_part3_continuation.py` only for the new group and source bindings.
**Create:** exact-source intake/closure manifest, formal receipts, declaration classification, and final scope record.

- [x] Preserve existing verification helpers, old groups, baseline checks, and the three-axiom whitelist.
- [x] Publish the concrete source commit on work/p3-1-proof-20261126.
- [x] Run the strict/replay/inventory/source-object gate on that exact commit and retrieve complete evidence.
- [x] Record fresh declarations separately from reused supplier declarations and previous acceptance.
- [x] Publish the evidence commit and verify its remote commit/tree/ref; leave a clean local tree.

The accepted source is `6840a3c4d4f3e67f076e55d70fce9851ab7615c9`.
P3 task `94f0edc5f5944c899af23f33ce023221` passed all 52 stages, with 164 complete
environment declarations: 130 named source declarations and 34 generated declarations.
The named sources comprise 109 reused suppliers, 9 recovered declarations and 12 new
composition/support declarations. The evidence-only delivery and exact scope are recorded in
`docs/part3-distribution/p31-actual-source-lanes-20261126/ROUND_COMPLETE.md`.
This completes this plan's finite-source increment, not all of P3.1.

## Execution rulings

The repeated user instruction to continue and publish authorizes execution of this bounded
continuation. No extra approval pause is introduced. Lean proof checking is the semantic test;
already accepted proofs are reused, and intentionally broken duplicate tests are not added.
Only concrete compatibility failures justify repeated probes. All task receipts and rulings
are retained with the source provenance and final verification results.
