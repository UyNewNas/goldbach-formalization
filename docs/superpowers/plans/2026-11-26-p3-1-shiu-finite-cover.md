# P3.1 finite-cover reconstruction and caller intake

## Goal and authorization

The user explicitly authorized searching the other conversations' work, then reimplementing the missing
FiniteCover if necessary, and continuing P3.1. The manuscript, Lean stack, external-input boundary and
existing caller are already specified. No further design-permission pause is needed.

## Chosen construction

Use shellBase j = 2^j, H = min(T,2^j), X = max(A,2^j)+kH, with half-open natural windows.
Two windows cover each positive closed-interval/shell intersection when B-A <= T and T > 0;
retain the caller's eight-window index and prove a total-length upper bound.

An exact original-provider recovery was considered first. Its bounded searches have not recovered
the old source bytes. Reconstructing unknown bytes or assuming the desired cover would not meet the
user's request. The chosen new elementary proof follows the frozen 1106 shifted-divisor paragraph.

## Work and gates

- [x] Inspect the uploaded caller and the frozen manuscript, and preserve the original upload exactly.
- [x] Read the original P1 task result and the disclosed new Git evidence without repeating completed searches.
- [x] Implement the actual finite cover, active-source witnesses, nonnegative-sum comparison and length budget locally.
- [x] Strict-compile the new provider and repaired supplied caller in an isolated P3 probe.
- [x] Read the rejected old verifier selector (`shiu-windows`, exit 2); add only the new group and provenance/closure bindings.
- [x] Run source-only closure checks, existing gate regressions and an independent review of the new selection.
- [x] Publish exact source `d28d340b0240dc5cd8658893d07b61637ee94aa2` and verify the two selected modules through strict Lean, bundled leanchecker and complete axiom inventory.
- [x] Read and verify the exact reports and original task output, archive all acceptance evidence locally, and record the actual P3.1 boundary.
- [x] Root publishes the prepared evidence and verifies its remote commit/tree/ref; no repeated Lean acceptance is required for this documentation step.

## Constraints

Write code locally; cloud jobs only synchronize exact bytes and compile. Preserve other conversations'
jobs and worktrees. Reuse accepted providers and the original audit logic. Keep Shiu itself and the
other manuscript-external analytic results as explicit inputs. Do not claim the unknown SignedSplit
or OverlapCover callers were tested, and do not equate this component with complete P3.1.

## Exact-source acceptance result

Combined task `c8f3589c6e604553bb5075f6c358270d` passed on the exact published source with
`shiu-windows=0`. Both strict and bundled leanchecker replay stages passed, followed by the complete
axiom inventory and final source/object checks. FiniteCover contributes 36 owned environment
declarations (24 source-named and 12 generated), and WindowGate contributes 39 (9 source-named and
30 generated). The actual axiom union is exactly `Classical.choice`, `Quot.sound`, `propext`.

Both reachable project modules are selected targets; there are no unselected project providers in
this group. Its two source/object bindings are recorded, and objects remained unchanged after audit.
This does not certify a full replay of Mathlib, recover the old provider bytes, prove primitive Shiu,
or close P3.1. Earlier probe/reconstruction metadata remains the historical source-bound snapshot.

The shared `docs/part3-distribution/p31-20261126-acceptance/` directory contains the complete checked
archive for both groups (107 environment declarations total), original task metadata/output, and
per-member hashes. Component `verification/` copies preserve the raw report, inventory and theorem
types. Later kernel-source intake is outside this accepted count and scope.
