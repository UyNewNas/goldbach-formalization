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
- [ ] Publish the exact source commit and verify the two selected modules through strict Lean, bundled leanchecker and complete axiom inventory.
- [ ] Archive the exact acceptance evidence, inspect remote commit/tree/ref, and report the actual P3.1 boundary.

## Constraints

Write code locally; cloud jobs only synchronize exact bytes and compile. Preserve other conversations'
jobs and worktrees. Reuse accepted providers and the original audit logic. Keep Shiu itself and the
other manuscript-external analytic results as explicit inputs. Do not claim the unknown SignedSplit
or OverlapCover callers were tested, and do not equate this component with complete P3.1.
