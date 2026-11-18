# P5.6 → h34 — physical projected key collisions without receipt identification

Date: 2026-11-18.
Dedicated branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Confirmed prior HEAD: `88644f30d70c1bed206efb41bd02ebad3b32f0fc`.
Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Fixed Lean: `v4.33.0-rc1`; Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
STATUS: SOURCE_ONLY / UNCOMPILED / UNEVALUATED / COMPLETE_H34_OPEN.

## Actual manuscript-internal increment

New `Part5OriginalH430CrossSourceProjectedCapacity.lean` follows the
retained-vs-failure *receipt* separation of 88644f30. It introduces a
projection for genuinely retained U3/U4 q/tag receipts into the literal
physical Q and their least ordinary-Rosser-compatible rank-two factor,
and then compares those numeric keys to the existing actual-Q
first-excluded failure key fibres.

1. A retained projected key exists on the true retained source and
   comes from a prime divisor of the literal q and a real ordinary
   rank-two frontier witness.
2. Retained projected key fibres preserve the original physical Q,
   never replacing U3 and U4 physical Q by a free globally shared Q.
3. Even where numeric (Q,p,ell) keys coincide, retained and failure
   q/tag receipts remain disjoint, with identical Q but distinct
   literal receipts; their first-compatible versus first-excluded
   history meanings remain distinct.
4. Arbitrary signed q/tag weights and cardinalities split exactly
   across the two source fibres at a numerical event key.
5. On every actual failure key, the exact combined receipt count is
   one plus the old failure-key collision overhang plus ALL retained
   receipts with the same projected key.
6. A failure key that also has a retained projected receipt has
   strictly more than one joint receipt. This is a conditional
   capacity obstruction, not a demonstration that the overlap occurs
   or that its historical mass is payable.

No root-7/2 count bound, q-to-Fin owner, Buchstab payment, or h34
consumer is inferred by projecting labels. No new external analytic
theorem was written or reclassified. No P1.4, P3.6, CI, or production
source was modified.

## Engineering and validation

GitHub branch HEAD was read at `88644f30d70c1bed206efb41bd02ebad3b32f0fc`; no active workflow run
was found on this branch. Existing workflow failures apply to other
older commits and do not validate this new file. Runtime has git but
no `lean`, `lake`, `elan`, and does not have the held, pinned
source-only import closure installed; native github.com DNS also
fails. Static source inspection is NOT Lean parsing or compilation.
No kernel replay, transitive axiom audit or finite certification was
performed. No downstream node may be marked green.

## Remaining manuscript-internal obligations

- Existence / nonexistence and quantitative capacity of genuine shared
  projected event keys, as distinct from literal receipt overlap;
  first-compatible vs deeper first-forbidden history owner binding.
- q/tag-to-actual-`Fin` and full/selected/inherited correspondence,
  original U3/U4 count weights and root 7/2 budget, all rejection lanes.
- Strict-prime Buchstab / retention physical positive-source payment,
  complete CLOSED-CELL induction, seed/fixed/switched/base/floor.
- Signed Euler residuals, PP/same-rho instantiations, native-history,
  integral–Theta–count and the single nested 430+11 refinement.
- Stage pinned import closure, compile and kernel replay, audit
  transitive axioms and evaluate finite certificates.

Next action: construct the actual selected-history `Fin` relation for
the two projected lanes and bound per-history-key capacity, preserving
the first-compatible / first-excluded distinction; restore pinned
incremental compilation when a proper Lean environment is available.

**Full h34 manuscript-internal proof remains OPEN.**
