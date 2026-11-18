# P5.6 → h34: literal MAX retention makes Q80 selected anchor deterioration vanish

Date: 2026-11-18 (Asia/Shanghai).
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Exact predecessor: `e0bd02fadfa716a111dd954a4cfbe589be7e1135`.
Manuscript remains `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Concrete mathematical improvement

The previous packet `Part5OriginalH430ClippedAnchorRecovery` kept a potentially positive effective Q80 upper-cell deterioration. This packet rechecks the *actual* old-table decision and finds a stronger result: `Part5OriginalH430DecisionProvenance.iterate_le_succ` already derives

`iterate k true i ≤ iterate (k+1) true i`

for the actual P2Selected430CausalOccurrenceExporter iterate from maximum-with-retention (not a P2 alternative simulator). Because decoding by the unchanged positive `2^80` preserves order, each upper fixed-cell read is nondecreasing and `actualUpperCellDrop k i = 0`. Hence `effectiveAnchorRise k i z = 0` for every reference z, without using a smallness assumption or monotonicity of F.

This vanishes for the original W1 anchor and the W2 endpoints with their preserved 4:1 weights, all 106 action indices, and each actual selected Fin occurrence and positive history mark. The old `bankSelectedBackwardVariationPayment` is also exactly zero.

The previously written clipped balance now yields the **exact** selected identity

`bankSelectedPositiveAnchorPayment + bankSelectedAnchorRecovery = bankSelectedSeedAnchorPayment`.

The improved frozen 430-root consumer has BOTH original complete per-product/outer-Q80 floor credit and actual anchor recovery on the **LEFT**, but *no* deterioration on the right. The same true predecessor CLOSED-CELL premise remains explicit and unproved. The reference F remains the original comparison function. No new PP/same-rho/count licence is assumed.

## Scope and limitations

No analytic seed smallness is established: the zero-iterate anchor mismatch may be substantial. There is no proof of full base/fixed/switched/seed/floor CLOSED-CELL induction, no quantitative Buchstab strict-prime source, no full U3/U4 counting/root 7/2 identification or rejection-lane ownership, no signed Euler/native-history control or shared nested 430+11 realisation. These are manuscript-internal debts, not externalized assumptions.

The existing `iterate_le_succ` theorem is itself in a source-only import chain without a successful pinned Lean compile. This new module is therefore a **candidate formal proof**, not a verified theorem. No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` escape was added. It changes no production file, no P1.4/P3.6, no CI, parameters, norm, or frozen manuscript.

## Validation and handoff

The h34 branch was verified to equal the exact predecessor and showed zero queued and zero in-progress Actions at write time. The local runtime has git but no lean/lake/elan, and native git cannot resolve github.com; the original source-only import closure is not staged. GitHub connector writes source files but does not provide a targeted Actions workflow dispatch. All declarations are **UNCOMPILED**, kernel replay/audit and inherited finite guards **UNEVALUATED**. Static token and delimiter checks are not Lean evidence.

NEXT: stage this module with fixed original import closure; compile it and direct dependencies with the pinned toolchain (increase memory as needed rather than imposing 4 GiB), fix any genuine Lean errors. Then compute/pay the actual zero-iterate positive anchor mismatch and full seed, and prove CLOSED-CELL/physical Buchstab/base and original count/PP/same-rho obligations. Do not generate more artificial deterioration ledgers.

**完整h34稿内证明仍未闭合。**
