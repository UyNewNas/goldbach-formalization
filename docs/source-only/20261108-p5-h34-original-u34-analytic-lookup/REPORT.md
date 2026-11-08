# P5.6 / h34 — actual original U3/U4 receiver-indexed H430 lookup

Date: 2026-11-08 UTC.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Incoming remote HEAD: `b376eb1189a48a2346a6f96f4035d76cd839760c`.
Math source commit: `2cf54c93ed0ed7adbdd1fc5cfbe625b0927f9a7e`.
Math source blob: `64805703e0e9ba06de90135c37881424238e709a`.

**PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED.**

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`;
body `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
The manuscript's "Finite defects and actual descendants" gives the finite 430 H/h feedback, while "The selected eleven occurrences and paired accounting" fixes U3/U4 upper H430 at `max(2,L/a)`, signed `-1/4` per label, with 248 elsewhere unchanged.
Lean v4.33.0-rc1 and Mathlib e4c91783 remain unchanged.

## Why this is a separate, non-duplicative increment

The preceding `20261108-p5-h34-rank-two-owner-obstruction` proved a *conditional* inability to inject two true retained U3/U4 q/tag receipts into a single fixed-Q rank-two Fin position. Older `true-upper-u34-phase` and `true-upper-clamp-integral` packets described the continuous genuine U3/U4 upper H430 coefficients but did **not** evaluate them on the original source's selected p.
This increment connects those two previously separate objects: the **actual original** `(tag,p,q)` finite source and the genuine `H430Numerators` main-envelope lookup, without identifying the lookup with the arithmetic count.

## 131 lines, 1 definition and 5 candidate theorems

`Part5OriginalH430OriginalU34AnalyticLookup.lean`:

1. `actualTaggedUpperH430Lookup`: evaluate `U3H430Coefficient` or `U4H430Coefficient` on the actual `primeCoordinate N p` of each original tagged receiver, keeping each original q position.
2. `original_u4_pair_upper_coordinate`: obtain the **strict** `Ico a (59/250)` membership directly from `originalPairs N .U4` and the original prime selector, not a new root-domain premise.
3. `original_u4_pair_true_upper_H430_equal`: on each original U4 (p,q) prove the two original U3/U4 genuine H430 upper table lookups agree.
4. `original_u4_pair_both_true_H430_formula`: instantiate both lookups to the actual un-clamped main residual `mainResidual/a`, `upperRoot H430Numerators` and the true `branchWeight`, not H248, lower h, or the U3 tail.
5. `original_U34_actual_H430_source_lookup_split`: exact **finite source-indexed lookup** equality: U3-exclusive p,q values + 2 times U4 p,q H430 lookup. This is not a finite arithmetic COUNT identity with an integral.
6. `original_U34_actual_H430_source_signed_quarter`: multiply by the unchanged negative Chen root quarter: U3-exclusive `-1/4` and actual shared U4 lookup `-1/2`. No positive or signed historical payment is inferred.

The proof uses previous genuine original source partition, `U3_eq_main_on_U4`, `u4_entire_phase_true_H430`, finite sum conjugation, and ring arithmetic. No new axiom or target-level proof assumption.

## Mathematically essential non-equivalence

For an original retained U4 receiver the two labels have equal H430 table values, and previous packets gave equal actual physical Q/ell slots. Yet the original integer q source, one finite historical root mark, and continuous H430 coefficient are three DIFFERENT objects. This packet does **not** equate the sum of H430 lookups over original q with either the true count `U3+U4` or the integrals of those coefficients. Such a correspondence needs the original asymptotic distribution and complete selected-count owner/filter, not a combinatorial sum lemma.

## Verification / scope / next action

The math commit was constructed as a new isolated source-only file, with a fast-forward ref update guarded by the expected prior HEAD. Static forbidden escape and comment-balance checks passed. No Lean elaboration/compilation, kernel replay, transitive-axiom audit, independent review, numerical430 evaluation or CI dispatch. Inherited certificate verification remains **UNEVALUATED**; no green credit.

Only this isolated h34 source-only directory is changed; no edits to P1.4/P3.6, production modules, manuscript, dependency locks or workflows, and no merge.

Next: locate the true upper H430 `full/selected/inherited` count consumer, actual z0, historic depth, physical root weight and source-to-Theta analytic **inequality**, then use this actual U3/U4 lookup as a table-value annotation. Keep outstanding Buchstab/retention, all-action CLOSED-CELL, signed Euler rejection lanes, PP/same-rho, and common430+11 obligations visible.

**完整h34稿内证明仍未闭合。**
