# P5.6 → h34 — genuine original U4 post-frontier exact capacity / signed q-tag ledger

Date: 2026-11-09 UTC.
Repository: `UyNewNas/goldbach-formalization`.
Isolated branch: `chatgpt/p5-h34-u4-postfilter-exact-capacity-20261109`.
Verified immediate predecessor: `304306503f8cfef8d80bea1364f7d88e23140553`.
Original task entrance: `0a3fa5aa639e74122fbef18be02f0ad6fa8a77a0` (historical only, not restarted).
Math source commit: `ea96ea0fc6b23a7f21d8695668ff937299bbfa59`.
Read-back math source Git blob: `61591c5bba7c67d2022e32d2cefd1b0c87538f75`.
Manuscript pinned at `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` (previous verified blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).
Lean: `v4.33.0-rc1`. Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Why this is the next increment

Prior packets established that true retained original U4 (p,q) yields *two* arithmetic tagged receipts at the same actual physical (Q,p,ell) slot, but exactly *one* rank-two recursive Fin occurrence with the actual selected prefix [ell,p]. The previous necessary cardinal shortfall remained a mere inequality after an arbitrary filter, and it did not identify where an additional first-excluded or filtered receipt disappears. This packet exposes the **exact zero-or-one post-filter occurrence**, isolates the **one-unit extra lost to a filter erasure**, and gives the corresponding genuine q/tag signed receipt ledger at fixed Q. It does **not** instantiate the unavailable manuscript full/selected/inherited owner predicate.

## Exact new Lean scope

New `Part5OriginalH430U4PostfilterExactCapacity.lean`: **201 lines, two definitions, six candidate theorems**. It imports the existing source-only `Part5OriginalH430UpperRankTwoPrefixCapacity` chain (which includes the true U4 retained fibre and fixed-Q Fin-list source).

1. `actualSlotPostfilterPositions` is the **literal intersection** of genuine rank-two Fin positions of the requested [ell,p] prefix and the existing `keptPositions` for an explicit Boolean filter. It does not create a new position.
2. `observed_slot_postfilter_positions_exact`: on an actually observed physical slot, the intersection equals either the singleton original list position or the empty set according to the Boolean gate at that exact position.
3. `observed_slot_postfilter_card_exact`: the corresponding cardinal is exactly 1 or 0. A second original tag cannot create another Fin occurrence.
4. `observed_slot_exact_postfilter_excess`: for a slot with at least one original receipt,
   `F.card - P.card = (F.card - 1) + (if gate then 0 else 1)`, with `F` the true retained original q/tag fibre and `P` the true kept Fin-prefix occurrence fibre. This is natural-cardinality accounting only, not an owner-payment theorem.
5. `actualU4OverlapSlot` and `actual_u4_overlap_slot_observed`: bind the actual original U4 left-tag receiver (p,q) through its chosen real second prime to the true observed physical slot.
6. `original_u4_retained_exact_postfilter_excess`: specialize the exact excess formula to **genuinely retained original U4 two-tag receipts**, obtaining the nontrivial `F.card ≥ 2` hypothesis from the earlier source, not assuming a fictitious second history position. All extra original q/tag receipts in that slot remain in `F`.
7. `original_fixed_Q_receipt_filter_signed`: instantiate the existing exact kept/erased physical-slot decomposition with the *actual signed inner q/tag receipt sum* for each slot, preserving arbitrary individual q/tag weights and the erased lane.

The original U3/U4 q/tag multiplicities, physical Q, selected-prefix order, original path histories, P5 constants (c/K, root norm 7/2, row norm 12), true alpha, frozen cutoff 11/5, all-action count induction, and 430+11 causal reserve are not modified. No artificial receipt-to-Fin injection, fresh q-positive bound, target-equivalent owner assumption, PNT/Mertens/BV rewrite, or new axiom is introduced.

## Validation and ownership

The connector has authenticated push access to the repository. It created **a new isolated h34 branch** rather than modifying a potentially concurrently used earlier branch. GitHub read-back verified the mathematical source blob `61591c5`; a real commit comparison from `3043065` to `ea96ea0` reported exactly one new 201-line Lean source file, zero deletions. Source-token checking found no `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide` proof escape.

In this execution environment, `lean`, `lake`, and `elan` are absent from PATH, and `git ls-remote https://github.com/UyNewNas/goldbach-formalization.git HEAD` failed with DNS `Could not resolve host: github.com`. Source-only predecessor modules were not installed as a complete production import closure. Thus **NO Lean parser/elaborator check, Lake compile, kernel replay, transitive-axiom audit, CI compilation, or numerical430 certification occurred**. Static checks and Git hash consistency are not proof verification. All new declarations are UNCOMPILED candidates; no green credit. Existing CI, toolchain, frozen manuscript, P1.4/P3.6, master, and all other source files remain unmodified. No force push or merge.

## Exact remaining manuscript-internal obligations

- Identify and prove the actual **full/selected/inherited** manuscript masks and owners at the same physical Q, including correct index, stage, z0, root count weights and real precursor history. The arbitrary post-frontier `keep` in this packet is NOT this identification.
- Convert each original arithmetic q/tag receipt to legitimate actual historical payments or explicitly retain its residual. The cardinal excess after a rank-two prefix filter is not a signed financial cost or global small H430 bound.
- Prove sufficient positive source sieve occupancy and weighted actual `Phi`, original q-to-Fin capacity (including other q at one slot and the U4 two-tag collision), the true H430 **small upper** bound for unpaid receipts, and all six rejection lanes.
- Prove first-excluded signed Euler suffix with true signs, all-action CLOSED-CELL count induction, correct base/switched/seed/floor, feedback weights to outer integrals, PP/same-rho and native-history mass.
- Close the common nested 430+11 causal refinement with exact c/K/reserve ordering, install full pinned source-only import closure, compile, kernel replay, audit transitive axioms, replay numerical finite certifications.

**Next precise step:** extract the actual manuscript full/selected/inherited predicate from the existing historical owner, prove it agrees with a concrete `keep` on each original observed fixed-Q rank-two position (or prove the erased discrepancy), and then attach the resulting *signed q/tag* lost-fibre ledger to the first-excluded and owner capacity accounts. Do not call `F.card - P.card` a paid receipt or a proven upper bound.

**完整h34稿内证明仍未闭合。**
