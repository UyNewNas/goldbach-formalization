# External inputs: P5.6 h34 original U3/U4 six-lane audit

Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes @ ba6ec11d800eccc54406490631895e174de85766, paper/source/manuscript-body.tex, blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79.
Toolchain and Mathlib remain at the unchanged repository revisions from bb0e3bee5bcca61173f4854301cfaae5ffa941d1.

NEW EXTERNAL ANALYTIC INPUTS: NONE. No PNT, Mertens, BV or positive-product theorem is added or re-proved.

Reused pinned MANUSCRIPT-INTERNAL sources and exact call locations:
- rejected_original_partition, rejected_original_card_split, frozen_only_disjoint_rejected, raw_U34_plus_two_rejections from Part5OriginalH430TaggedSourceRejections; consumed in original_rejected_six_lane_card, raw_U34_six_exception_counts, original_rejected_six_lane_signed.
- frozen_only_bad_post_root_remaining_iff and rejected_frozen_bad_post_root_remaining_iff from Part5OriginalH430PostRootRemainingExact; consumed in frozen_outside_not_remaining and rejected_outside_not_remaining.
- frozen_only_bad_post_root_first_exit and rejected_frozen_bad_post_root_first_exit from that same earlier source; consumed in frozen_failed_has_event and rejected_failed_has_event. These depend on original historicalRejectedEvents / genuine firstExitDepthFrontier, which remain internal and uncompiled.

Mathlib basics reused: Finset.filter, Finset.union and disjoint sums/cards, real casts and arithmetic, omega, ring, linarith, classical decidability. No new axiom, target-equivalent input, unsafe proof or replacement of the native counts.

Still INTERNAL and unproved: per-receiver actual selected-history frontier map, full/selected/inherited filters and event multiplicities, physical exceptions and signed payment, source count-to-generated request feedback, closed-cell induction, real seed/base/floor, PP/same-rho instantiation, native-history and common 430+11 refinement.

Verification: SOURCE_ONLY / UNCOMPILED / UNEVALUATED. No kernel replay, transitive axiom audit, finite certificate execution or CI dispatch.
