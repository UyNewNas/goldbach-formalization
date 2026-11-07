# P5.6/h34 — external-input and internal-dependency boundary

- Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
- Physical text: `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Latest consumed h34 baseline: `492d8a43b776967836fc15029af993ee4e7a43a1`; newly added source: `8da43e22b949525ce9fa8c754ce6142ff3f8ff99`.
- **New genuinely external analytic inputs: NONE**. No change to PNT, Mertens, BV, external distribution/prime-product theorem or permitted constants.

## Existing standard library

Lean/Mathlib finite-set filter, union, pairwise disjointness, finite sum/cardinality, Nat arithmetic (`omega`), elementary real/algebraic simplification (`ring`, `linarith`), and casts (`exact_mod_cast`) are invoked as ordinary library interfaces. No library theorem is replaced by an axiom.

## Existing manuscript-internal interfaces actually called

These are **not** claimed to be external black boxes; they are earlier source-only declarations and are not certified by this packet:

- `Part5OriginalH430HistoricalReceiverSixLanes`: original tagged `frozenOnlyBad` and `rejectedFrozenBad` declarations; new receipt-root partitions classify these separately.
- `Part5OriginalH430TaggedSourceRejections`: `rejected_original_card_split`, `rejected_original_partition`, `frozen_only_disjoint_rejected`, `raw_U34_plus_two_rejections`, original finite `frozenOnly`, `rejectedFrozen`, `rejectedOriginal`, `rawTagged`. Invoked in `original_U34_receiver_root_eight_lane_count`, `original_U34_raw_with_eight_exceptions`, `original_rejected_eight_lane_signed`.
- `Part5OriginalH430ReceiverRootFrontier`: `frozen_receiver_own_root_first_exit` and `rejected_receiver_own_root_first_exit` (actual receipt-specific rank-one history and retained-prefix failure with physical hypotheses). Invoked by both new `*_own_root_fail_has_event` declarations.
- `ordinaryRosserPrefixAdmissible` from the existing original ordinary-Rosser policy; the singleton root test appears in `rootLicensed` and actual length-two decision in `ownPolicyPass`/`ownPolicyFail`.
- `historicalRejectedEvents`, `roughPrimeUniverse`, `FirstExitDepthState` from the existing first-exit path definitions; used only in the conclusion of the two conditional event certificates.

The exact source version is the immutable preceding HEAD `492d8a4` on `chatgpt/p5-h34-request-admission-20261105`. New proofs are isolated to a new source-only directory, with imports from that pinned implementation rather than a toolchain upgrade.

## Still manuscript-internal and UNPROVED

Not externalized: original root physical/root-policy gates for every counted receipt, full/selected/inherited post-root history and owner mapping, noninjective occurrence-fibre payment, all three other receiver lanes, original selected-count weights and U3/U4 feedback, request-level Buchstab/retention and CLOSED-CELL induction, base/seed/floor/fixed/switched, manuscript-specific PP/same-rho matching, common alpha/same-Q, outer integral–Theta–count conversion, native-history error budget, and common 430+11 nested causal refinement.

## Validation

SOURCE_ONLY / UNCOMPILED / UNEVALUATED. Static text and GitHub blob checks are not Lean elaboration, kernel replay, transitive axiom audit or the finite table/certificate evaluations. No CI dispatched.
