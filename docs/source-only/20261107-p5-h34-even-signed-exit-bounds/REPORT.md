# P5.6 → h34 — even-N sign and quantitative size of the genuine historical exit

Date: 2026-11-07 UTC.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Verified preceding remote HEAD: `8c6d078925357d5381c67f5da0638c6792299e24`.
New mathematical source commit: `ac8fa47005eb55f9d13d29488e1a9dd38c9d9510`.
Lean source blob: `ecb6a7b971b0fb09d61a9b33f80c19873ba7c175`.
Module: `Part5OriginalH430EvenSignedExitBounds.lean` (331 inserted lines, 4 public theorem bodies and 5 private theorem bodies).
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` (blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).

**PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED.** 
The source was committed to the existing task-owned h34 branch, without modifying production Lean files, other tasks' files, CI, toolchain or the fixed manuscript.

## True new mathematical step

The previous `TrueReceiverWeightedExit` packet gave the exact identity

    rejected_original_weight =
      six_non_event_weight
      + sum_distinct_keys(actual_rank_two_signed_exit)
      + sum_distinct_keys(true_q_tag_receipt - actual_rank_two_signed_exit).

It correctly left the last sum **UNPAID**. The present packet derives its actual sign and an upper bound in the manuscript's original **even-N** case. This uses the real historical recursion and Euler suffix, rather than inserting a hypothetical positive payment.

1. `historical_remaining_member` traces every enumerated first-excluded event's `remaining` list back to its starting ordered rough-prime carrier. No fictional suffix or owner appears.
2. `even_rough_euler_factor_bounds` and `even_rough_euler_product_bounds` use the original roughPrimeUniverse predicate (`q.Prime`, `¬ q ∣ N`), plus the manuscript fact `2 ∣ N`. Thus no actual remaining q is 2; each is ≥3, and each Euler factor and the complete suffix product lie in [0,1].
3. `original_fourth_key_primes` obtains BOTH genuine primes p and ell from the existing frozen-only and rejected-frozen tagged arithmetic sources. It does **not** declare the quotient receiver q prime. `original_fourth_key_mass_nonneg` then proves nonnegative genuine rank-two mass.
4. `original_fourth_key_signed_exit_interval` combines the previous actual unique historical event and its exact negative Euler expression with those elementary bounds. For every TRUE event key k in the two genuine fourth lanes, with z0≤cap and 2∣N,

       -originalEventMass(k) ≤ actualRankTwoSignedExit(k) ≤ 0.

   This is conditional on the actual even-N and finite-cap geometry, not an arbitrary new sign axiom.
5. `original_fourth_key_receipt_gap_interval` and `original_fourth_total_receipt_gap_interval` preserve every q/tag-dependent weight and all distinct event keys, proving the **quantitative direction**

       receipt(k) ≤ receipt(k) - actualRankTwoSignedExit(k)
                  ≤ receipt(k) + originalEventMass(k).

   No sign assumption about arbitrary receipt weight w is required, because the direction is supplied by the actual Euler correction.
6. `original_unit_fourth_receiver_gap_lower` specializes the weight to the real U3/U4 unit count and reuses the original two-source key-fibre identity. It obtains

       card(true_frozen_fourth_lane) + card(true_rejected_fourth_lane)
          ≤ sum_distinct_keys(unit_receipt(k) - actualRankTwoSignedExit(k)).

   The two lanes and every (tag,p,q) occurrence remain distinct; one event key is not charged once for each q.

**Important sign consequence:** a negative actual rank-two historical correction does *not* cancel a positive rejected arithmetic receiver. On the contrary, the gap in the prior algebraic identity is at least the actual unit fourth-lane count. This diagnoses an unavoidable manuscript-internal ownership/sign-payment problem. It is **not** a proof that any original receiver or positive q-fibre has been paid, nor a refutation of the full manuscript theorem.

## What remains open, in actual dependency order

- Determine the true full/selected/inherited owner and correct sign placement of the rank-two historical correction in the original count inequality, rather than treating the algebraic signed gap as a positive payment.
- Pay the extra q/tag fibres and cross-lane overlaps with real historical occurrences or demonstrate their correct filtering. The same (p,ell) key has one rank-two event in the fixed-root history.
- Pay the SIX genuine gateBlocked/carrierOutside/policyPass non-event lanes, with original selected-count and root-sieve semantics.
- Connect complete original U3/U4 selected-count, root weights and root pre-sieve gates to the actual generated history; prove the CLOSED-CELL predecessor induction, base/switched/seed/floor and true feedback integral–Theta–count correspondence.
- Complete manuscript-internal PP/same-rho, native-history proper/equality/inherit, and one common nested causal 430+11 refinement.
- Install sources under existing versioned ImbalancedChen dependencies, compile, kernel replay, audit transitive axioms and replay the held numerical430/finite guards.

## Source-only verification and status

- GitHub compare `8c6d078...ac8fa470` confirmed exactly one newly added 331-line Lean source, zero deletions.
- Remote file readback confirmed source blob `ecb6a7b971b0fb09d61a9b33f80c19873ba7c175` and branch HEAD `ac8fa470...`.
- Text-only forbidden proof escape-token and bracket balance checks passed before upload.
- **NOT RUN:** Lean parsing, elaboration/build, kernel replay, transitive axiom audit, independent mathematical review, CI, held numerical430 certification or any finite guard. All are UNEVALUATED. There is **no green formal credit**.
- No new external PNT/Mertens/BV or other analytic theorems; no new custom axiom, sorry/admit, target-equivalent premise, unsafe/native bypass, CI dispatch or toolchain changes.

**Next precise action:** trace the genuine `historicalExitValue` orientation through the original U3/U4 full/selected/inherited count identity, using this sign interval to prevent a false cancellation. Then identify which of the actual six non-event lanes can be filtered or paid by legitimate historical owners. Do not repeat the bare-key or same-q ledger as a new advance.

**Complete h34 manuscript-internal proof remains OPEN.**
