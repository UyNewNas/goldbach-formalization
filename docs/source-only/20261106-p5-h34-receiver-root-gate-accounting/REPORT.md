# P5.6 → h34 — receiver-indexed root-gate and eight-lane original rejection ledger

Status: **PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED**.

Repository: `UyNewNas/goldbach-formalization`; branch `chatgpt/p5-h34-request-admission-20261105`.
Previous verified HEAD: `492d8a43b776967836fc15029af993ee4e7a43a1`.
New source commit: `8da43e22b949525ce9fa8c754ce6142ff3f8ff99`.
New source blob: `fdac0a2d8b2d962a7edd1cfe59ea983e91549c9b`.
Manuscript remains pinned to `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. No new manuscript version or constants.

## Verified additive scope

New `Part5OriginalH430ReceiverRootGateAccounting.lean`: 347 source lines plus final newline, five definitions, eleven theorem proof bodies (including three private disjointness lemmas). Previous receiver-root frontier and original six-lane sources were read before this change. Only the new h34 directory is written.

Prior work supplied a receiver's true rank-one historical frontier **conditional** on physical and root-policy gates. The earlier six-lane theorem instead classified all original U3/U4 rejection receipts relative to one arbitrary common frontier. Neither alone accounted for the receipts whose **own roots** fail admission.

This packet makes the distinction exact using original `TaggedReceiver` finsets. `rootLicensed` requires the actual arithmetic prime not to divide N, its strict root cutoff, and the singleton ordinary-Rosser test. The shared `z0 ≤ cap` remains a separate explicit hypothesis for any event witness; a raw arithmetic receiver does not get a free root admission.

`receiver_four_lane_union/card/signed` give a disjoint exhaustive four-way classification for an arbitrary ORIGINAL receipt set with its own arithmetic prime:
1. `gateBlocked`: at least one literal root gate fails;
2. `ownCarrierOutside`: licensed root but first-bad quotient factor is not strictly less than its own p;
3. `ownPolicyPass`: smaller first-bad factor is still retained at `[ell,p]`;
4. `ownPolicyFail`: the genuine `[ell,p]` ordinary-Rosser test fails.

`original_U34_receiver_root_eight_lane_count`, `original_U34_raw_with_eight_exceptions` and `original_rejected_eight_lane_signed` combine these four cases for each of the two distinct **original** rejection sources, `frozenOnly` and `rejectedFrozen`. They reuse the previous original `rejected_original_card_split`, `raw_U34_plus_two_rejections` and exact source partition. Both bad-factor cutoff definitions, tagged U3/U4 occurrences and arbitrary signed per-receipt weights survive; there is no division by event-fibre size or unproved nonnegativity.

`frozen_own_root_fail_has_event` and `rejected_own_root_fail_has_event` now obtain the previously conditional historical rejected-event witness DIRECTLY from each receipt's fourth-lane membership plus the actual global `z0 ≤ cap`. The event has the genuine selected prefix `[ell,p]`, parity `true`, mass `1/(p-1) * 1/(ell-1)`, and the receiver-root physical suffix. These are conditional event existence statements only, not injectivity, unique historical owner or full signed payment.

## Mathematical boundary and unclosed obligations

- Root admission is **not** established for all original U3/U4 roots. The first lane records the precise failures of `p ∤ N`, `p < z0` or the singleton ordinary-Rosser policy. Its cardinality and signed mass are not bounded or paid.
- The non-event second and third lanes remain explicitly unpaid. The fourth lane has existence of a local event, not its unique owner in the full/selected/inherited retained history. Distinct q receipts may lead to the same event; original receiver multiplicity and eventual payment are OPEN.
- Original U3/U4 `selected-count` root weights, complete full/selected/inherited filters, true subsequent histories and count-to-history map remain OPEN.
- Request-layer Buchstab/retention and all-action CLOSED-CELL induction remain OPEN. Base/fixed/switched/seed/floor, internal PP/same-rho, true alpha, same-Q, integral/Theta/count correspondence, native-history mass and one nested 430+11 construction remain OPEN. The existing c/K, root norm 7/2 and row norm 12 are unchanged.
- No external PNT/Mertens/BV proof was added or moved into a new axiom. See EXTERNAL_INPUTS.md.

## Checks and next action

GitHub fetch confirmed the new blob and source commit, and compare against `492d8a4` initially showed one additive new source path. Text checks found 11 theorem declarations and five definitions; regex scan found **zero standalone** `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` or `sorryAx` tokens. These checks say nothing about Lean elaboration or kernel validity.

**NOT RUN:** Lean/Lake, full compilation, kernel replay, transitive axiom audit, CI dispatch, independent analytic review, numerical430 certificate checks and other finite guards. Keep all finite checks **UNEVALUATED**; no node becomes green or receives formal proof credit.

**Next distinct manuscript-internal move:** inspect the fixed original selected/full/inherited counting gate for the source of each root (including the diagonal p|N possibility) and derive whether the blocked lane can be eliminated or bounded, then prove the occurrence-preserving, noninjective fibre payment from each fourth-lane original receipt into its actual retained history. Do not repeat the arbitrary-frontier six-lane account or relabel any of these as external inputs.
