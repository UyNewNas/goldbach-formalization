# h34 external-input boundary — unique actual-Q first-excluded key ledger

Pinned manuscript map: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`; `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. No switch to the newer publication is permitted by this packet.

**New genuinely external analytic inputs: NONE.** This packet introduces no PNT, Mertens, BV, positivity axiom, external counting lemma, target-equivalent count licence, or substitute numerical430 certificate.

## Exact existing manuscript-local interfaces consumed

- `frozenFailAtActualQ` and `rejectedFailAtActualQ` from `Part5OriginalH430ActualQFirstExitReceipts`: filters of the original two disjoint tagged rejected-receipt sets, each tested at the receipt's actual `originalPhysicalQ` and with its own `frozenOnlyBad N` versus `rejectedFrozenBad N n tau`.
- `actual_Q_two_fail_sources_disjoint`: receipt disjointness only; used in `actual_Q_two_fail_signed_split` and in the second case of `actual_Q_unique_key_has_signed_first_exit`. No event-key injectivity is inferred.
- `receiverEventKey` / `originalEventMass` from `Part5OriginalH430ReceiverEventFibreWeights`: original ordered (p,ell) event key and bare event mass, not original q and not an additional prime slot.
- `originalPhysicalQ` from `Part5OriginalH430PhysicalSelectedRootQFibres`: true tag-and-root physical Q, preserved by the new paired key `(Q,(p,ell))`.
- `actualRankTwoHistory` and `actualRankTwoSignedExit` from `Part5OriginalH430RealSignedExitPayment`: literal rank-two history and **signed** first-excluded Euler term, including the complete actual remaining product.
- `frozen_fail_actual_Q_unique_signed_first_exit` and `rejected_fail_actual_Q_unique_signed_first_exit`: instantiated in `actual_Q_unique_key_has_signed_first_exit` for an original witness of a distinct actual physical key. Requires the genuine local `z0 ≤ cap` premise, not a new externally assumed existence.
- Mathlib finite images, filters, exact finite sum reindexing, card positivity, natural subtraction and `omega` are reused foundational tactics/laws. No new analytic theorem is re-proved.

## Manuscript-internal obligations still open

All theorems in this packet are source-only uncompiled candidates. The actual-Q triple identifies a **distinct historical event key**, not the complete full/selected/inherited owner, nor a theorem that one event can pay a q/tag fibre. In particular, `actual_Q_unique_signed_exit_and_unpaid_fibre_ledger` carries its signed residual exactly and `actual_Q_card_unique_keys_plus_collision_overhang` carries every excess q/tag receipt. Neither remainder has the direction or quantitative estimate needed by H430. The other original rejection lanes, root count weights, the real Buchstab/retention all-action count induction, base/seed/floor/feedback integrals, PP/same-rho, native-history and common nested 430+11 remain internal.

No transitive external-axiom audit, Lean build, kernel replay or finite numerical430 replay was performed.
