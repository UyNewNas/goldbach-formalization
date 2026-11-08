# P5.6 → h34 — actual U3/U4 retained overlap, physical-Q and rank-two slot collision

Date: 2026-11-08 UTC. **PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED.**

- Branch: `chatgpt/p5-h34-request-admission-20261105`.
- Previous verified remote HEAD: `bb33501f0a10dbd87c2e3fe44c25b1a4588d9958`.
- Mathematics commit: `0bb591782f3cb437bf64a5159dfab53d4fea5099`.
- New module: `Part5OriginalH430UpperOverlapPhysicalSlot.lean` (233 lines, 11 candidate theorem declarations, 3 definitions), Git blob `c887eaf854bd977fef5017f38ca09df0deefc391`.
- Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Existing Lean `v4.33.0-rc1` and Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; neither modified.

## Actual mathematical source increment

The prior packet proved the exact original selected-quotient U3/U4 overlap `U3+U4 = |E| + 2|F|` with `F = originalPairs N .U4`. That double arithmetic occurrence is genuine, but it is **not** necessarily one shared physical first-exit state: the frozen `rootQ N precision .U3 tau p` can differ from `.U4`, and the retained second-prime factor `chosenSecondFactor` is determined from the actual root policy at each physical Q.

This module **does not assume** both tags are retained. It defines `bothTagRetainedOverlap` by filtering the genuine original U4 `(p,q)` pairs for which both concrete `Sum.inl x` and `Sum.inr x` are members of the **existing** `retainedReceipts`. The first theorem preserves distinct source tags and full original q even before filtering. The next two definitions split this genuine doubly retained set into equal and different physical `(Q,p,ell)` slots, where each ell is the existing `chosenSecondFactor`.

The central theorem `original_overlap_chosen_slot_eq_iff` proves the exact (conditional, source-only candidate) criterion:

```
physicalSlot(chosenKey(U3,p,q)) = physicalSlot(chosenKey(U4,p,q))
  ↔ rootQ(U3,p) = rootQ(U4,p)
    ∧ chosenSecondFactor(U3,p,q) = chosenSecondFactor(U4,p,q).
```

Thus distinct actual Q values **prevent** cross-tag collision, even on the same original arithmetic `(p,q)`. Conversely, when a shared `(p,q)` passes BOTH actual retained gates and this criterion holds, the two **different tagged original receipts** have the **same** physical chosen slot. The candidate theorem `actual_chosen_slot_map_not_injective_of_overlap` gives a formal obstruction: the true retained-source-to-physical-slot map is not injective in that case. This identifies a genuine potential one-history-event capacity deficit, not a payment or successful owner match.

Finally the candidate exact finite cardinality partition counts same-slot vs distinct-slot doubly retained original U4 pairs, and `original_tag_dependent_signed_overlap` strengthens the preceding common-weight overlap formula to **arbitrary different signed U3 and U4 arithmetic weights**: `Σ_originalTagged Sum.elim w3 w4 = Σ_exclusive w3 + Σ_U4 (w3+w4)`. Neither equality assumes the two labels share historical weights or pays a signed Euler suffix.

## Honest remaining manuscript-INTERNAL obligations

1. Instantiate the genuine U3/U4 UPPER H430 selected-count `full/selected/inherited` owner, its stage, exact `z0`, root count weights and proper original q/tag multiplicities; the ordinary LOWER h-start is **not** such a licence.
2. Prove the actual `rootQ .U3` vs `.U4` relation on each relevant overlap stage, plus real matching of historical Fin-list positions after the complete filters. Both retained and chosen same-slot predicates are not asserted unconditionally; determine their true size and survivor status.
3. Reconcile one physical slot with at most one historical first-exit occurrence, the current slot/key/q collision ledger, the erased positions, six rejection lanes and arithmetic-minus-history mass gap. Do **not** pay two U3/U4 labels from one event without a separate proven capacity mechanism.
4. Establish the full signed Euler suffix and first-excluded correct-direction bound. Complete request-level Buchstab/retention all-action CLOSED-CELL induction, original base/switched/seed/floor, feedback integral–Theta–selected-count, manuscript-local PP/same-rho and native-history 430+11 shared causal refinement. Preserve fixed c/K, norm 7/2 and 12, true alpha and same-Q.
5. Elaborate, compile, kernel replay, audit transitive axioms and evaluate inherited numerical430 finite guards.

## Validation and ownership

GitHub readback confirmed the mathematics commit, source Git blob and a one-file addition against the previous head (233 additions, zero deletions); no existing code or other task's files changed. Local Lean and Lake executables were unavailable; no CI, heavy build, kernel replay, transitive axiom review, numerical430 evaluation or independent proof validation was executed. Basic source-text marker checks are **not** proof verification. All 11 declarations remain UNCOMPILED candidates; no green credit. No new external analytic theorem or axiom was introduced.

**NEXT:** at the pinned U3/U4 upper H430 consumer, determine whether the actual physical Q and chosen retained second prime coincide on the original U4 overlap, and then bind the resulting same-slot/different-slot count to genuine full/selected/inherited historical owners. Maintain the unpaid deficit when there is no sufficient owner capacity.

**完整h34稿内证明仍未闭合。**
