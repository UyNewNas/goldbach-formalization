# P5.6 → h34 — actual upper U4 overlap has common frozen physical Q

Date: 2026-11-08 UTC. **PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED**.

- Dedicated branch: `chatgpt/p5-h34-request-admission-20261105`.
- Last verified remote baseline: `91da1ded813133de08c499506690db1a0d7e80c7`.
- Mathematics commit: `3428d735bd92214b9d0b02fb6462effd57630ec2`.
- New Lean module: `Part5OriginalH430UpperOverlapCommonQ.lean` (204 source lines added, 11 candidate theorem declarations, zero additional axioms/definitions); Git blob `aca5a0b523fe24dab2a3a86bb1f0e29272fa8b44`.
- Fixed manuscript remains `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Original Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` unchanged. No CI dispatch.

## Exact new manuscript-internal source

Prior checkpoint `91da1de` distinguished two original arithmetic U3/U4 tags at a common original `(p,q)` and proved a **conditional** physical slot collision: same actual Q *and* same chosen ell. The new source resolves both conditions **on the original U4 overlap** using the already frozen native definitions; it does not assume them.

1. The original upper U4 prime band ends at exponent `59/250`, strictly before the genuine U3 main/tail switch `57/224`. Thus `U3Residual tau t = mainResidual t` everywhere in this interval, for any tau. The U3 and U4 `sourceRoot` total fields coincide, regardless of their DIFFERENT root-kind/ceiling fields.
2. The original `rootQ` is `N ^ frozenLevel precision sourceRoot.total`. Since the cumulative frozenLevel is applied at the **same precision** to identical real totals, `rootQ(.U3,p)=rootQ(.U4,p)` for every genuine `x∈originalPairs N .U4`, with `2≤N`. This is a literal source-map equality, not an imported same-rho postulate or a claim that the two root TypedNodes are equal.
3. Consequently the actual `selectedOriginalRootStage` and second `retainedOriginalSecond` gates agree across tags at the same selected original q. The existential `hasRetainedOriginalSecond` agrees as well.
4. The current `chosenSecondFactor` is selected through `Classical.choose` from that *same unfolded existential proposition*. The candidate proof identifies the two chosen ell factors; hence the actual `physicalRankTwoSlot` values coincide on this true original U4 overlap. No different Q/ell slot can be used to avoid its double-tag capacity deficit.
5. Conditional on actual **both-tag retention**, `samePhysicalSlotOverlap = bothTagRetainedOverlap` and `distinctPhysicalSlotOverlap = ∅`. The theorem does **not** assert any pair is retained, much less that the original integer q gets a full/inherited history owner or two signed-Euler payments.

This is a substantive correction to the previous open question: on the original U4 **upper-count** shared (p,q) interval the physical Q's do not differ under the actual frozen construction; only outside that interval or for different p can tag-specific Q still diverge. Historical root requests retain distinct root-type/ceiling information. Identical `(Q,p,ell)` slots are NOT the same thing as paid history positions.

## Honest remaining manuscript-INTERNAL obligations

1. Bind the actual U3/U4 upper H430 selected-count **full/selected/inherited** predicates, genuine stage and z0 and original q/tag multiplicity to actual historical Fin positions. This packet does not do so, and ordinary lower h-start is not a substitute.
2. Resolve the **double arithmetic-tag vs single physical-slot capacity deficit** (including different q and keys), with real owner and first-excluded occurrence multiplicities. The presently conditional same-slot equality cannot be converted into two payments; keep any unpaid excess.
3. Prove original root count weights, erased-position/retained mass differences, six rejection lanes, signed Euler full suffix, correct-direction first-excluded estimate and cancellation/payment.
4. Finish request-level Buchstab/retention all-action CLOSED-CELL induction, base/switched/seed/floor, integral–Theta–selected-count and manuscript-local PP/same-rho matching, native-history proper/equality/inherit mass and one nested common 430+11 causal refinement.
5. Lean elaboration, compilation, kernel replay, transitive axiom audit, finite numerical430 replay and independent validation remain unperformed. No green node is claimed.

## Verification and next action

Actual GitHub commit, source blob and previous-HEAD comparison were read back: **only one new Lean file**, 204 added / zero deleted; no P1.4, P3.6, other owner files, installed module, CI or dependencies touched. Checked forbidden source tokens absent. Static inspection is NOT Lean elaboration or a kernel proof; all 11 declarations remain **uncompiled candidate proofs**. Numerical430 remains `UNEVALUATED`.

**NEXT:** consume the now-literal common-Q/ell physical slot on the true upper H430 original U4 overlap. Identify the actual upper selected/full/inherited owner and the number of history *positions* available per such slot; preserve both original U3/U4 q labels and mark their unpaid double-incidence unless a legitimate distinct capacity theorem supplies payment. Do not create another abstract slot-filter ledger.

**完整h34稿内证明仍未闭合。**
