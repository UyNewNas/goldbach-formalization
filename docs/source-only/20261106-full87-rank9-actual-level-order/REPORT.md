# P1.4 — actual parent-before-cap orientation of rank-nine crossing [SOURCE_ONLY]

## Actual scope and provenance

Baseline read: `5f802ead6b771d3859ae56c261e039e42aa74dc3`, branch `chatgpt/p1-full87-rank9-two-sided-window-20261106`; previous exact two-window candidate `e134d56be82397970c77684ea5cc1bc207a16244` (blob `db367b1558160ed9aabfab286a4a451da92b8232`). New independent branch `chatgpt/p1-full87-rank9-actual-level-order-20261106`. Candidate `docs/source-only/20261106-full87-rank9-actual-level-order/P4AOriginalFull87RankNineActualLevelOrder.lean`, Git blob `7b7e87c2f21c952b54e4f549a5b2924d97eca043`, 190 lines.

Fixed manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, especially §4's original sixth-parent / eighth-cap comparison. Fixed Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. Constants c=49044063/25000000 and K=8452171/1250000 unchanged.

## Mathematical proof-body addition, not a numerical claim

The previous crossing test used two un-ordered frozen levels L=min(R_parent,R_cap), U=max(...), so it had to retain two possible decision directions. On the actual *owned* eighth frontier, this packet derives the orientation from existing literal source data:

1. `states_eq_owner_filter` and `retainedOwner_some_iff` extract the same original Cell and genuine `point8 ∈ trim`, without assuming owner/trim as a new field or replacing the carrier.
2. `owned87_eighth_state_exact_carrier` supplies `selectedPrefix.length = 8`; this rewrites `point8` to the original `primeHistoryLogCoordinates N 8 selectedPrefix`.
3. The existing `actual_eighth_kernel_transport`, instantiated at this **same state**, original `actualParent`, original `finiteCap`, and real `RealizedHistory`, gives `actualParent ≤ comparison c t < finiteCap`. With N>1, real powers preserve strict ordering.
4. Consequently **only parent rejects / cap accepts** can occur at rank nine: `R_parent ≤ Θ(H,p) < R_cap`. The opposite direction is ruled out. The previously proved disjoint historical-square shell and cubic annulus specialize, with unchanged strict endpoints, to:
   - historical: `R_parent ≤ J(H) < R_cap` and `B*p^3 < R_cap`;
   - cubic: `J(H) < R_parent ≤ B*p^3 < R_cap`.
   Here B is the actual selected-prefix product and J the actual inherited odd-square ceiling, not a new independent geometric threshold.
5. A rank-nine prime genuinely admitted by the parent's original ordinary Rosser test must also be admitted by the cap's original test. No mask has been applied to any inherited continuation.

This resolves the *orientation of the finite rank-nine comparison* at each actual **licensed** owned source occurrence. It does not show the historical-shell cost is zero or small. In particular, a history admitted at earlier levels need not pass all inherited tests at the newly frozen parent level.

## Assumptions and checks

The lemma is **conditional on the actual** `RealizedHistory e q om N s.selectedPrefix c`, the original `4*width n < width r` rounding resolution, `N>1`, and membership in the unchanged original owner/trim `states` list. Those are explicitly retained, not packaged as an equivalently difficult certificate field. The global full-87, same-rho supplier of `RealizedHistory` at every relevant occurrence and parameter has NOT been completed here.

Static inspection of the complete 190-line candidate source found no forbidden proof escape tokens. The exact frozen manuscript and three repository/toolchain pins were re-read, together with the actual source/geometry/guard and preceding rank-nine proof. Separate exact-rational/integer synthetic orientation and window tests: 30,000 pairs (30 shell, 16 annulus, 29,954 no crossing, 2,927 equality setups), zero contradictions. These are deliberately **not** original saved87 replay or Lean elaboration.

**SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.** No Lean/Lake, kernel replay, axiom audit, independent review, saved87 original archive or reserve payment; no CI, Codex, extra compute or upgrade. Nothing is promoted to green.

## Still open

Full original 87-domain unconditional `RealizedHistory` for the actual current state and parameter schedule; genuine same-rho quantitative historical-shell and cubic-annulus prime-harmonic payment, keeping target-prime deletion; original `attachedLeafTest` full-q AP/primitive/centre/modulus mismatch, deeper signed deletion, sixth filtering, ordinary exit integral, saved87 numerical source and gains, changed/tagged, two distinct reserves, final common-rho assembly. Next step: instantiate the inherited historical-square ceiling under the true geometric old-sixth and new-eighth exponents, and determine if historical-shell can be excluded or bounded on the archived full87 source; do not assume it vanishes.
