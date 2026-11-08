# P5.6 → h34 — genuine U4 retained-tag obstruction at the actual rank-two owner

Date: 2026-11-08 (UTC).
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Incoming remote HEAD: `4c46033dd5d4890bd693b741b297e221832794d9`.
Math source commit: `3dcd25412ca33618cb30e248ba9764c19572af30`.
Source blob: `0825cf491d93943913da785e5d62870004bb759f`.

Status: **PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED**.

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`;
`paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Pinned Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
No manuscript or dependency update.

## Recovery and mathematical scope

Read the original `20261105-p5-h34-request-admission` REPORT, REGISTRY,
EXTERNAL_INPUTS and the latest `20261108-p5-h34-initial-two-signed-root-factor`
handoff. That previous packet separated the true depth-k native first-two
factor from its signed suffix but explicitly did NOT identify the original
U3/U4 arithmetic owner. Earlier packets established actual Q/ell coincidence
and two retained U3/U4 tags at the same physical slot, plus a unique actual
rank-two Fin prefix position.

This increment is NOT another generic history-factor interface. It proves
a concrete impossibility for the real rank-two candidate owner and retains
the exact remaining original q/tag fibre under Chen's -1/4 sign.

## New source and exact assertions

New module: `Part5OriginalH430UpperRankTwoOwnerObstruction.lean`
(131 lines; 3 candidate theorems; no new axioms or abstractions of h34).

1. `original_u4_retained_no_injective_rank_two_fin_owner`:
   for an original U4 (p,q) whose *left tag actually passes*
   `retainedReceipts`, there does not exist an injective assignment
   from ALL receipts in its actual physical (Q,p,ell) slot fibre to
   positions in the genuine fixed-Q rank-two first-exit list,
   requiring the literal selectedPrefix [ell,p]. The two retained tags
   have the same actual prefix; original rank-two prefix uniqueness
   would force equal Fin indices and contradict tag distinctness.
   No assumption of nonempty U4 or a second historical owner is made.

2. `original_u4_retained_slot_card_two_plus_remaining`:
   for that same exact ORIGINAL retained fibre F,
   `F.card = 2 + ((F.erase (inl x)).erase (inr x)).card`.
   The leftover q/tag receipts are not removed by replacing q with ell.
   This strengthens the previous lower cardinality bound to exact
   bookkeeping including cross-q collisions.

3. `original_u4_retained_slot_negative_quarter_with_remaining`:
   the true negative Chen-quarter arithmetic cost of this restricted
   slot fibre is
   `-(1/4) * F.card = -(1/2) - (1/4)*remaining.card`.
   The sign and the original U3/U4 two-tag coefficient are preserved.
   This is an arithmetic identity, NOT proof that an H430 rank-two
   history pays either tag or the remaining q mass.

## Mathematical boundary and next dependency

The actual upper H430 `full/selected/inherited` owner, depth and z0
are STILL unknown. The rank-two impossibility rules out precisely
an injective *rank-two*, same-Q, same-prefix owner of those distinct
retained arithmetic receipts; it DOES NOT rule out a deeper history,
a legitimate non-injective weighted accounting, or signed Euler
reconciliation at the actual owner.

Next: locate the manuscript's real upper H430 count-root owner and
its `full/selected/inherited` filters; determine physical Q, z0,
actual history depth and whether a receipt is mapped to a position,
an extension fibre, or an exclusion charge. At THAT actual stage
measure retained positions, map the original signed root weights,
and retain any unmatched q/tag mass. Do not use the rank-two owner
impossibility as a proof of the global upper bound.

Other unclosed INTERNAL obligations remain request-level
Buchstab/retention and all-action CLOSED-CELL count induction;
correct base/switched/seed/floor and feedback-to-integral payments;
signed Euler first-excluded/rejected six lanes; manuscript-local
PP/same-rho; native proper/equality/inherited mass; and ONE common
430+11 causal refinement. Preserve original c/K, 7/2 root norm,
12 row norm, true alpha, Q, and original positive occurrence counts.

## Validation and ownership

Actual GitHub math blob and commit were read back. Compare against the
incoming HEAD: exactly one new, 131-line Lean file and zero deletions.
Static delimiter and forbidden-proof-escape token scan only.
No Lean/Lake elaboration, compilation, kernel replay, axiom audit,
independent review, CI dispatch or numerical430 evaluation.
All new candidates and inherited finite certificates remain
**UNCOMPILED / UNEVALUATED**. NO green proof credit.

Only this new isolated h34 source-only directory changed. Production
modules, P1.4, P3.6, manuscript, CI settings and original toolchain are
unchanged. No mainline merge or forced update.

**完整h34稿内证明仍未闭合。**
