# P5.6 → h34 — true initial-two prime projection of the actual all-depth first-exit history

Date: 2026-11-08 UTC. Branch: `chatgpt/p5-h34-request-admission-20261105`.
Incoming remote HEAD: `bb63b19970a015073f4ea28d00e003550cbb8be5`.
Mathematical source commit: `ffd61568b04bcdf535bbda0b2a6df38d06571dd0`.
Source blob: `f9da5a0f53ff111aaaac6d6564b03b3e56ea1de1`; new candidate Lean file 207 lines, 7 theorem declarations and 3 definitions.
Status: **PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED**.

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1. No changes to these inputs.

## Why this advances the prior stop

The previous packet `Part5OriginalH430ActualAllDepthFullPrefix` established unique
**complete** depth-k prefixes and their native mass, but this does not bound
the number of deeper histories sharing the **first two ORIGINAL** primes.
The first-exit list stores primes in reverse order: rank-two [ell,p], longer
histories [newer,...,ell,p]. Thus the first two selected primes in original
order are `selectedPrefix.reverse.take 2`, not `selectedPrefix.take 2`.
A fixed rank-two physical slot can have multiple distinct longer extensions.

The new module `Part5OriginalH430ActualInitialTwoExtensionMass.lean` adds:

1. `actualFirstTwoOriginal` and `actualDepthFirstTwoPositions`:
   concrete lists of **true Fin positions** in the genuine ordinary-Rosser
   depth-k first-exit frontier at one physical Q. Repeated deeper positions
   are not deduplicated and original q/tag receipts are not replaced.
2. `actual_depth_original_prefix_length` and
   `actual_depth_first_two_length`: specialize the existing real
   first-exit depth invariant and show exactly two original labels exist
   at every genuine rank k>=2.
3. `actual_depth_different_first_two_disjoint`: different original
   (p,ell) first-two groups cannot claim the same rank-k Fin position.
   This does **not** say any one group has cardinality <=1 at depth k>2.
4. `actual_depth_first_two_weighted_tuple_identity`: a new exact
   transport of the **signed arbitrary full-prefix weight** F over
   actual depth-k native mass to the existing admitted finite prime tuples,
   with the genuine two-prime indicator carried through. No invented
   owner, positivity or signed cancellation is used.
5. `actual_depth_first_two_native_mass_eq_admitted_tuples`: the true
   total native mass of each first-two group is exactly its admitted-tuple
   finite sum, not the count weight or first-excluded Euler payment.
6. `original_u4_retained_rank_two_initial_pair_and_two_receipts`:
   use the actual retained original U4 (p,q) source and the existing
   actual observed-slot Fin witness. It has its original [p,ell] pair
   in a true rank-two history position, while the same slot has at least
   two distinct U3/U4 q/tag arithmetic receipts. This is a conditional
   theorem requiring one genuinely retained original U4 receipt.

## Mathematical boundary

The new equalities are for ACTUAL ordinary Rosser depth-k admitted histories,
not for the manuscript's yet-unidentified upper-H430 historical owner.
At deeper ranks the number of extensions under one pair is a genuine fibre
that must be separately computed at the *correct* full/selected/inherited
stage. The source does not identify that stage, map historical owners to
original arithmetic q/tag weights, or pay the extra tag and cross-q receipts.

Root norm 7/2, row norm 12, original alpha, physical same-Q, original
c/K and 430+11 reserve order are unchanged. This packet introduces no
external analytic theorem and does not expand PNT/Mertens/BV. No target-
equivalent assumed count licence or extra history payment is introduced.

## Remaining manuscript-internal obligations

- Determine the exact U3/U4 upper H430 source full/selected/inherited stage,
  owner, physical z0 and true position filter. Bind the new first-two
  extension fibres at **that exact stage**, not generically.
- Distinguish arithmetic U3/U4 q/tag overlap, different q with the same
  physical (Q,p,ell), native historical mass, original root count weights
  and true first-excluded signed Euler-suffix payment. Keep all extra
  receipts and every rejected lane as unpaid until a proved bound applies.
- Complete request-level Buchstab/retention supply and the all-action
  CLOSED-CELL count induction; base, switched, seed, floor and feedback
  rounding-to-integral with actual Theta/count objects.
- Prove the manuscript-local PP/same-rho applications, native proper,
  equality and inherited history mass and one common nested causal
  430+11 construction.
- Stage source and run Lean elaboration, compilation, kernel replay,
  transitive axiom auditing and numerical430 finite certification.

## Engineering validation

Authenticated GitHub remote source readback confirmed 207 source lines,
source blob `f9da5a0f53ff111aaaac6d6564b03b3e56ea1de1`, and a source-only addition to a NEW dedicated
directory after `bb63b19970a015073f4ea28d00e003550cbb8be5`. Prewrite static forbidden-proof-token
and bracket-balance checks passed. **These checks do not validate Lean.**

Lean/Lake unavailable in the run container. No parser, elaboration, kernel,
CI, transitive axiom audit, heavy compilation or independent review was run.
The numerical430 guards remain UNEVALUATED. No green status is claimed.
No existing file, P1.4, P3.6, manuscript, CI or toolchain was changed.

**Next exact step:** inspect the pinned H430 selected-count consumer to
identify its real full/selected/inherited stage and per-root z0, then apply
the pair-group native mass/position transport there. Do not misapply
rank-two uniqueness to deeper prefixes or double-charge historical slots.

**完整h34稿内证明仍未闭合。**
