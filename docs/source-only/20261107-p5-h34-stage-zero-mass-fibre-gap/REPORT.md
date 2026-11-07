# P5.6 → h34: actual stage-zero candidate mass and original quotient-fibre surplus

Date: 2026-11-07. Branch: `chatgpt/p5-h34-request-admission-20261105`.
Predecessor verified HEAD: `6e9e4386c08898742f5a43574ea0577fc01134ed`.
Source commit: `5f44a1b889e36c5b973a90c4d87011e04e9a58e4`.
Source Git blob: `c46ac0761ee21e95de3019983b008a5adacbb80d`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.

**PARTIAL_SOURCE_INCREMENT · FULL_H34_OPEN · SOURCE_ONLY · UNCOMPILED · UNEVALUATED**

## Concrete increment

New module `Part5OriginalH430StageZeroMassFibreGap.lean` (190 added
source lines, eight theorem declarations, one real weight definition).

The previous packet attached the original U3/U4 selected (tag,p,q)
receipts to the **actual** stage-zero root candidate at their true
tag/p-dependent physical Q, but left the one-candidate versus many-q
mass difference unspecified. This packet reads the actual
`firstExitNextSelectionCandidates` recursion. For a candidate with
selectedPrefix=[p], it derives:

- `candidate.positive = false`;
- `candidate.mass = 1/((p:Real)-1)`;
- `candidate.remaining = roughPrimeUniverse N cap 0 (p:Real)`.

These are true first-exit history data, *not* the separate generated
frozen-request `rootHistory` root mark, which remains one. The proof
uses the original descending rough-prime universe and the actual
enumerator's skipped prefix. The physical cap and cutoff are not enlarged.

`original_stage_root_exact_geometry` combines this literal mass, sign
and suffix with the preceding actual root-stage policy witness, retaining
`rootQ N precision k tau p`, the lower Boolean and its real cap.

For `m(p)=1/(p-1)`, the original tagged q receipts at admitted roots
satisfy the following candidate exact weighted identity, with each
U3/U4 tag separately counted (including overlapping p values):

    sum_(tag,p,q stage-admitted) m(p)
      = sum_(tag,p stage-admitted) m(p)
        + sum_(tag,p stage-admitted) (card(originalReceiver N p)-1)*m(p).

The first sum on the right is exactly ONE rank-one candidate weight per
tagged root. The second is the explicit q-fibre multiplicity difference,
not an owner payment. Since an original admitted root p is prime, m(p)>0;
when its originalReceiver fibre contains at least two q labels, that
surplus is strictly positive. No global existence of such p is asserted.

Precise declaration list:

1. `stage_zero_candidate_mass_sign`
2. `stage_zero_candidate_exact_suffix`
3. `original_stage_root_exact_geometry`
4. `original_quotient_fibre_root_mass`
5. `stage_original_receipt_root_mass_total`
6. `stage_original_root_mass_gap`
7. `actual_admitted_root_mass_pos`
8. `two_quotients_force_positive_root_surplus`

## Mathematical boundary

This is only the stage-zero one-root versus q-receipt accounting.
Neither the root candidate nor its single mass is a proven
full/selected/inherited **owner** for every original q. No post-root
historical ownership, inherited filter, actual final selected-count
consumer or directional Euler-event compensation has been proved.

Unpaid: physical z0 and lower-stage choice; stage-surviving q owners
and weights; cutoff/policy/carrier-outside/policy-pass failures; q/tag
and cross-source overlaps; signed Euler correction and its proper
direction; all-action CLOSED-CELL count induction; genuine
base/switched/seed/floor; feedback integral—Theta—count; manuscript-local
PP/same-rho; native-history mass; one common 430+11 nested causal
refinement. P1.4 and P3.6 are untouched.

## Validation and installation

No Lean elaboration, compilation, kernel replay, transitive axiom
audit, CI dispatch, independent review, or numerical430 certificate
evaluation is done. All inherited finite guards remain UNEVALUATED.
Static source-token checks and remote blob/diff readback are NOT Lean
verification. This packet is not staged into the production
`ImbalancedChen` library; it imports earlier source-only candidates.
The old toolchain, dependencies, c/K, root norm 7/2, row norm 12,
true alpha and Q, closed-node discipline and generation budget remain
unchanged.

## Next precise action

Use the true first-stage mass and explicit q-fibre surplus to trace
**one actual tagged q receipt** through the first subsequent
full/selected/inherited historical filter and identify its genuine
owner/occurrence and correctly signed weight. Any surplus or rejected
mass not so matched must stay as a named, unpaid term. Do not replace
a q-weight sum by a single candidate mark.

**完整 h34 稿内证明仍未闭合。**
