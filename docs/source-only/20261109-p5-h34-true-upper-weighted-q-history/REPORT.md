# P5.6 → h34 — true upper H430 q-weight source at actual physical history

Date: 2026-11-09 UTC. Branch: `chatgpt/p5-h34-true-upper-weighted-q-history-20261109`.
Predecessor verified commit: `104272239f190f86576f22cb36bd261aba1c067a` (continuation of the earlier h34 chain, not the initial task SHA).
New math source: `d6cc4af1ce3175dba8aecdb95f7d24fe0847f08b`, blob `55688625a24824ffe241be7205a8b4a9cba86974`, 174 lines.
File: `docs/source-only/20261109-p5-h34-true-upper-weighted-q-history/Part5OriginalH430TrueUpperWeightedQHistory.lean`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**.

## Why this increment matters

Previous packets (through 1042722) established a literal six-lane original U3/U4 arithmetic
source ledger on real physical rank-two Fin positions, including a signed arithmetic/history
mass gap and a Q-dependent post-frontier erasure. Independently, the genuine upper U3/U4
H430 coefficient had been brought back to the original (p,q,tag) arithmetic q-fibres.
There was not yet one common theorem that applies that **exact, tag-specific H430 upper
lookup** to the **true physical-Q history** with all outstanding signed debts visible.

This new source combines those actual pre-existing objects rather than assuming
a generic owner or silently setting original q-dependent arithmetic weights to one.

## New declarations and exact scope

1. `trueUpperH430TaggedReceiptWeight` retains arbitrary independently signed
   `w3(p,q)`, `w4(p,q)`, multiplied by the fixed true `U3H430Coefficient`
   and `U4H430Coefficient` respectively. Both original tags and original q
   occurrences remain distinct.
2. `original_true_upper_tagged_sum_eq_lookup` identifies the resulting
   original tagged arithmetic sum definitionally with the existing literal
   `originalWeightedTrueH430Lookup`.
3. `original_u4_two_tag_true_upper_weight` applies the **existing** genuine
   U4 upper-band equality `U3_eq_main_on_U4` to show that one real U4
   (p,q) pair incurs `(w3+w4) * U4H430Coefficient`. This is a common
   upper *table* coefficient, **not** an assertion that both tags have an
   identical historical root Q or path.
4. `original_true_upper_H430_qfibres_to_actual_kept_history` is the main
   exact signed bridge: the original upper H430 q-fibre sum equals the
   retained true rank-two **mass plus arithmetic/history mismatch**, plus
   erased arithmetic source, plus ALL six already established original
   receipt/rejection/collision lanes. The `keep Q` predicate is left
   as a literal Q-dependent filter, with no claim it is the unpublished
   selected/inherited owner.
5. `original_true_upper_H430_lookup_to_actual_unfiltered_history`
   states the corresponding exact original H430 lookup and **unfiltered**
   real Fin-position sum. The actual history mass is not a first-excluded
   signed Euler correction or a complete h34 count proof.
6. `original_true_upper_H430_negative_quarter_ledger` carries precisely
   the original Chen negative-quarter sign across the real q-source ledger.
   Every unmatched signed component remains on the right; no component is
   dropped on an unjustified sign claim.

These are finite exact source equalities, not a favorable unpaid error
inequality. No new root Q, normalization, c/K, 7/2 root norm, 12 row norm,
real alpha, original tag count, stage, seed, or certificate threshold was
chosen or changed. H430 remains the actual frozen upper table; H248 is
not substituted. No P1.4/P3.6 file or production module was edited.

## Mathematical obligations still open

- Prove the literal frozen manuscript U3/U4 **full/selected/inherited owner**,
  stage/depth, root weights, z0, Fin positions and physical Q, rather than
  treating the Q-dependent Boolean filter as that owner.
- Bound, with correct signs, the `trueUpperH430TaggedReceiptWeight`
  arithmetic-vs-history gap, erased q receipts and all six lanes. The
  U4 two-tag/cross-q collision needs real weighted signed capacity.
- Supply actual first-excluded Euler suffix/owner payments; a positive
  rank-two frontier mass is **not** its signed correction.
- Establish request-level Buchstab/retention and all-action CLOSED-CELL
  count induction, correct base/switched/seed/floor, feedback-to-integral,
  original PP/same-rho compatibility, native-history mass control and the
  common causal430+11 nested refinement.
- Stage the full pinned source-only import closure and run Lean/Lake,
  kernel replay, axiom audit and finite numerical430 checks.

## Actual engineering validation

GitHub push permission was available; a dedicated h34 branch was created
at the verified predecessor, with no force push, merge, CI edit, or upstream
file replacement. The mathematical source blob was read back as
`55688625a24824ffe241be7205a8b4a9cba86974`; the baseline-to-math comparison contains only this
new Lean file (174 lines, zero deleted). Forbidden-proof-escape text
scan found no `sorry`, `admit`, custom `axiom` or `unsafe`.

Local runtime has no `lean`, `lake`, or `elan` executable; direct
git access to github.com fails DNS resolution; complete source-only
import closure is not staged. Thus no Lean elaboration, compilation,
kernel replay, transitive axiom audit, or numerical430 certification
ran. Static scan and GitHub hashes are NOT Lean checks.
The original finite evidence remains **UNEVALUATED**, formal green credit 0.
No existing CI was dispatched to avoid a heavyweight run that would
not compile this unstaged source-only module.

**Next precise work:** instantiate the TRUE full/selected/inherited
historical owner on the physical Q-dependent filter and bound the
signed U4 tag/cross-q gap plus all rejected lanes. Prioritize a pinned
local import-closure compile, then resolve actual Lean failures before
claiming compiled coverage. Avoid another abstract positive-part or
unit-cardinality envelope.

**完整h34稿内证明仍未闭合。**
