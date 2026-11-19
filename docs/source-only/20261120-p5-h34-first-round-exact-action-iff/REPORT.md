# P5.6 → h34 — first-round exact positive-action equivalence

Date: 2026-11-20 (Asia/Shanghai).
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Incoming verified HEAD: `1c10cdd1877c09880a489058046ab060446654e4`.
Source: `Part5OriginalH430FirstRoundExactActionIff.lean` (156 lines, 8 theorem declarations, 3 public).
Source blob: `0f1165dcf48d68d940fadf6edaca456d8cdd8996`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Actual mathematics (Lean candidates; not compiled)

The previous first-round source partition proved one direction only: with the
authentic seed already bounded by an integer Table ceiling, bounds for every
targeted original 106-bank row and every lower suffix at physical indices
50..108 are sufficient to bound the full first-round two-table producer.

This packet establishes the missing reverse implication using the actual
offerRow / 106-row scan max semantics and the original ordinary lower
Buchstab decision. Even a targeted bank candidate which ultimately LOSES
is <= the actual first upper result at that physical cell. Each enabled
lower suffix is <= the actual first lower result. Thus the previous
sufficient conditions are also necessary (under the same genuine seed
inequality). The final candidate theorem is:

`first_round_safe_iff_all_actual_positive_sources`:
if `iterate 0 <= ceiling` at all original 400 cells, then
`iterate 1 <= ceiling` at all 400 cells iff BOTH:

1. Every original targeted row `(k : Fin 106)` has
   `candidate seed (rows k) <= ceiling true i` at every genuine target i.
2. Every original lower physical i with `50 <= i < 109` has
   `suffix seed true (i - 49) <= ceiling false i`.

This is a source-specific *exact obligation classifier*, not an assumption
that the candidate bounds are true, an analytic closed-cell F comparison,
or the full 430-stage invariant. It does not charge an unchosen candidate;
a needed inequality for proving a max bound is not a mass payment. The
original Q80 floor, q/logWeights, fixed seed, left-to-right scan and
genuine target lists are unchanged.

## Boundary and next work

The packet does NOT establish the positive candidate bounds, seed-safe
ceiling, frozen F at closed query endpoints, or the other 429 generations.
No original U3/U4 selected-count identity, root weights, owner, rejection
payment, PP/same-rho or common 430+11 nested refinement is supplied.
Prior seven-integral candidate total remains 0.590 vs 0.650 required.

The independent container has git but no Lean, Lake, Elan or pinned
compiled import closure. Native github.com DNS resolution fails. Existing
GitHub Actions are heavyweight and do not install these held source-only
modules as a targeted build; this packet does not change CI or dispatch
a misleading verification run. No Lean/Lake elaboration, kernel replay,
transitive-axiom audit or finite Lean certification. All eight theorem
bodies and inherited finite table guards remain UNEVALUATED.

To stage the source, import after
`ImbalancedChen.Part5OriginalH430FirstRoundActiveSupport` under the
pinned source-only installation, then compile targeted module and direct
imports. If compiler errors arise, repair this task-owned source; do not
substitute an unproved wrapper. Substantively, produce *numeric* original
bank and 59 lower suffix integer inequalities together with the frozen
analytic F envelope before proceeding to the remaining 429 rounds.

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean: `leanprover/lean4:v4.33.0-rc1`.
Pinned mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
Original c/K, root norm7/2, row norm12, same Q and other owners untouched.
No new external analytic input.

**完整h34稿内证明仍未闭合。**
