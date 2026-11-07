# P5.6 / h34 — all-choice generated level and common feedback budget

2026-11-05. Continuation from `b9694b354a21b3a6238ef4b2be8ed708912a2de7`,
branch `chatgpt/p5-h34-request-admission-20261105`.

Status: **PARTIAL_SOURCE_INCREMENT; SOURCE_ONLY / UNCOMPILED.**
**The complete manuscript-internal h34 is OPEN.** No kernel-credit claim.
This packet adds three candidate Lean files (380 lines, seven theorem
bodies including one private theorem; six definitions). They belong only to
the held manuscript-internal h34 proof lane, not the production import root.

## What was connected

### 1. AllChoice: true three-way single-generation partition

`selected_case_partition` divides one actual generation-(g+1) request
into exactly one branch chosen by `resolve` and `roundDecision`:

- one of the original 106 bank actions;
- the selected strict Buchstab list (both polarities);
- the selected retention of an exact specified old cell.

If `resolve` returns none, the request emits no children and has zero
edgeValue. `exact_level_partition` sums this classification over the
**actual `Index` of the level list** for any signed test. It neither
identifies products nor deletes repeated occurrences. In particular, it
does not identify a specified-cell read with a scalar closed-owner read.
`generationValue_partition` applies the exact partition to the original
positive-mark child `edgeValue` with previous-generation table; its
retained summand is the existing `retainedLevelValue` exact old cell.

This is an exact **feedback-generation value** identity; it is not yet
an equality with the original U3/U4 prime-count sum.

### 2. AllFeedbackBudget: one epsilon and one 12-Theta ceiling

`uniform_combined_feedback` obtains a single threshold before N from
the previously supplied `uniform_level_bank_supply` and
`uniform_level_buchstab_supply`. It is uniform across root kind, root
prime, precision, generation and selected action (with the previously
stated root hypotheses). It sums only their actually selected level
positions, with unchanged positive path marks. For the resulting
`combinedTheta`, `combinedError` and `combinedRow`:

- coefficientwise absolute error `combinedError <= epsilon*combinedTheta`;
- every combined coefficient is nonnegative;
- the total combined row mass is `<= 12*combinedTheta`;
- a zero combined Theta gives zero error and every coefficient zero.

The Buchstab row bound is 5-Theta, but it is on DISJOINT selected
positions and 5<=12: it is NOT an additional 5-Theta fee imposed on a
winning bank request, and there is no 106-fold charge. Buchstab Theta
nonnegativity is derived from its nonnegative mass and 5-Theta upper
bound. Retention carries no new coefficient error (it is exact).

The source preserves the row norm 12 and the true positive marks, with
no division by Theta at zero.

### 3. CandidateLevel: the literal winner's finite candidate upper

`markedBankRead_le_candidate` instantiates the already proved
`selected_bank_candidate_upper` at each actually selected list
position, multiplies only by its positive path mark, and sums.
`all_markedBankRead_le_candidate` sums across all 106 bank actions;
the other two choices stay excluded by exact winner selection.
The candidate uses the original previous-table base, fixed and
feedback terms, and `actionOfSlot (slotOfAction a)=a`. No extra
analytic input or source-count licence is assumed.

This is still an inequality about the original table READS, not the
actual prime-count CLOSED-CELL induction. Theta-weighted count
comparison, floors and integer source identification are not inserted.

## Remaining manuscript-internal obligations

1. Establish the genuine all-action CLOSED-CELL count induction from
   original prime/sifted counts, including base/fixed/switched/seed,
   directional count-versus-feedback comparison, integer floor/rounding
   payments, and the correct boundary/equality cases.
2. Identify the complete original U3/U4 source: original root count
   weights, unique source owner, full/selected/inherited filters,
   rejection lanes and multiplicities, not merely the generated
   request-list history. Keep original occurrence positions.
3. Bind actual feedback integral pieces, manuscript-local same-rho/PP
   instances and seed estimates with the correct quantifier order.
4. Establish all proper/equality/inherit native-history masses,
   outer-integral/Theta/count normalization and ONE nested causal
   common 430+11 refinement with its reserve order.
5. Stage the complete held sources, compile and perform P0-controlled
   kernel replay, complete types and transitive axiom audit.

Only genuinely external results are referenced in EXTERNAL_INPUTS.md;
no PNT/Mertens/BV theorem was implemented, no new sorry/admit/axiom
was introduced, and no h34/hLower-equivalent hypothesis was added.
Original c/K, root norm 7/2, row norm 12 and 430+11 budget are
unchanged. P1.4 and P3.6 are untouched.

## Verification and next action

Local Lean and Lake are unavailable; the pinned repository control
permits only P0 to dispatch heavy compilation/CI. **No Lean parsing,
elaboration, build, kernel replay, axioms or numerical 430 table were
executed.** Text checks only: exclusion of proof placeholders,
nested-comment-aware delimiter balance, source declaration inventory,
new-blob readback and base-ref comparison. These are not formal proofs.

Stage the three new files in order (all prefixed
`Part5OriginalH430Requested`):
`AllChoice`, `AllFeedbackBudget`, `CandidateLevel`. Previous six
requested-source modules must be staged first in their original order.
The next manuscript-internal action is the actual source-count one-step
inequality, linking the correctly signed arithmetic prime/PP counts to
the chosen feedback-generation value, then paying base/seed/floor.
No source-count licence is to be substituted as an assumption.
