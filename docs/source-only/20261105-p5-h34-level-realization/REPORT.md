# P5.6 / h34 — exact realized level mass from original selected frontier

Date: 2026-11-05. Base: `e3eb887a11b86130da9ff826c13464a5b4bd341e`.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Status: **PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT**.
The complete manuscript-internal h34 remains **OPEN**.

## New manuscript-internal source

`Part5OriginalH430RequestedLevelRealization.lean` (161 lines, 5 theorem
proof bodies including one private finite-list lemma, one definition).

The preceding `e3eb887` proved an ordered LIST equality between every
actual generation-g occurrence and the flatMap of the actual selected
winners from generation g+1, including every duplicate position.

This increment EVALUATES that list equality using the ORIGINAL frozen
root Q, the actual old array `iterate g.val`, the inherited
`thetaAtom` and `requestValue`, and the original product marks.
`realizedCellMass` names that literal term (not an arithmetic count).

Exact source-only theorem chain:
- `child_marked_list_eq_tableMass`: one tagged child list evaluates to
  the existing `childTableMass`, with the original appended-path mark.
- `selectedFrontier_realized_mass`: every parent occurrence is expanded
  through its own actually selected winning children; list concatenation,
  not a quotient by physical cell, prime product, owner, or word, drives
  the finite real sum.
- `list_sum_eq_position_sum`: induction converts the ordinary list sum
  into its `Fin xs.length` indexed sum, preserving repeated positions.
- `actual_level_realized_mass_eq_parents`: specialize the preceding
  finite equality to the genuine frozen U3/U4 level list.
- `generationValue_eq_actual_level_mass`: connect this exact list sum
  to the PRE-EXISTING `generationValue` (with computed parent indices)
  through `generationValue_eq_nextLevelMass`, `mark_extend` and the
  original `edgeValue` consumption.

Mathematical scope of the final candidate is an exact identity:

```
generationValue N n root tau p g =
  ((levelRequests N n root tau p g.val).map
    (realizedCellMass N (rootQ N n root tau p) (iterate g.val))).sum
```

No new analytic/error hypothesis appears. The list values are still
generated FEEDBACK request values, NOT the original selected-count
arithmetic prime or PP count source.

## Strictly outstanding manuscript-internal obligations

1. Match the COMPLETE original U3/U4 selected-count source to the
   generated occurrences, including original root count weights,
   scalar versus specified-cell owner, full/selected/inherited
   filters, rejected lanes, and source multiplicities.
2. Prove the true closed-cell arithmetic count induction with correct
   count direction, ordinary/fixed/switched base, seed, and integer
   floor payments.
3. Prove manuscript-local same-rho/PP instances and exact feedback
   integral/outer Theta normalization, retaining all real quantifiers.
4. Pay native-history proper/equality/inherit masses and provide ONE
   nested common causal 430+11 refinement with prescribed reserves.
5. Compile all held modules, kernel replay and transitive axiom audit.

## Boundary and validation

External PNT/Mertens/BV, prime profile or distribution proofs are NOT
implemented here; see EXTERNAL_INPUTS.md. This module adds no target
equivalent assumption, `sorry`, `admit`, new axiom, native proof
escape, dependency/toolchain change, CI action or numerical430 rerun.

Static checks only: no forbidden placeholder tokens, no unmatched
uncommented parentheses/braces, expected declaration signatures and
GitHub object upload. No Lean executable or staging of transitive
imports in this run. **Every new proof is UNEVALUATED in Lean**.
Potential elaboration errors remain open and must not be counted as
verified theorem statements. No green node or full h34 completion.
