# P5.6 / h34 — exact selected frontier list multiplicities

Date: 2026-11-05. Parent: `2d392e5dd469c61b469cfbf24a8e0d5590c367cc`.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Status: **PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / ZERO KERNEL CREDIT**.
The entire manuscript-internal h34 is still **OPEN**.

## Narrow mathematical advance

The parent `2d392e5` proved bidirectional MEMBER support, not positional
multiplicities.  This increment proves a stronger finite identity directly
from the ORIGINAL recursive `RequestedHistory.history` definition.

For each original frozen U3/U4 root and `g : Fin 430`:

```
levelRequests N n root tau p g.val
  =
selectedFrontier N (rootQ N n root tau p) g.val
  (levelRequests N n root tau p (g.val + 1))
```

`selectedFrontier` is literally `flatMap` over the original parent list;
each parent is expanded by its own actual `children N Q g` and
`extend`, not all candidate actions.  `extend` retains the old path
and appends exactly one tagged edge. There is **no deduplication** by
physical node, integer product, prime word, owner label or geometric cell.

Proof chain, one new held Lean module:
- `at_map_prepend`, `at_flatMap`, `selectedFrontier_flatMap` and
  `selectedFrontier_map_prepend`: literal list/order transport.
- `history_at_above`, `history_at_top`, `history_at_below`: root
  isolation and exact depth-first level extraction from `history_facts`.
- `history_first_frontier`: first step equals actual root's chosen
  children, using existing `extend_origin`.
- `history_frontier_list`: induction through the original recursive
  forest; no member-support-to-count inference.
- `level_frontier_list`: specialization to the same literal frozen
  root and common Q; no arbitrary parent or weight function.
- `level_occurrence_count` and `level_sum_exact`: immediate countwise
  and real-valued finite-sum consequences. These preserve duplicate
  list positions, not only set membership.

The list equality provides the missing positional/multiset combinatorics
of the *generated request history*. It does **not** identify that history
with the complete original U3/U4 arithmetic selected-count source.

## Important boundaries

1. The equality uses the original depth-first list order, real
   `children`, `nextRequest`, `prepend`, `extend` and 430-step
   recursion; it changes neither selected scalar versus specified-cell
   resolution nor edge coefficient.
2. `mark_extend` and the earlier `generationValue_eq_nextLevelMass`
   can now be reindexed without dropping duplicate occurrences. The
   arithmetic meaning and sign of the count remain **unproved**.
3. The outer U3/U4 initial count weights are NOT inferred from
   `mark_origin = 1`; actual owner, full/selected/inherited filters,
   rejection lanes and multiplicities still require source matching.
4. Nothing in this module asserts ordinary/fixed/switched base estimates,
   seed, integer floor payments, same-rho PP realization, native-history
   mass, a common causal 430+11 refinement, or the final h34.
5. Original c/K, root norm 7/2, row norm 12 and 430+11 budget remain
   unchanged. No P1.4/P3.6 source, production module, toolchain or CI
   configuration was edited.

## Validation evidence and limitations

The source text was checked for nested-comment balance, four kinds of
paired delimiters, forbidden proof-bypass tokens and exact declaration
presence. The Git blob was created through the repository connector.
These are **text-only checks**. There is no local Lean/Lake executable,
no installation into the production import tree, no compile, kernel
replay, transitive-axiom audit, numeric 430 evaluation or CI dispatch.
All new proof bodies remain **UNEVALUATED** in Lean; no green status.

## Explicit next manuscript-internal target

With positional equality supplied as a held candidate, next read the
original U3/U4 *arithmetic* source predicates and weights and prove their
exact signed recursion / closed-cell comparison against the chosen request
family. Check original root normalizations, selected-owner multiplicities,
full/selected/inherited ancestor filters and rejected lanes before applying
the signed feedback bound from `42859b2`. Preserve base, fixed/switched,
seed and floor costs as separately paid manuscript lemmas. Do not add a
count-source-equivalent hypothesis or classify this missing bridge as external.

Install order: all earlier requested h34 candidates in their chronological
order, then `ImbalancedChen/Part5OriginalH430RequestedFrontierMultiplicity.lean`.
