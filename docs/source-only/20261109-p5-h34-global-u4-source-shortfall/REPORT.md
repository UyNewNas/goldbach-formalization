# P5.6 → h34 — global original U4 source-to-slot shortfall

Date: 2026-11-09 UTC.
Repository: `UyNewNas/goldbach-formalization`.
Isolated branch: `chatgpt/p5-h34-global-u4-source-shortfall-20261109`.
Verified predecessor: `2ffd701a39d22b23b0511f4a17dcbe995607709e`.
Math source commit: `997f03f591066e51bf877b1ccab6c1bfb44eeb10`.
GitHub read-back source blob: `800f649180d5aa1442bc086a4b4d7971ce979943`.

Pinned existing manuscript map (not changed):
`UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex`. Lean `v4.33.0-rc1`;
Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT · SOURCE_ONLY · UNCOMPILED · UNEVALUATED · FULL_H34_OPEN.**

## New original-source proof candidate

New file `Part5OriginalH430GlobalU4SourceShortfall.lean` (156 lines,
one definition, four theorem declarations).

1. `allU3CandidateSlots` maps every genuine original U3 arithmetic
   `(p,q)` receiver through the already-existing chosen-second-factor
   selector to its literal physical `(Q,p,ell)` key. This candidate
   image is not an assumed owner or a new receipt source.
2. `observed_slots_subset_original_u3_candidates` proves that every
   physically observed rank-two source slot has such an original U3
   arithmetic witness. The U4 case explicitly uses
   `original_u4_pair_has_two_tags` and
   `original_u4_overlap_actual_slot_equal`: it does not posit a
   tag-independent Q or a quotient/history prime identification.
3. `observed_slots_card_le_original_u3` deduces that the number of
   distinct observed `(Q,p,ell)` slots is at most the original
   U3 `(p,q)` cardinality. All q/tag multiplicity remains in the
   source side and is never silently deduplicated.
4. `original_six_unpaid_unit_card_exact` specializes the PREVIOUS
   exact signed six-lane arithmetic-source ledger to unit weights:
   `SixLanes(1) = card(originalTagged) - card(observedPhysicalSlots)`.
   It relies on the previous real Fin-position representative
   reindexing; it does not equate a historical signed mass to 1.
5. `original_u4_global_six_lane_unit_floor` combines this identity
   with the literal `U3 + U4` tagged-card decomposition to give,
   for every `N ≥ 2` and `z0 ≤ cap`:
   
   ```text
   card(originalPairs N U4) ≤ originalSixUnpaidReceiptLanes(..., weight=1).
   ```

This lower bound is filter-independent: it counts the source-to-one-slot
shortfall *before* the still-missing full/selected/inherited owner.
It is not a lower bound for the signed Euler correction, not an
unpaid-analytic-cost estimate, and not evidence of impossibility for the
manuscript's H430 upper count. A valid weighted history payment may cover
multiple arithmetic receipts; that exact map and its signs remain open.

## Pinned inputs and scope

All imported arithmetic source, slot collision, chosen-second-factor,
representative reindexing, and six-lane identities are **existing
manuscript-internal source-only candidates**. No PNT/Mertens/BV
implementation, target-equivalent axiom, `sorry`, `admit`, `unsafe`,
or finite numerical substitute was added. No c/K, `7/2` root norm,
`12` row norm, real alpha, physical Q, selected-cell/scalar distinction,
original q/tag counts, feedback seed or cutoff convention was changed.

## Actual validation boundary

- GitHub permission: authenticated push onto the isolated branch.
- GitHub remote read-back: 156-line source blob
  `800f649180d5aa1442bc086a4b4d7971ce979943`.
- The first commit compared against `2ffd701` adds exactly the new
  Lean file, with zero other changes.
- Text-only checks: declaration count, forbidden-escape scan and
  balanced simple delimiters. These do **not** show Lean elaboration.
- Local container: `lean`, `lake`, `elan` absent on PATH;
  native `git ls-remote` cannot resolve github.com; full source-only
  import closure not staged. No Lean/Lake compilation was executed.
- No CI dispatch (existing heavyweight workflows do not compile an
  unstaged source-only module), kernel replay, transitive axiom audit,
  independent mathematical review or numerical430 replay.
- Earlier finite certificates remain `UNEVALUATED`. No green credit.

## Remaining genuine manuscript-internal obligations

1. Bind the **actual** frozen manuscript upper-count owner to
   full/selected/inherited, stage, z0, depth, real root weights and
   actual Fin positions; no generic postfilter can substitute for it.
2. Supply a valid quantitative map from original U3/U4 q/tag source to
   weighted historical payments; handle the global U4 collision floor
   without pretending one slot represents two arithmetic counts.
3. Pay first-excluded signed Euler suffixes, all six rejection lanes
   and bound the **upper** unpaid counting error by the H430 budget.
4. Complete request-level Buchstab/retention and all-action CLOSED-CELL
   induction, base/switched/seed/floor and feedback to integral.
5. Complete manuscript-local PP/same-rho, native-history mass, external
   input compatibility and one shared causal 430+11 refinement.
6. Stage pinned source-only imports, run incremental Lean compilation
   and kernel replay, then audit transitive axioms and numeric guards.

**Next precise action:** stage/compile the predecessor chain on the fixed
toolchain if possible, then prove the actual upper H430 full/selected/
inherited owner and a **signed weighted capacity** for the U4
double-tagged q-fibres. Do not produce another free-standing unit
cardinality or positive-part identity.

**完整h34稿内证明仍未闭合。**
