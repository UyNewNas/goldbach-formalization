# P5.6 → h34 — actual arithmetic receiver fibres and unpaid frozen surplus

Date: 2026-11-05. Parent: `495757063db590ad30d98795ea91ba5b810a7611`.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Status: **PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT**.
The complete manuscript-internal h34 remains OPEN.

## New source-only manuscript step

`Part5OriginalH430TaggedReceiverFibres.lean` imports the previous tagged arithmetic source and preserves the actual U3/U4 tag, original selected prime `p`, and individual strict receiver prime `q`.

- `arithmetic_labels_injective` establishes that those **three labels** determine a tagged arithmetic occurrence. This is not an identification with a generated feedback `Occurrence` or its root mark.
- `frozen_tagged_band` attaches each frozen arithmetic receiver to the **original** selected prime band.
- `frozen_only_U3_iff` and `frozen_only_U4_iff` characterize every excess receiver exactly as an old-band `p` with a frozen `q` that failed the original source. No excess is declared zero.
- `frozen_only_card_by_fibres` computes the full difference by genuine `(tag,p,q)` **fibres**, retaining U3/U4 overlap costs and all distinct q for one p.
- `frozen_tagged_partition` and `frozen_tagged_card_split` prove exact finite disjoint accounting under the already-derived pointwise cutoff inclusion.
- `original_U34_plus_extra_eq_frozen` produces the exact arithmetic balance `U3 + U4 + frozenOnly.card = frozenTagged.card` as a proposed Lean theorem. In particular, replacing original counts by the frozen counts costs an explicit, nonnegative **surplus**; this is not a free root-feedback equality.

The predecessor packet `4957570` compared the original arithmetic receivers and their frozen superset. This packet makes its **unpaid overcount** an exact, finite, root-indexed source, rather than merely naming a set.

## Still manuscript-internal and OPEN

1. Match each `(tag,p,q)` arithmetic receiver to the manuscript's actual full/selected/inherited **owner and filtration**; the arithmetic tag is NOT the table's updated-cell owner.
2. Derive the correct closed-cell counting inequality with those filters, error direction and rejection payments; account for `frozenOnly` without silently dropping its mass.
3. Pay real root weights, base/fixed/switched/seed/floor and same-rho/PP instantiation.
4. Pay native-history, outer integral–Theta–count normalization, and the common nested 430+11 refinement.

There are no new external inputs or axioms; genuinely external PNT/Mertens/BV proofs are not implemented.
P1.4 and P3.6, production code, dependencies and CI are unchanged.

## Validation

Only source delivery; Lean elaboration, kernel replay, transitive axiom audit and numerical430 are **UNEVALUATED**. Theorems are proposed proof bodies, not machine-checked results. No build or CI was dispatched.

Next action: follow the real source owner/filter definitions, then relate each tagged `q` fibre to the accepted/rejected counting recurrence; do not turn the unique tagged-root label into a unique receiver or root count weight.
