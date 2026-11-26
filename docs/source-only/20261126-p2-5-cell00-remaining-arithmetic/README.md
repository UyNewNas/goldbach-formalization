# Cell00: remaining row arithmetic and all-eight composition

**Status: source only. No Lean compilation, kernel replay, complete owned audit,
or cloud job has run for this package.** The existing row00 pilot remains
unchanged and pending its own run. This package prepares seven separate
successor owners, row01–07, and one composition owner importing all eight rows.
The parent authorized preparing all seven while the queued row00 pilot runs;
their execution remains gated on that pilot's actual result.

## Reuse findings

The inspected production/source-only/verification sources and receipts contain
accepted cell00 data, all eight stored Q96 floor equalities, shape/count facts,
and the original finite-core definitions. They do not contain accepted saving16
row01–07 geometric Jensen identities or `simplexValid` certificates. The exact
proposed row01 paths also have no earlier all-ref Git history.

The historical P26 row arithmetic concerns saving19: 28 vertices, 56 rows, and
different comparison/cap functions. Its concrete arithmetic facts cannot be
applied to these saving16 rows. Its unchanged generic `P2Winner9FastDetPure`
algorithm and correctness theorem are reusable. That module now has actual P1
strict normal, independent replay, and complete owned acceptance for 43
declarations. The current capsule identity is recorded in the manifest; this
package does not repeat those gates or the P1-to-P3 environment remapping.

| Existing component | Accepted owned declarations | Reused contribution |
|---|---:|---|
| `P2OriginalSaving16FiniteCore` | 29 | Original vertex lookup, volume, gap, means, Jensen and eleven-conjunct guard |
| `P2Saving16Cell00TypedPayload` | 544 | Exact named data definitions; its original-text binding is a separate chain |
| `P2Saving16Cell00StoredFloors` | 30 | Every stored Q96 floor, all shape/count facts, and the separate-floor sum |
| `P2Winner9FastDetPure` | 43 | Exact generic Gaussian determinant and equality with `Matrix.det` |

The reuse search is limited to the named local source/history/receipt scopes in
`REUSE_AND_OBLIGATION_MAP.json`. It is not a claim about every possible remote
environment or uninspected repository.

## Separate row owners

`ImbalancedChen/P2Saving16Cell00Row01Arithmetic.lean` is a mechanical successor
to the unchanged row00 source, SHA256
`2d75a057eb12c8bd77ebce748646867bac202fe1cda70fe8c0236598278bee0e`.
Only the namespace, row selector, expected ID, stored-floor theorem, and row
description change. Reverse substitution recovers the exact pilot bytes. The
patch and replacement counts are retained.

Each new row owner imports the same four modules and has the same fifteen public
source declarations. The remaining six are obtained by the same restricted
substitution for their own selector, ID, namespace and accepted stored-floor
theorem. Every reverse substitution recovers the exact pilot bytes. Row01 uses
the original vertex IDs
`[15, 14, 13, 9, 7, 6, 3, 2, 0]` through `simplexVertices`; it generates no
independent point array. Relative to row00, the selected vertex `1` becomes `2`.

The four separate closed arithmetic obligations are unchanged in form:

```lean
volume_eq : row.physicalVolume = physicalVolumeQ vertices
mean_gap_eq : row.meanGap = gapTotalQ vertices / 9
ten_means_eq : ∀ j : Fin 10,
  row.gapWeightedMeans.getD j.val 0 = meansQ vertices j
stored_jensen_expression : row.jensenBound =
  4 * row.physicalVolume * row.meanGap /
    ∏ j : Fin 10, row.gapWeightedMeans.getD j.val 0
```

The existing `fastDet_eq` rewrites the volume specification. Positive stored
volume and mean gap are checked separately and transported through the preceding
equalities. Multiplication/division/product congruence then establishes the
geometric Jensen identity. The already accepted
`simplex01_stored_jensen_floor` supplies the floor by equality transport; no
floor computation is repeated. The final target is exactly

```lean
simplex_valid : simplexValid cell00Payload (1 : Fin 8)
```

The other owners use the corresponding indices 2 through 7. All eleven original
conjuncts remain present. There is no new success premise, changed decoder,
changed determinant algorithm, or changed geometric formula.

## All-eight composition

`P2Saving16Cell00AllRowsArithmetic.lean` imports exactly row00–07 and adds three
proof-composition theorems:

```lean
cell00_simplex_operations :
  ∀ s : Fin cell00Payload.simplices.size, simplexValid cell00Payload s

cell00_geometric_jensen_floors :
  ∀ s : Fin cell00Payload.simplices.size,
    (cell00Payload.simplices[s]).jensenFloor =
      q96Floor (jensenQ (simplexVertices cell00Payload (cell00Payload.simplices[s])))

cell00_geometric_floor_sum :
  (∑ s : Fin cell00Payload.simplices.size,
    q96Floor (jensenQ (simplexVertices cell00Payload (cell00Payload.simplices[s])))) =
      13236428172062120
```

The first theorem uses finite cases and the eight row guards. The second
extracts their original eleventh conjunct. The third uses equality under the
sum and the already accepted stored-floor sum. It contains no `decide`, new
determinant computation, rational evaluation or floor computation. Its source
is not an acceptance claim: all eight exact row owners must first pass their
own gates, followed by this composition owner.

## The remaining seven rows

All entries below name existing typed-payload constants. The complete ordered
vertex IDs and all ten means are recorded in the obligation map.

| Row | Stored volume | Stored mean gap | Stored Jensen bound | Accepted stored floor |
|---|---|---|---|---|
| 01 | `rational119` | `rational105` | `rational131` | `integer003` |
| 02 | `rational132` | `rational105` | `rational145` | `integer005` |
| 03 | `rational146` | `rational105` | `rational158` | `integer007` |
| 04 | `rational159` | `rational160` | `rational172` | `integer009` |
| 05 | `rational173` | `rational174` | `rational186` | `integer011` |
| 06 | `rational187` | `rational174` | `rational197` | `integer013` |
| 07 | `rational198` | `rational174` | `rational208` | `integer015` |

Rows00–03 share the stored mean-gap constant, and rows05–07 share another one.
This equality of stored values does not itself prove equality of their different
vertex-dependent gap sums. Their geometric equalities remain separate
obligations unless a later accepted equality relates the sums.

The determinant is an 8 by 8 rational calculation in every row. The next
potential cost is the ten weighted means, each using nine vertex values and a
gap-weighted sum. The stored Jensen expression combines ten rational factors.
Row04 has the largest textual Jensen numerator/denominator, 162/175 decimal
digits, and weighted-mean components up to 20 digits. The other remaining rows
have Jensen components of at most 98 digits and weighted-mean components of at
most 13 digits. These are input-size observations, not measured Lean costs.

The row00 result should determine whether any actual subdivision is needed.
If its volume stage passes, reuse the existing representation and algorithm.
If another exact closed obligation fails because of reduction cost, separate
only that observed boundary. The seven prepared row owners retain the same
representation; no alternate algorithms or new generic cache layer are added.

## Manuscript normalization and scope

The local `argument.tex` and `numerical-appendix.tex` Git blobs were checked
against the existing pin for
`UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`.
The numerical appendix's `num:simplex-moment` gives the barycentric moment
formula. In dimension eight it yields mean gap `G / 9` and weighted factor
means `((sum factor) + (sum gap * factor) / G) / 10`.

The argument's `eq:current-eighth-saving` gives the multiplier 4 and a
denominator containing both residual factors and all eight coordinate factors.
The physical simplex volume is `abs(det(edgeMatrix)) / 8!`. The source retains
all these factors and divisors; it inserts neither a Chen quarter nor an
additional ordering factorial. This is the original finite arithmetic needed
by the manuscript calculation, not a new analytic estimate.

The included composition candidate implements the assembly of the eight row
guards and transport of the already accepted sum of eight separate floors.
Connecting its eventual accepted result to `archive 0` also requires the
accepted original-text consumer equality. No new formal acceptance or archive
transport is claimed by this source-only package.

Vertex membership in the physical source cell, pulling ownership, coverage,
the other thirteen cells, the original all-cell guards, and the integral
endpoint remain outside this package. No existing row00 source, frozen runner,
production module, or acceptance ledger was edited.
