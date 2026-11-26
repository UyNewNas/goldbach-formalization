# Original floor transport: candidate interface

## Status and scope

`ImbalancedChen/P2OriginalSaving19OriginalFloorTransport.lean` is a new,
uncompiled generic owner. No Lean process was run for this work. It certifies no
concrete row, finite family, archive parse, shape, simplex ownership, or integral.
All accepted owners retain their original bytes. The row000 original-floor
bridge is the proof-pattern donor; it is not imported or recompiled.

The three direct imports are the existing `HigherMomentsPrefix`,
`RowNumericsPure`, and `LogMomentQ96ArithmeticBridge` owners. In particular this
helper does not import `Original28918`, `Original28918FloorBinding`, `Archive`,
or `OwnedIntegral`, whose large family obligations are not premises here.

## Mathematical transport

1. `gapEvaluator_congr_through_six` uses the original five terms indexed by
   `Finset.range 5`. Thus each accessed degree `k + 2` lies between 2 and 6;
   the other accessed degree is 1. No term or rounding operation changes.
2. `totalLowerQ80_congr_through_six` preserves each factor's exact downward
   rounding and the sum of all ten factors.
3. `newFloorQ96_congr_through_six` preserves the uncapped new Q96 operator.
   The later five-clause formula still saves `max oldFloorQ96 newFloorQ96`.
4. `prefixMoments_eq_original` applies the accepted
   `normalizedMoment_eq_encoded`. It derives the actual `rationalMoment`
   equality from the nine coordinate encodings. It does not assume that
   equality or any saved floor.
5. `original_floor_and_bounds_of_encoding` transports the exact five finite
   prefix clauses to the original checker namespace and also transports both
   Q80 bounds for all ten factors.
6. `original_floor_and_bounds_of_bindings` transports a proved typed-row
   result to raw selectors only after receiving all vertex, geometry-row,
   and moment-row equalities. No bounds or raw-array success are inferred.

The two intermediate congruence wrappers accept moment equalities as ordinary
lemma parameters. The entry theorem discharges these equalities from the
coordinate encodings before applying those wrappers. There is no original
floor, integral, or all-row target among the entry theorem's assumptions.

## Exact per-row interface

Data arguments are the actual nine ordered rational vertices, geometry row,
moment record, nine gap numerators `g`, ten arrays of nine deviation numerators
`z`, ten deviation denominators `d`, and one gap scale `s`.

| Required proved premise | Existing row-owner theorem | Content |
|---|---|---|
| `hd` | `deviationDenominators_ne` | Every one of the ten natural denominators is nonzero. |
| `hs` | `gapScale_ne` | The common natural gap scale is nonzero. |
| `hg` | `gap_encoding` | Each of the nine original gaps equals `g i / s`. |
| `hz` | `deviation_encoding` | All 90 original deviations equal `z j i / d j`. |
| `hprefix` | `prefix_floor_checks` | All five saved finite floor clauses, including the exact maximum. |
| `hbounds` | `all_Q80_bounds` | All ten lower and ten strict upper Q80 bounds. |

`prefixMoments g z d` is definitionally the existing row owner's
`prefixMoment`. Consequently no full moment table or equality to the target
is an extra premise. A later closed instance should consist of an application
of the entry theorem using precisely these existing closed proofs.

The five retained clauses are:

1. The first moment equals `1 - mean / top` for every factor.
2. Every saved Q80 integer equals the original factor-floor operator.
3. The saved old Q96 field equals the geometry's Jensen floor.
4. The saved old Q96 field equals the original old-floor operator.
5. The saved new Q96 field equals the maximum of the original old and
   uncapped new-floor operators.

The ten row arithmetic conditions remain a separate mandatory input to later
geometric/analytic construction. This helper neither consumes nor proves
determinant, physical-region, gap positivity, volume, mean, or maximum-attainment
facts. Their existing `RowDataChecksFor` certificates and original-namespace
bridge remain available unchanged.

## From typed row to the original indexed family

For a single cell01 row `r : Fin 144`, use that finite owner's proved
`raw_row_eq` and `raw_vertices_eq`, and its exact raw moment-row binding. The raw
vertex expression must remain

```text
geometry.vertices[(geometry.rows[r.val]!).vertexIds[i.val]!]![j.val]!
```

with all three accesses bounded by existing no-fallback theorems. The generic
binding lemma requires coordinate equality for every `i : Fin 9` and
`j : Fin 8`; it cannot reorder or replace the nine original vertices.

After each row has its own accepted finite owner and its closed transport
instance, assemble the `Fin 144` family by finite case dispatch of those
proofs. There is no new numerical induction and no need to reevaluate the
60 rational moment literals or the ten arithmetic certificates per row.
Only then use the separately proved cell01 geometry and moment Archive aliases
to reach `OriginalRowIndex`. Other cells retain their own genuine finite row
types and bounds.

`originalFloorChecksFor_iff_originalForm` exposes the unchanged five-clause
formula with arbitrary actual raw selectors as lets. Its `Iff.rfl` proof does
not import the old family-wide `original_floor_checks : ... := by decide`.
An eventual integration can instantiate these selectors with the real Archive
selectors after the complete per-cell dispatch exists.

## Candidate acceptance order

1. Reuse the accepted source/object closure of the three direct suppliers.
2. Compile the new generic owner normally, independently replay its kernel
   proof, and run the complete owned inventory audit supplied here.
3. Restore and pin the accepted row001 finite source/object, then author a
   small closed row001 transport owner using the six premises above and exact
   raw bindings. This README is not a row001 proof or acceptance record.
4. After that pilot passes, use the same interface for other accepted rows.
   Rows 2 through 143 cannot acquire original-floor credit from the generic
   lemma alone; each must have its own accepted finite source/object first.

The `cloud_order.txt` and owned audit contain only locally prepared source.
No compile job, Git operation, or status update is submitted by this work.
