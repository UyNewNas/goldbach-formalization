# Cell01 original floor transport: first 16-row pilot

This is a source-only candidate. No Lean command, kernel replay, owned audit,
cloud proof job, Git action, or STATUS update has been run by the author for
these new owners. A source declaration is not an acceptance receipt.

## Two new owners in dependency order

1. `ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorInterface` defines the
   original cell01 selectors and the original rational moments, and reuses
   the existing geometry and moment bounds. It proves no row's floor formula.
2. `ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock000_015` derives
   the five original floor clauses and both Q80 inequalities for ordinals
   000 through 015. Its final theorem combines exactly those sixteen closed
   row results through an order-preserving `Fin 16 → Fin 144` map.

Both owners require their own normal, stock leanchecker, and full owned
acceptance. The frozen audit sources compare serialized and environment
inventories, print every complete type, reject unsafe/partial/new-axiom
declarations, and check all transitive axioms against propext,
Classical.choice, and Quot.sound. No selected-declaration shortcut is used.

## Original mathematical target

The shared `OriginalFloorAndBoundsAt (r : Fin 144)` means all of:

- The degree-one rational moment agrees with the original gap-weighted mean.
- Each saved Q80 integer equals the original checker's factor floor.
- The saved old Q96 integer equals the geometry's Jensen integer.
- The saved old Q96 integer equals the original old operator.
- The saved new Q96 integer equals the maximum of the old operator and the
  uncapped original new operator.
- Each of the ten original gap-evaluator values satisfies both Q80 floor
  inequalities, including the strict upper bound.

`rawOriginalMoments` explicitly uses
`P2OriginalSaving19HigherMoments.rationalMoment`. It reads the original
decoded cell01 geometry and moment rows with the same ordinal. Vertices keep
the original order: row, ordered vertex ID, vertex coordinates. The finite
types remain `Fin 144`, `Fin 9`, and `Fin 8` respectively; factors use `Fin 10`.
The interface supplies the proved bounds for the row lookups, all three raw
vertex lookup levels, factor maxima, weighted means, and saved Q80 fields.

For row000 the block reuses the already accepted
`Cell01Row000OriginalFloorBridge.original_floor_formula` and
`original_Q80_bounds`; it does not repeat that original transport proof.
For rows001–015, the generic entry point receives the six existing finite
facts: nonzero denominator and gap scale, the exact gap and deviation
encodings, the five prefix floor clauses, and all Q80 bounds. Its definition
of the actual moments is supplied by the unchanged generic owner. Every row
then uses its three proved raw bindings for vertices, geometry row, and
moment row. The row theorems have no proof-premise parameters.

The imported finite owners retain their original ten arithmetic conditions,
sixty moment calculations, twenty Q80 inequalities, and five floor clauses.
This pilot adds no numeric literal, moment computation, or alternative
arithmetic solver. In particular, it never replaces the saved maximum by an
assumption that it equals the uncapped new Q96 result.

## Source and acceptance boundaries

The unchanged generic source is fixed at
`9f4b64321975f8eb567484982abc622ee77ac222c90a6d117b2acc7a0f39b574`.
The unchanged accepted row000 original bridge is fixed at
`044746b6376ae5efdac05dd97b77ba9840c91435001acf3e7a402015b272ede8`.
All 143 finite source hashes were compared before and after generation with
the restored series manifest; row001 remains
`c15da8c66ab55245dfab3ea2bbcdbc7c070dbe71bff6e7da38b476ce44808876`.

The coordinating agent has reported the earlier finite acceptances and is
arranging the generic acceptance. This package does not carry supplier
objects or receipt bodies. Before execution, the coordinator must supply the
same-source accepted generic, finite, decoding, arithmetic, and analytic
closure and validate their actual object/context pins. The complete project
source closure is listed in `SOURCE_MANIFEST.json`; it is not represented as
a claim that all corresponding objects are present in one environment.

The row001 completed-evidence archive is not read, packaged, or transferred.
The pilot does not assert an Archive alias, an integral bound, an all-cell
result, or completion of P2.6.

## Route to the full original 144-row guard

Use nine block owners, each containing sixteen short transports:
000–015, 016–031, 032–047, 048–063, 064–079, 080–095, 096–111,
112–127, and 128–143. They share one raw interface. A final owner can state

```lean
theorem all_original_floor_and_bounds (r : Fin 144) :
    OriginalFloorAndBoundsAt r := by
  fin_cases r
  -- one exact block theorem application per original ordinal
```

Each branch uses block `r.val / 16` and position `r.val % 16`; the block's
ordinal map is `16 * block + position`. There is no extra target hypothesis.
This gives eleven new owners in total: one interface, nine blocks, and one
final finite aggregation, instead of one runner per row.

Only the interface and block 000–015 are authored in this pilot. The other
eight blocks and final all-144 theorem are not claimed to exist or to be
accepted. The local generator defaults to block 0, checks every donor pin,
and refuses to overwrite any existing output. After the pilot's real
resource use is measured, the coordinator can choose when to author and
verify the remaining blocks. `FAMILY_PLAN.json` records the exact ordinal
coverage and this pending boundary.
