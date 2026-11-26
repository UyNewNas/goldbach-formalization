# Cell01 original floor family: all 144 source candidates

The complete source family now has eleven new owners: one shared raw
interface, nine blocks of sixteen original rows each, and one final
`∀ r : Fin 144` aggregation. These are authored Lean source candidates.
They have not been compiled, kernel-replayed, or given complete owned audits
by this preparation task. Source presence does not establish acceptance.

## Exact source structure

| Order | Owner suffix | Original ordinals |
|---|---|---|
| 1 | Cell01OriginalFloorInterface | Shared `Fin 144` selectors and access bounds |
| 2 | Cell01OriginalFloorBlock000_015 | 000–015 |
| 3 | Cell01OriginalFloorBlock016_031 | 016–031 |
| 4 | Cell01OriginalFloorBlock032_047 | 032–047 |
| 5 | Cell01OriginalFloorBlock048_063 | 048–063 |
| 6 | Cell01OriginalFloorBlock064_079 | 064–079 |
| 7 | Cell01OriginalFloorBlock080_095 | 080–095 |
| 8 | Cell01OriginalFloorBlock096_111 | 096–111 |
| 9 | Cell01OriginalFloorBlock112_127 | 112–127 |
| 10 | Cell01OriginalFloorBlock128_143 | 128–143 |
| 11 | Cell01AllOriginalFloorBridge | All original `Fin 144` rows |

Every suffix above has the prefix `ImbalancedChen.P2OriginalSaving19`.
The first two owners are byte-identical to the previously frozen pilot.
The remaining nine owners are the only added Lean sources in this extension.

The final theorem is:

```lean
theorem all_original_floor_and_bounds :
    ∀ r : Fin 144, OriginalFloorAndBoundsAt r
```

It has 144 explicit `exact` branches after `fin_cases r`. Branch `r` uses
block `r / 16` and position `r % 16`; each block's map returns the original
ordinal `16 * block + position`. No row is skipped, duplicated or reordered.
Two projection theorems expose the original five-clause floor formula and
the ten Q80 double bounds separately for later consumers.

## Mathematical meaning and discharged inputs

The shared raw interface keeps `Fin 144` rows, the original ordered `Fin 9`
vertices, all `Fin 8` coordinates, and `Fin 10` factors. Its original vertex
lookup is still row → vertex ID → vertex → coordinate. Geometry rows and
moment rows use the same original ordinal. All original `!` lookups are
connected to already proved bounded accesses, including factor maxima,
weighted means, and saved Q80 integers.

`rawOriginalMoments` explicitly calls
`P2OriginalSaving19HigherMoments.rationalMoment`. The derived row statement
contains the original five floor clauses:

1. The degree-one original rational moment agrees with the original mean.
2. Every saved Q80 integer equals the original checker's factor floor.
3. The saved old Q96 integer equals the geometry's Jensen integer.
4. The saved old Q96 integer equals the original old operator.
5. The saved new Q96 integer equals `max(old, uncapped new)`.

For each of the ten factors it also contains the lower Q80 inequality and
the strict upper inequality. The saved maximum is never silently replaced
by the uncapped new operator.

The row000 transport reuses the already accepted row000 original bridge's
floor formula and Q80 bounds. For each other row, the unchanged generic
entry theorem is instantiated with six finite facts: nonzero deviation
denominators, a nonzero gap scale, exact gap encoding, exact deviation
encoding, all five prefix floor clauses, and all Q80 double bounds. The
three existing raw equalities then bind the typed vertices, geometry row,
and moment row to the original array lookups. Every resulting typed and raw
row theorem has no proof-premise parameters. The block and final theorems
only take their finite index; they add no arithmetic or floor hypothesis.

All imported finite sources retain their original ten arithmetic conditions,
sixty moment calculations per row, twenty Q80 inequalities, and five prefix
floor clauses. This extension does not recompute any numeric value. Its only
generated numeric values are the original ordinal and block-position labels.

## Frozen prior work

The following mathematical sources and packages remain unchanged:

- Generic transport source:
  `9f4b64321975f8eb567484982abc622ee77ac222c90a6d117b2acc7a0f39b574`.
- Accepted row000 original bridge:
  `044746b6376ae5efdac05dd97b77ba9840c91435001acf3e7a402015b272ede8`.
- Pilot interface:
  `dcfebb22ceae165a75e78fbc612a4b0d46ef3381e81cf637f71d6d45c8d5d504`.
- Pilot block000–015:
  `78c649f07f8000949d807a800162eaa1c8025cd335b0a4370144510456346b66`.
- Pilot source-only package:
  `e41581d10a25f95d59ddd1b679b69dc55efd06fa79ce4346ba8c0f4b5fb45f65`.

All 143 finite source hashes are checked against the restored series
manifest before and after authoring and packaging. The full source closure
is recorded with every module's SHA256, byte count and project imports.
These source pins do not imply that every accepted object is available in
one environment.

## Verification and acceptance boundary

Before executing any new owner, supply the same-source accepted generic and
the required exact finite, decoding, arithmetic and analytic objects,
together with their normal/kernel/owned receipt chains and runtime context.
The coordinator has reported the unchanged generic owner fully accepted in
P1 job `2bb6e4af6d9e49f78cf6f7026a7fb90b`; its three accepted steps and
runtime evidence must be supplied, rather than inferred from this source
package. The finite batches are coordinated separately. This package never
infers acceptance from an earlier source header, declaration,
or static check, and never authorizes rerunning an accepted supplier proof.

`cloud_order.txt` lists normal, exact stock leanchecker, and full owned audit
for each of the eleven new owners in dependency order. These are pending
steps, not executed commands. Any already accepted same-source pilot owner
must instead be reused with its complete validated receipt chain. This
source package includes no new execution driver and submits no jobs.

Each owner has a locally authored complete owned-audit source. It compares
serialized and environment ownership inventories, prints every complete
type, rejects unsafe/partial/new-axiom owned declarations, and checks the
full transitive axiom list against propext, Classical.choice, and Quot.sound.
Actual owned counts remain pending the real audits.

The source package contains the eleven target sources, eleven audit sources,
source and generation manifests, static checks, documentation and the local
authoring tools. Old supplier source/object bodies and completed-evidence
archives are excluded. The blocked row001 completed archive is not accessed
or transferred. This family makes no Archive-alias claim, integral claim,
all-cell claim, or P2.6-completion claim.

## Exact P1 supplier difference

`SUPPLIER_DELTA.json` compares all 791 suppliers against the original 23rd
attempt's 1,111-module canonical registry, using the published local evidence
INPUT at SHA256
`67ac94afd5e2c3466b0b728c7cc95a574e8b840d5cc5d92fc3bf6f96f5c40e32`.
The comparison has 646 exact module/source-size/source-SHA matches and no
same-module conflicts. It records each real canonical source provider,
the accepted object-union path, and exact sidecars; it does not assume that
old supplier source files are under the 23rd attempt's project directory.

The remaining 145 suppliers are exactly the 143 finite owners, the generic
owner, and the accepted row000 original bridge. The last is the 23rd attempt's
own target, so it is correctly absent from its own canonical import table;
its accepted RESULT and three seal identities supply its source/object pins.
The two separately accepted Archive bridges are outside this family closure.

At the coordinator's reported snapshot, finite001–106 and generic were
accepted, giving 754 known accepted suppliers including the 646 old entries
and row000 target. Only finite107–143, 37 owners, remained running on P3.
No other unclassified or unverified supplier owner was found. The comparison
does not itself inspect physical cloud cache presence or replace any receipt
validation before staging.

The included independent mathematical review covers the two-owner pilot,
its original rows 000–015 data, and a limited check of the final 144-row
dispatch and statement. It found no source correction required. It is not
a Lean acceptance and does not claim to rerun the remaining 128 rows' data
or numerical proofs. The other block sources are exact renderings of the
unchanged pilot generator, with the actual corresponding finite interfaces.

## Local authoring commands

The existing generator was used without modification:

```text
python -B tools/p26/original-floor-family/generate_cell01_transport_blocks.py \
  --blocks 1 2 3 4 5 6 7 8 \
  --report tools/p26/original-floor-family/cell01-family/GENERATION.json
```

The final aggregation was authored separately:

```text
python -B tools/p26/original-floor-family/prepare_cell01_transport_family.py --author
```

Both commands refuse to overwrite existing outputs. The later `--freeze`
mode verifies exact renderings, donor pins, ordinal coverage, forbidden
mechanisms, complete project source availability and tar payloads before
publishing the source-only package metadata. It does not run Lean.
