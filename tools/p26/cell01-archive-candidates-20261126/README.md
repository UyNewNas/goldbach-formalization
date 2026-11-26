# Cell01 Archive and arithmetic bridge candidates

Status: locally authored source candidates only. No Lean compilation, kernel
replay, cloud command, Git operation, or proof-acceptance claim is made by
this package. Production `ImbalancedChen/` sources are unchanged. Candidate
files are staged here under their intended module paths.

## Three owners

| Intended module suffix | Direct project imports | Result |
|---|---|---|
| `Cell01AllRowArithmetic` | `Cell01Row000Arithmetic`, `Cell01Row001Finite` through `Cell01Row143Finite` | All 144 original bounded row certificates, then the exact raw-array statement. |
| `Cell01ArchiveBridge` | `ArchiveCore`, `Geometry01ArchiveBridge`, `Moment01Decoded`, `Cell01AllOriginalFloorBridge` | The exact cell01 moment Archive alias; the five original floor clauses and ten Q80 double bounds at original Archive indices. |
| `Cell01ArchiveRowArithmetic` | The two new owners above | All ten arithmetic clauses at the same original Archive indices and vertices as the floor bridge. |

Every suffix has prefix `ImbalancedChen.P2OriginalSaving19`. The arithmetic
aggregation also directly imports `Mathlib.Tactic.FinCases`.

`Cell01ArchiveBridge` reuses the existing `geometry_one` theorem rather than
re-proving it. Its `momentParse_one` applies the existing
`momentPacked01_parse_decode` theorem to the unchanged ArchiveCore input;
`moments_one` eliminates the fallback by applying `Except.toOption.getD` to
that equality. No JSON parser or rational calculation is rerun.

The Archive selectors are the existing Cell00 donor pattern restricted to
cell one. They retain `OriginalRowIndex`, all original 144 ordinals, nine
ordered vertices, eight coordinates, ten factors, the saved maxima and the
original `rationalMoment`. The exact raw-to-concrete equalities precede
transport of every floor and Q80 conclusion. The final `_at_one` theorems
expose `Fin (originalRowCount (1 : Fin 13))` and the actual Archive lookups.

The arithmetic aggregation has 144 explicit branches. Branch `r` applies
only the existing `Cell01RowRRR.bounded_row_data_checks`; no row is omitted,
duplicated or reordered. Its raw theorem uses the existing bounded-access
equalities, and the final Archive owner uses the same selector equalities
as the floor owner. There is no new numeric guard or target-valued premise.

## Prerequisites and scope

First accept or reuse the exact source/object/normal/kernel/owned chains for
all existing suppliers, including the eleven-owner Cell01 original-floor
family. The first two new owners are independent and can be checked in either
order; the Archive arithmetic owner follows both. `owner_order.txt` gives
one valid order. No accepted supplier proof should be rerun.

The result is the original five-clause floor formula, both Q80 bounds and
the unchanged ten-clause `RowDataChecksFor` at cell-one Archive selectors.
It does not import the legacy `Archive`, `Original28918`,
`Original28918FloorBinding`, `RowNumerics`, `OwnedIntegral` or
`ActualEndpoint` monoliths. Their all-cell declarations are not accepted by
this package. Later integration may use the already available pure
`rowDataChecksFor_iff_originalForm` equivalence without adding assumptions.

There is no claim about cells other than cell01, the 28,918-row aggregate,
saved total sums, source gates, pulling ownership, actual integrals or common
history. The saved new Q96 remains the original maximum of the old and
uncapped new floor through the imported five-clause predicate.

## Audits and remaining execution risks

Each audit is an exact target-name substitution in the current family audit
template. It compares complete serialized and environment inventories,
prints every full type, rejects unsafe/partial/new-axiom owned declarations,
and checks transitive axioms against `propext`, `Classical.choice` and
`Quot.sound`. These are prepared audit sources, not audit results.

`SOURCE_MANIFEST.json` records all candidate/audit pins and each complete
project source closure. `STATIC_CHECK.json` checks exact 144-row dispatch,
supplier theorem presence, prohibited proof escapes, import closure, donor
audit equality and production-path absence. These source checks do not
establish Lean elaboration or evidence acceptance.

The material execution risks are definitional elaboration of the dependent
cell-one index, the ArchiveCore-to-Moment01 input alias, and memory usage when
loading the 144 finite owners. All three follow existing accepted source
patterns; only real normal, independent kernel and full-owned runs can settle
those risks. This package does not prepare or alter an execution driver.
