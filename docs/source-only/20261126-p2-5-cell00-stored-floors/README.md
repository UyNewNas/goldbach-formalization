# Cell00 stored-floor arithmetic candidate

**SOURCE ONLY. No Lean compilation, replay, or complete-owned acceptance has
been performed for this package. The host precheck supplies no formal credit.**

The candidate imports the frozen typed payload and the unchanged original
`P2OriginalSaving16Q96FloorCore`. It imports no finite archive, original input,
JSON parser certificate, or analytic Jensen owner. No floor definition is added
or modified. The existing finite archive's `decide +kernel` proof pattern is
reused for the eight closed integer-floor equalities and small finite shapes.
No prior closed certificate for these cell00 stored floors was found.

`simplex04_stored_jensen_floor` is first because row04 has the longest stored
bound: 338 characters, with a 162-digit numerator and a 175-digit denominator.
The candidate uses that bound through `simplex04.jensenBound` and the exact
stored integer through `simplex04.jensenFloor`. It does not replace either with
a host-computed rational or a new floor operation.

The public statements cover the eight individual floor equalities, their
finite combination, the 8 simplex / 45 active8 / 16 vertex counts, the vertex
dimension and original simplex indexing/array-size conjuncts, and the integer
sum candidate `13236428172062120`. The final sum proof rewrites using the eight
individual floor equalities. It sums the separate floors, preserving the
original operation order.

Two independent bindings remain necessary: the unchanged original decoder
must return this payload, and each stored bound must equal the original
`jensenQ` expression of its simplex vertices. No statement here claims either
binding, `simplexValid`, the original cell floor numerator, or any all-cell
finite/geometry/Q96 guard. The shape statement includes no volume, positivity,
or Jensen identity.

`HOST_PRECHECK.json` records exact-input quotient/remainder candidates for
review, starting with row04. The host arithmetic agrees with all eight stored
floors; this is only a candidate-generation check. `MANIFEST.json` binds the
source, payload, unchanged floor definition, input hash, and the 17 public
candidate names. `AUDIT.lean` is the existing complete-owned audit template
instantiated for this module; any compiler-generated private declarations
must also pass that future audit.
