# Cell01 original typed geometry continuation

This continuation recovers previously completed work and advances only the
remaining typed decoder and shape obligations. It does not change any existing
parser, schema, cell00 theorem, moment theorem, or root import.

## Exact input and semantic boundary

The input is
`eighth-third-minorant-extension-20261009-a23-s23_low-01-cell.witness.json`,
470,901 bytes, SHA-256
`e19eee9d7e282cd3a618a71f12e93bcce28319485c9d0fd31bbeaf9f81a995a4`.

The original complete cell01 parser has already been certified. Its full JSON
AST retains all 14 original root fields. The continuation applies the unchanged
`P2OriginalSaving19Archive.decodeGeometry` to that actual AST and constructs the
concrete value of the unchanged eight-field `Geometry` structure. Each original
`GeometryRow` is decoded through all eight fields of the unchanged row schema.
Additional JSON fields that the original schema does not select remain in the
original parsed AST; this continuation does not redefine the decoder.

The concrete collections have 40 vertices, 40 vertex-value records, 144 simplex
rows, 12 facet-index records, 12 facet-vertex records, and 79 face-ledger records.
All raw rational tokens are quoted by the existing renderer and checked by the
original rational decoder, including its integer parsing and nonzero-denominator
guards. Host quotation and host JSON checks are not proof.

## Recovered acceptance boundary

The recovery snapshot is:

`/workspace/p26-recovery-candidates/geometry-direct-packed/attempts/cell01-full-v2/typed-v1`

Exactly 96 typed owners have matching current-source normal and kernel receipts:

- `Geometry01DirectDecodeFields`.
- `Geometry01DirectDecodedVertices000` through `002`: all 40 vertices.
- `Geometry01DirectDecodedVertexValues000` through `004`: all 40 records.
- `Geometry01DirectDecodedFacetVertices000`: all 12 records.
- `Geometry01DirectDecodedFaces000` through `019`: all 79 faces.
- `Geometry01DirectDecodedRows000` through `065`: simplex rows 0 through 129.

These 96 owners are copied byte-for-byte under their original module names.
Their accepted objects are reused, not recompiled.

`Geometry01DirectDecodedRows066`, containing rows 130 and 131, has a successful
normal receipt and its exact object. The old kernel driver reached its receipt
write and then failed with `OSError: [Errno 28] No space left on device`.
The old kernel result file is empty. This owner is explicitly **normal-only**;
the replay log by itself is not counted as acceptance. Only its kernel replay
needs to be repeated.

No archived Rows067--072, complete typed decoder, or shape success was found.

## New source-only owners

The new row modules `Geometry01DirectDecodedRows067` through `072` preserve the
existing field-wise proof pattern and cover rows 132 through 143. The cumulative
list proofs preserve the original order and join the complete parsed row array
to all 144 typed records.

`P2OriginalSaving19Geometry01Decoded` introduces the namespace
`ImbalancedChen.P2OriginalSaving19Geometry01Decoding`, with:

- `concreteGeometry01`.
- `decode_originalGeometryJson01`.
- `geometryPacked01_parse_decode`.

The last theorem has the full original input and original decoder in its
statement:

```lean
(SourceJson.parse (String.ofList geometryPacked01.toList) >>= decodeGeometry) =
  .ok concreteGeometry01
```

`Geometry01ShapeBase` states exact metadata and cardinalities. Eighteen
`Geometry01ShapeRowsNNN` modules check eight original rows each. Five
`Geometry01ShapeVerticesNNN` modules check eight original vertices each. The
final `Geometry01Shape` theorem combines those finite pieces by arithmetic
interval reasoning; it does not decide the entire collection in one kernel
computation. Its `all_rows` quantifies over `Fin 144`, and its `all_vertices`
quantifies over the actual decoded vertex-array size.

Shape covers the original row index, nine distinct and in-range vertex IDs,
ten factor maxima, ten gap-weighted means, eight coordinates per vertex, and
ten factors per vertex-value record. It does not assert geometric coverage,
determinant validity, analytic inequalities, numerical floor acceptance, or an
all-cells result.

## Cloud handoff and cache

The supplier package is:

`/dev/shm/p26-59264dd64286/geometry01-suppliers.tar.xz`

SHA-256:
`c5717cac83aba2f0ee10c8def1cb604ff101717258d28a8e404fbad915d9078d`

It contains 278 accepted suppliers (the 180-module parser closure, two generic
schema/rational suppliers, and 96 accepted typed owners), Rows066 separately as
normal-only, and the 32 new source-only modules. Accepted source and object
fingerprints and the applicable normal/kernel receipts have been checked.
Archived objects are under `objects/ImbalancedChen`; sources are under
`project/ImbalancedChen`. The exact inventory is
`Geometry01Decoding_SUPPLIERS.json` and the compile order is
`Geometry01Decoding_CONTINUATION.json`.

The required sequence is:

1. Kernel replay only for `Geometry01DirectDecodedRows066`.
2. Normal compile and kernel replay for Rows067 through Rows072, in order.
3. Normal compile and kernel replay for `Geometry01Decoded`.
4. `Geometry01ShapeBase`.
5. The 18 row shape blocks and five vertex shape blocks; these are independent
   once the base is available.
6. `Geometry01Shape`.

The generator `tools/p26/Geometry01Decoding_continue.py` pins and reuses the four
archived quotation/generation sources, writes only the isolated `/tmp` checkout,
and never invokes Lean. `Geometry01Decoding_suppliers.py` audits and packages
existing evidence without compiling or modifying archived work.

## Current verification status

No local Lean compiler or cloud compiler was invoked by this continuation.
The fixture hash, all 129 copied/new Lean source fingerprints, source import
availability, forbidden-token scan, and host shape sanity checks were verified.
The new 32 owners and the missing Rows066 kernel receipt remain subject to the
coordinator's cloud compilation and kernel replay. This document does not claim
that the full new typed decoder or shape result has already passed.

## Cloud acceptance of the continuation

The 33 continuation targets were accepted by P3 task `69006747f6bf4de485b450110dcdc397`: 32 new normal compilations, 33 independent kernel replays, and 33 full owned-declaration audits covering 1,015 declarations. The previously normal-only Rows066 object was replayed without recompilation. All 278 existing accepted supplier modules were reused unchanged.

The complete evidence archive is `geometry01-decoded-shape/evidence.tar.xz` (SHA-256 `f745da8b3351998d942c247db23ee56518c222cf9c3db95277a7254777da50df`). Its 434 files, including every new source and object, were checked again after transfer. The source-generation manifests above retain their pre-compilation status as provenance; the new acceptance manifest and main STATUS.json carry the current acceptance result.

This closes original cell01 geometry parsing, typed decoding and the stated finite shape facts. It does not close cell01 arithmetic/floor certificates, Archive alias bridges, physical simplex integration, all13 guards, or P2.6.
