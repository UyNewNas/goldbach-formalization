# Independent review: Moment00Shape

**Result:** no semantic scope or fallback issue found in the six stated shape theorems. This is a read-only review of source and existing receipts; no compiler was run.

The reviewed source is `P2OriginalSaving19Moment00Shape.lean`, 2480 bytes, SHA256 `1c077c3ed062c0682fe11af0b530458b734b490f4415f6d7d77323e26cd11159`. It imports the already decoded original moment00 value. The existing `momentPacked00_parse_decode` theorem binds that concrete value to the unchanged original reader and decoder on the production-compatible packed input.

## Exact scope

| Theorem | Checked scope |
|---|---|
| `metadata` | Nine equalities matching the moment portion of `Archive.CellShape`: cell 0, exact source witness filename, dimension 8, 9 vertices, 10 factors, log degree 6, exp degree 3, denominators 2^80 and 2^96. |
| `row_count` | Actual decoded array size 56, matching `originalRowCount 0`. |
| `row_bound` | Each `Fin 56` index is in bounds in that actual array. |
| `row_lookup_no_fallback` | `getElem!` equals bounded lookup, using the explicit actual array, index and bound. |
| `row_ids_and_floor_sizes` | Every one of the 56 rows has the expected simplex ID and exactly ten factor-floor entries. |
| `row_ids_and_floor_sizes_bounded` | The same row clauses hold for bounded lookup. |

The row clauses match the moment portions of the original `Archive.RowShape`. No fallback value is used in their bounded interpretation. No inequality or numerical validity claim is made about saved floors. Geometry clauses, the other twelve cells, complete `CellShape`/`RowShape`, and P1 original-path acceptance remain outside this owner’s scope.

## Evidence inspected

The existing normal and independent kernel receipts both succeed for the same source and object. Normal: 2.1088 seconds, peak 2,187,411,456 bytes. Kernel: 2.0020 seconds, peak 1,851,883,520 bytes. The six printed theorem axiom sets have union `{propext}`. Object SHA256: `c8c151d48f14c9ab0b416c026443ce8ed329cf3336ddcc6808edd067db82f8b6`.

All 42 supplier modules were checked against `BOOTSTRAP.json`: 168 original/copy source/object file records match their exact recorded sizes and SHA256 hashes. No supplier was compiled or changed in this review.

The preserved failed v1 has no object. Its only source difference from accepted v2 is replacing the two implicit placeholders in `getElem!_pos _ _ (row_bound i)` with the explicit actual array and index. No theorem statement or proof obligation changed.

The JSON companion records exact paths/hashes for source, original contracts, receipts, supplier checks and the failed baseline. The review did not alter either the shape source or the direct-packed raw pilot.
