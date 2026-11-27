# Cell01: separate Q96 floors and geometric arithmetic

This continuation instantiates the existing Cell00 arithmetic construction on
the unchanged Cell01 witness from the frozen 20261106 manuscript. Its input is
344,873 bytes, SHA256
`d7215c408203fd149155ec34af91c0d3af45a49d4dc64e23b508917d176a5c2f`.
The payload contains 81 ordered simplices, 35 vertices and 495 active-eight
records. The typed data and the original finite-core operations are reused.

The generated sources preserve their authoring-time `UNCOMPILED` markers.
Acceptance belongs to the separately recorded normal, stock-kernel and complete
owned-declaration results for the exact source bytes. This README and the
generators grant no acceptance.

## Separate floors and their sum

`P2Saving16Cell01StoredFloors` supplies one theorem for each original stored
Jensen bound, the finite index/array shapes, and the exact sum

```lean
cell01_stored_jensen_floor_sum :
  (∑ s : Fin cell01Payload.simplices.size,
    (cell01Payload.simplices[s]).jensenFloor) = 292535084187454643081
```

Each of the 81 equations uses the unchanged `q96Floor` definition. The
composition theorem transports each individual equality under the sum.
Both stored-floor facts and the geometric connection are required by the
manuscript's certificate.

## Actual vertex arithmetic

Each `P2Saving16Cell01RowNNArithmetic` takes its nine vertices through
`simplexVertices cell01Payload row`. It supplies the original eleven-conjunct
`simplexValid` guard at its own `Fin 81` index. Its closed obligations check:

- the absolute 8-by-8 determinant divided by `8!`;
- the positive gap total and its nine-vertex mean;
- both residual means and all eight coordinate means, retaining the divisor 10;
- the complete stored Jensen expression with multiplier 4;
- the equality between that expression and `jensenQ` at the actual vertices.

The accepted generic `P2Winner9FastDetPure.fastDet_eq` supplies the existing
determinant algorithm's equality to `Matrix.det`. Each row reuses its own
already checked stored-floor theorem after establishing its geometric Jensen
identity. Row00's original vertex indices are `[34,26,25,22,11,7,5,1,0]`.

`P2Saving16Cell01AllRowsArithmetic` combines all 81 row guards, extracts their
floor conjuncts, and concludes the exact sum of the geometric floors:

```lean
cell01_geometric_floor_sum :
  (∑ s : Fin cell01Payload.simplices.size,
    q96Floor (jensenQ
      (simplexVertices cell01Payload (cell01Payload.simplices[s])))) =
    292535084187454643081
```

The composition has no new determinant, rational-mean, Jensen or floor decision.
Its 81 imports and 81 branches are the original ordered indices exactly once.

## Source reuse and review

`MANIFEST.json` fixes the input, exact donor and candidate sources, and frozen
manuscript paths and formula labels. `REMAINING_ROWS_MANIFEST.json` fixes the
accepted pilot/floor objects and all 80 successor rows plus their composition.
Reversing the restricted namespace, selector, index and description changes
recovers the complete pilot bytes for every successor. The composition similarly
reuses the existing Cell00 proof construction.

Both generators precheck every destination before writing and preserve any
different existing output. Reproduction is:

```sh
python3 -B generate.py --input /path/to/eighth-prefix-family-20261009-cell-01.witness.json --check
python3 -B generate_remaining_rows.py --check
```

`REVIEW.json` records independent source and rational-arithmetic inspection.
The host calculations serve as diagnostics. Kernel acceptance is recorded
separately with the exact object/source hashes and transitive axioms.

## Remaining source-region obligations

These concrete arithmetic guards do not supply the original-text binding,
membership in all 96 original source rows, face/pulling ownership, the other
cells, or the all-fourteen integral endpoint. Their connection to `archive 1`
must use the accepted original parse and exact payload equality. The existing
generic total/integral theorems remain the route to the manuscript endpoint;
they are not reimplemented here. P2.5 remains unfinished until its complete
dependency chain has passed the actual gates.
