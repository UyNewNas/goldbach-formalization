# Cell01 original parse and complete arithmetic: actual acceptance

The original Cell01 witness now has accepted parsing, decoding, all 81 row
guards, and its exact sum of individually floored geometric Jensen expressions.
The full P2.5 theorem remains unproved at this checkpoint.

The original input has SHA-256
`d7215c408203fd149155ec34af91c0d3af45a49d4dc64e23b508917d176a5c2f`.
It contains 35 vertices, 81 ordered simplex records, and the original retained
metadata. Its parser-success proof rules out the default error branch.

## Accepted original-archive conclusions

`P2Saving16Cell01OriginalParse` proves actual parse and decode success and
`archive (1 : Fin 14) = decodedCell01`, with `decodedCell01 := cell01Payload`.

`P2Saving16Cell01OriginalArithmetic` proves, without new hypotheses:

```lean
∀ s : Fin (archive (1 : Fin 14)).simplices.size,
  simplexValid (archive (1 : Fin 14)) s

cellFloorNumerator (1 : Fin 14) = 292535084187454643081
```

`simplexValid` retains all eleven original conjuncts. Each row uses its actual
vertices, the rational determinant volume, the original factors and means,
and the unchanged Q96 floor definition. The sum floors each Jensen expression
separately. It does not replace the sum by a floor of the total.

## What the records establish

The sealed cutoff covers 172 newly accepted local owners with 9,047 owned
declarations, plus 25 newly accepted P2 owners with 410 declarations: the
original JSON parser and the remaining 24 simplex decoders. In total it covers
197 new owners and 9,457 owned declarations. Forty-two historical objects were
reused with exact source and object identity. These module counts are not a
count of the manuscript's cells or of its 39,741 simplices.

Every accepted new owner has strict normal checking, stock kernel replay, and
a complete owned-declaration audit. The allowed transitive logical axioms are
`propext`, `Classical.choice`, and `Quot.sound`. Source hashes, object hashes,
raw log hashes, imports, and actual failure records are retained. The complete
module inventory is in `SUMMARY.json`; `ACCEPTANCE.json` highlights the final
original-archive owners and pins every artifact. The P2 row package also
contains the accepted objects and the 15,936-file external before/after check.

The previous successful Cell01 row 00 and accepted decoder owners were reused.
The 24 transferred P2 objects were verified and installed without recompiling
them locally. Failed attempts have no acceptance credit; in particular the
first two pulling-induction candidates remain failed at this cutoff.

## Remaining mathematical boundary

These results do not establish the cell's physical support inequalities,
geometric separation, its integral lower bound, the other twelve uncompleted
cells, or the fourteen-cell Q96 endpoint. Pulling and geometry have separate
sources and separate acceptance records. The 377-module analytic continuation
also keeps its own actual round receipts. No whole P2.5 status is promoted by
this checkpoint.
