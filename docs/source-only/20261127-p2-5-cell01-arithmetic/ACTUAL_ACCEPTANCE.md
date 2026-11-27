# Actual Cell01 arithmetic acceptance

StoredFloors, Row00 through Row80, AllRowsArithmetic, and OriginalArithmetic
have now passed strict normal checking, stock kernel replay, and complete
owned-declaration auditing. Row00 was reused after its original acceptance.
The complete unchanged simplex guard holds for all 81 rows in the original
archive, and `cellFloorNumerator (1 : Fin 14) = 292535084187454643081`.

The original input, its successful decoding, the dependent simplex index, and
each separate Q96 floor remain bound by the accepted proofs. The immutable
generation manifests retain their creation-time source-only status; actual
acceptance is recorded in
[the sealed checkpoint](../../verification/20261127-p2-5-cell01-original-arithmetic/README.md).
This is a single-cell arithmetic result. Physical support, nonoverlap,
integration, and the full fourteen-cell P2.5 endpoint remain separate.
