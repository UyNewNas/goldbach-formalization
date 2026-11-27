import ImbalancedChen.P2Saving16Cell03FieldDecode
import ImbalancedChen.P2Saving16Cell03PayloadBinding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Cell03 specialization of the existing original-decoder proof decomposition.
All data, field order, scalar spellings and row order come from the unchanged
published typed candidate. These equalities require actual Lean checking.
No geometric validity, integral estimate, Q96 endpoint or P2.5 is asserted.
-/
namespace ImbalancedChen.P2Saving16Cell03Decoded

open P2OriginalSaving16OriginalArchive (CellRecord decodeCell)
open P2Saving16Cell03Segments (rootValue)
open P2Saving16Cell03TypedPayload (cell03Payload)
open P2Saving16Cell03PayloadBinding (rootValue_eq_rawRoot)
open P2Saving16Cell03FieldDecode (rawRoot_decoded)

noncomputable def decodedCell03 : CellRecord := cell03Payload

theorem cell03_decode : decodeCell rootValue = .ok decodedCell03 := by
  exact (congrArg decodeCell rootValue_eq_rawRoot).trans rawRoot_decoded

theorem cell03_decode_success :
    (match decodeCell rootValue with | .ok _ => true | .error _ => false) = true := by
  rw [cell03_decode]

#print axioms decodedCell03
#print axioms cell03_decode
#print axioms cell03_decode_success

end ImbalancedChen.P2Saving16Cell03Decoded
