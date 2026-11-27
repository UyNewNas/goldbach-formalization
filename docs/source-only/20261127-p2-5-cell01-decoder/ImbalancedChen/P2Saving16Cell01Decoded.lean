import ImbalancedChen.P2Saving16Cell01FieldDecode
import ImbalancedChen.P2Saving16Cell01PayloadBinding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Cell01 specialization of the existing original-decoder proof decomposition.
All data, field order, scalar spellings and row order come from the unchanged
published typed candidate. These equalities require actual Lean checking.
No geometric validity, integral estimate, Q96 endpoint or P2.5 is asserted.
-/
namespace ImbalancedChen.P2Saving16Cell01Decoded

open P2OriginalSaving16OriginalArchive (CellRecord decodeCell)
open P2Saving16Cell01Segments (rootValue)
open P2Saving16Cell01TypedPayload (cell01Payload)
open P2Saving16Cell01PayloadBinding (rootValue_eq_rawRoot)
open P2Saving16Cell01FieldDecode (rawRoot_decoded)

noncomputable def decodedCell01 : CellRecord := cell01Payload

theorem cell01_decode : decodeCell rootValue = .ok decodedCell01 := by
  exact (congrArg decodeCell rootValue_eq_rawRoot).trans rawRoot_decoded

theorem cell01_decode_success :
    (match decodeCell rootValue with | .ok _ => true | .error _ => false) = true := by
  rw [cell01_decode]

#print axioms decodedCell01
#print axioms cell01_decode
#print axioms cell01_decode_success

end ImbalancedChen.P2Saving16Cell01Decoded
