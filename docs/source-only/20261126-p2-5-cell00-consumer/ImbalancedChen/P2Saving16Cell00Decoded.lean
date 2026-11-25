import ImbalancedChen.P2Saving16Cell00FieldDecode
import ImbalancedChen.P2Saving16Cell00PayloadBinding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Compose the exact complete AST identity with the field-by-field certificate
for the unchanged original typed decoder. The returned record is the named
literal payload. These three API names replace the failed monolithic
consumer only when this source and its exact checked dependencies are
selected together. No decoder or success premise is introduced.
-/
namespace ImbalancedChen.P2Saving16Cell00Decoded

open P2OriginalSaving16OriginalArchive (CellRecord decodeCell)
open P2Saving16Cell00Segments (rootValue)
open P2Saving16Cell00TypedPayload (cell00Payload)
open P2Saving16Cell00PayloadBinding (rootValue_eq_rawRoot)
open P2Saving16Cell00FieldDecode (rawRoot_decoded)

noncomputable def decodedCell00 : CellRecord := cell00Payload

theorem cell00_decode : decodeCell rootValue = .ok decodedCell00 := by
  exact (congrArg decodeCell rootValue_eq_rawRoot).trans rawRoot_decoded

theorem cell00_decode_success :
    (match decodeCell rootValue with | .ok _ => true | .error _ => false) = true := by
  rw [cell00_decode]

#print axioms decodedCell00
#print axioms cell00_decode
#print axioms cell00_decode_success

end ImbalancedChen.P2Saving16Cell00Decoded
