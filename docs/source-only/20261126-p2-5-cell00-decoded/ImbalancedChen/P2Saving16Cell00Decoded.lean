import ImbalancedChen.P2OriginalSaving16Decoder
import ImbalancedChen.P2Saving16Cell00DirectParse

/-!
Typed decoding of the complete cell00 value certified by the unchanged
original JSON reader. The original decoder and its complete success guard
are used directly. The default below is eliminated by `cell00_decode`.
-/

namespace ImbalancedChen.P2Saving16Cell00Decoded

open P2OriginalSaving16OriginalArchive (CellRecord decodeCell)
open P2Saving16Cell00Segments (rootValue)

noncomputable def decodedCell00 : CellRecord :=
  (decodeCell rootValue).toOption.getD default

theorem cell00_decode_success :
    (match decodeCell rootValue with | .ok _ => true | .error _ => false) = true := by
  decide +kernel

theorem cell00_decode : decodeCell rootValue = .ok decodedCell00 := by
  unfold decodedCell00
  cases h : decodeCell rootValue with
  | error e =>
    have hs := cell00_decode_success
    rw [h] at hs
    cases hs
  | ok c => rfl

#print axioms cell00_decode_success
#print axioms cell00_decode

end ImbalancedChen.P2Saving16Cell00Decoded
