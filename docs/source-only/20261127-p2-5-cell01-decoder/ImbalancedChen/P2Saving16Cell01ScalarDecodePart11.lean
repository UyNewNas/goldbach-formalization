import ImbalancedChen.P2OriginalSaving16DecoderChars
import ImbalancedChen.P2Saving16Cell01TypedPayload

/-! Cell01 decoder proof candidates. SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/
namespace ImbalancedChen.P2Saving16Cell01ScalarDecode
open P2OriginalSaving16OriginalArchive
open P2Saving16Cell01TypedPayload

theorem integer158_decoded :
    parseInteger (String.ofList ['2', '7', '9', '2', '3', '0', '0', '7', '8', '6', '2', '7', '1', '6', '3', '4', '3']) = .ok integer158 := by
  rw [parseInteger_ofList]
  rfl

theorem integer159_decoded :
    parseInteger (String.ofList ['1', '2', '6', '3', '1', '0', '7', '2', '2', '8', '4', '7', '4', '7', '4', '8', '5', '2']) = .ok integer159 := by
  rw [parseInteger_ofList]
  rfl

theorem integer160_decoded :
    parseInteger (String.ofList ['1', '7', '5', '9', '5', '0', '3', '6', '3', '5', '8', '9', '4', '4', '7', '9', '5']) = .ok integer160 := by
  rw [parseInteger_ofList]
  rfl

theorem integer161_decoded :
    parseInteger (String.ofList ['7', '8', '2', '2', '6', '1', '7', '1', '5', '9', '0', '3', '4', '2', '4', '3', '2']) = .ok integer161 := by
  rw [parseInteger_ofList]
  rfl

end ImbalancedChen.P2Saving16Cell01ScalarDecode
