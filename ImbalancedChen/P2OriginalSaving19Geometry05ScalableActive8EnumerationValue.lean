import ImbalancedChen.P2OriginalSaving19Geometry05ScalableActive8EnumerationNode000To010

/-! Complete original active8_enumeration array value from a balanced tree.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace Active8EnumerationValue

noncomputable def arrayOpenChars : List Char := ['[']
noncomputable def arrayValue : SourceJson := .arr ((ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationNode000To010.blockPush []).reverse)

theorem array_open_prefix :
    (sourceRest 416).take 1 = arrayOpenChars := by rfl

theorem array_open_split : sourceRest 416 = arrayOpenChars ++ sourceRest 417 := by
  calc
    sourceRest 416 = (sourceRest 416).take 1 ++ (sourceRest 416).drop 1 :=
      (List.take_append_drop 1 (sourceRest 416)).symm
    _ = arrayOpenChars ++ (sourceRest 416).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 416).drop 1) array_open_prefix
    _ = arrayOpenChars ++ sourceRest 417 :=
      congrArg (fun tail => arrayOpenChars ++ tail) (sourceRest_drop 416 1)

theorem value_array_open (fuel : Nat) :
    SourceJson.value (fuel + 194) (sourceRest 416) =
      SourceJson.array (fuel + 193) (SourceJson.white (sourceRest 417)) [] :=
  (congrArg (SourceJson.value (fuel + 194)) array_open_split).trans (by rfl)

theorem array_all_blocks (fuel : Nat) :
    SourceJson.array (fuel + 193) (SourceJson.white (sourceRest 417)) [] =
      .ok (arrayValue, sourceRest 41065) := ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationNode000To010.array_original fuel []

theorem value_array_original (fuel : Nat) :
    SourceJson.value (fuel + 194) (sourceRest 416) =
      .ok (arrayValue, sourceRest 41065) :=
  (value_array_open fuel).trans (array_all_blocks fuel)

#print axioms array_open_prefix
#print axioms array_open_split
#print axioms value_array_open
#print axioms array_all_blocks
#print axioms value_array_original

end Active8EnumerationValue

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
