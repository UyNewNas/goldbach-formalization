import ImbalancedChen.P2OriginalSaving19Geometry05ScalableRowsNode000To006

/-! Complete original simplices array value from a balanced tree.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesValue

noncomputable def arrayOpenChars : List Char := ['[']
noncomputable def arrayValue : SourceJson := .arr (ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.Node000To006.jsonRows)

theorem array_open_prefix :
    (sourceRest 104496).take 1 = arrayOpenChars := by rfl

theorem array_open_split : sourceRest 104496 = arrayOpenChars ++ sourceRest 104497 := by
  calc
    sourceRest 104496 = (sourceRest 104496).take 1 ++ (sourceRest 104496).drop 1 :=
      (List.take_append_drop 1 (sourceRest 104496)).symm
    _ = arrayOpenChars ++ (sourceRest 104496).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 104496).drop 1) array_open_prefix
    _ = arrayOpenChars ++ sourceRest 104497 :=
      congrArg (fun tail => arrayOpenChars ++ tail) (sourceRest_drop 104496 1)

theorem value_array_open (fuel : Nat) :
    SourceJson.value (fuel + 474) (sourceRest 104496) =
      SourceJson.array (fuel + 473) (SourceJson.white (sourceRest 104497)) [] :=
  (congrArg (SourceJson.value (fuel + 474)) array_open_split).trans (by rfl)

theorem array_all_blocks (fuel : Nat) :
    SourceJson.array (fuel + 473) (SourceJson.white (sourceRest 104497)) [] =
      .ok (arrayValue, sourceRest 200699) := by
  simpa only [arrayValue, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.Node000To006.blockPush_reverse, List.reverse_nil, List.nil_append]
    using (ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.Node000To006.array_original fuel [])

theorem value_array_original (fuel : Nat) :
    SourceJson.value (fuel + 474) (sourceRest 104496) =
      .ok (arrayValue, sourceRest 200699) :=
  (value_array_open fuel).trans (array_all_blocks fuel)

#print axioms array_open_prefix
#print axioms array_open_split
#print axioms value_array_open
#print axioms array_all_blocks
#print axioms value_array_original

end SimplicesValue

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
