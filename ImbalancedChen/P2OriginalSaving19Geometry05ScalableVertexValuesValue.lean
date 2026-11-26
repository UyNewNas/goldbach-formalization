import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVertexValuesNode000To003

/-! Complete original vertex_values array value from a balanced tree.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace VertexValuesValue

noncomputable def arrayOpenChars : List Char := ['[']
noncomputable def arrayValue : SourceJson := .arr (ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.VertexValuesNode000To003.jsonItems)

theorem array_open_prefix :
    (sourceRest 47433).take 1 = arrayOpenChars := by rfl

theorem array_open_split : sourceRest 47433 = arrayOpenChars ++ sourceRest 47434 := by
  calc
    sourceRest 47433 = (sourceRest 47433).take 1 ++ (sourceRest 47433).drop 1 :=
      (List.take_append_drop 1 (sourceRest 47433)).symm
    _ = arrayOpenChars ++ (sourceRest 47433).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 47433).drop 1) array_open_prefix
    _ = arrayOpenChars ++ sourceRest 47434 :=
      congrArg (fun tail => arrayOpenChars ++ tail) (sourceRest_drop 47433 1)

theorem value_array_open (fuel : Nat) :
    SourceJson.value (fuel + 66) (sourceRest 47433) =
      SourceJson.array (fuel + 65) (SourceJson.white (sourceRest 47434)) [] :=
  (congrArg (SourceJson.value (fuel + 66)) array_open_split).trans (by rfl)

theorem array_all_blocks (fuel : Nat) :
    SourceJson.array (fuel + 65) (SourceJson.white (sourceRest 47434)) [] =
      .ok (arrayValue, sourceRest 60862) := by
  simpa only [arrayValue, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.VertexValuesNode000To003.blockPush_reverse, List.reverse_nil, List.nil_append]
    using (ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.VertexValuesNode000To003.array_original fuel [])

theorem value_array_original (fuel : Nat) :
    SourceJson.value (fuel + 66) (sourceRest 47433) =
      .ok (arrayValue, sourceRest 60862) :=
  (value_array_open fuel).trans (array_all_blocks fuel)

#print axioms array_open_prefix
#print axioms array_open_split
#print axioms value_array_open
#print axioms array_all_blocks
#print axioms value_array_original

end VertexValuesValue

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
