import ImbalancedChen.P2OriginalSaving19Geometry06ScalableVerticesNode000To002

/-! Complete original vertices array value from a balanced tree.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace VerticesValue

noncomputable def arrayOpenChars : List Char := ['[']
noncomputable def arrayValue : SourceJson := .arr (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VerticesNode000To002.jsonItems)

theorem array_open_prefix :
    (sourceRest 41118).take 1 = arrayOpenChars := by rfl

theorem array_open_split : sourceRest 41118 = arrayOpenChars ++ sourceRest 41119 := by
  calc
    sourceRest 41118 = (sourceRest 41118).take 1 ++ (sourceRest 41118).drop 1 :=
      (List.take_append_drop 1 (sourceRest 41118)).symm
    _ = arrayOpenChars ++ (sourceRest 41118).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 41118).drop 1) array_open_prefix
    _ = arrayOpenChars ++ sourceRest 41119 :=
      congrArg (fun tail => arrayOpenChars ++ tail) (sourceRest_drop 41118 1)

theorem value_array_open (fuel : Nat) :
    SourceJson.value (fuel + 61) (sourceRest 41118) =
      SourceJson.array (fuel + 60) (SourceJson.white (sourceRest 41119)) [] :=
  (congrArg (SourceJson.value (fuel + 61)) array_open_split).trans (by rfl)

theorem array_all_blocks (fuel : Nat) :
    SourceJson.array (fuel + 60) (SourceJson.white (sourceRest 41119)) [] =
      .ok (arrayValue, sourceRest 48340) := by
  simpa only [arrayValue, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VerticesNode000To002.blockPush_reverse, List.reverse_nil, List.nil_append]
    using (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VerticesNode000To002.array_original fuel [])

theorem value_array_original (fuel : Nat) :
    SourceJson.value (fuel + 61) (sourceRest 41118) =
      .ok (arrayValue, sourceRest 48340) :=
  (value_array_open fuel).trans (array_all_blocks fuel)

#print axioms array_open_prefix
#print axioms array_open_split
#print axioms value_array_open
#print axioms array_all_blocks
#print axioms value_array_original

end VerticesValue

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
