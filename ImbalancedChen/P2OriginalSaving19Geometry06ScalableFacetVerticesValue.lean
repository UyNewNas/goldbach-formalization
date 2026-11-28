import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedFacetVertices000

/-! Complete original facet_vertices array value from a balanced tree.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FacetVerticesValue

noncomputable def arrayOpenChars : List Char := ['[']
noncomputable def arrayValue : SourceJson := .arr (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryFacetVerticesJsonBlock000)

theorem array_open_prefix :
    (sourceRest 66084).take 1 = arrayOpenChars := by rfl

theorem array_open_split : sourceRest 66084 = arrayOpenChars ++ sourceRest 66085 := by
  calc
    sourceRest 66084 = (sourceRest 66084).take 1 ++ (sourceRest 66084).drop 1 :=
      (List.take_append_drop 1 (sourceRest 66084)).symm
    _ = arrayOpenChars ++ (sourceRest 66084).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 66084).drop 1) array_open_prefix
    _ = arrayOpenChars ++ sourceRest 66085 :=
      congrArg (fun tail => arrayOpenChars ++ tail) (sourceRest_drop 66084 1)

theorem value_array_open (fuel : Nat) :
    SourceJson.value (fuel + 42) (sourceRest 66084) =
      SourceJson.array (fuel + 41) (SourceJson.white (sourceRest 66085)) [] :=
  (congrArg (SourceJson.value (fuel + 42)) array_open_split).trans (by rfl)

theorem array_all_blocks (fuel : Nat) :
    SourceJson.array (fuel + 41) (SourceJson.white (sourceRest 66085)) [] =
      .ok (arrayValue, sourceRest 69067) := by
  simpa only [arrayValue, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_FacetVertices_block_000_reverse, List.reverse_nil, List.nil_append]
    using (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.FacetVerticesBlock000.array_block_original fuel [])

theorem value_array_original (fuel : Nat) :
    SourceJson.value (fuel + 42) (sourceRest 66084) =
      .ok (arrayValue, sourceRest 69067) :=
  (value_array_open fuel).trans (array_all_blocks fuel)

#print axioms array_open_prefix
#print axioms array_open_split
#print axioms value_array_open
#print axioms array_all_blocks
#print axioms value_array_original

end FacetVerticesValue

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
