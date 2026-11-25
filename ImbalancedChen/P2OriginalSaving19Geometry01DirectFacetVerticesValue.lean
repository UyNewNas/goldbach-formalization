import ImbalancedChen.P2OriginalSaving19Geometry01DirectFacetVerticesBlock000

/-! Composition of every original facet_vertices block; no full-array reduction.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FacetVerticesValue

noncomputable def arrayOpenChars : List Char := ['[']
noncomputable def arrayAcc000 : List SourceJson := []
noncomputable def arrayAcc001 : List SourceJson := FacetVerticesBlock000.blockPush arrayAcc000
noncomputable def arrayValue : SourceJson := .arr (arrayAcc001.reverse)

theorem array_open_prefix :
    (sourceRest 153015).take 1 = arrayOpenChars := by rfl

theorem array_open_split : sourceRest 153015 = arrayOpenChars ++ sourceRest 153016 := by
  calc
    sourceRest 153015 = (sourceRest 153015).take 1 ++ (sourceRest 153015).drop 1 :=
      (List.take_append_drop 1 (sourceRest 153015)).symm
    _ = arrayOpenChars ++ (sourceRest 153015).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 153015).drop 1) array_open_prefix
    _ = arrayOpenChars ++ sourceRest 153016 :=
      congrArg (fun tail => arrayOpenChars ++ tail) (sourceRest_drop 153015 1)

theorem value_array_open (fuel : Nat) :
    SourceJson.value (fuel + 49) (sourceRest 153015) =
      SourceJson.array (fuel + 48) (SourceJson.white (sourceRest 153016)) [] :=
  (congrArg (SourceJson.value (fuel + 49)) array_open_split).trans (by rfl)

theorem array_all_blocks (fuel : Nat) :
    SourceJson.array (fuel + 48) (SourceJson.white (sourceRest 153016)) [] =
      .ok (arrayValue, sourceRest 156628) := by
  calc
    SourceJson.array (fuel + 48) (SourceJson.white (sourceRest 153016)) [] = .ok (arrayValue, sourceRest 156628) := FacetVerticesBlock000.array_block_original fuel arrayAcc000

theorem value_array_original (fuel : Nat) :
    SourceJson.value (fuel + 49) (sourceRest 153015) =
      .ok (arrayValue, sourceRest 156628) :=
  (value_array_open fuel).trans (array_all_blocks fuel)

#print axioms array_open_prefix
#print axioms array_open_split
#print axioms value_array_open
#print axioms array_all_blocks
#print axioms value_array_original

end FacetVerticesValue

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
