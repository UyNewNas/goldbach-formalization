import ImbalancedChen.P2OriginalSaving19Geometry01DirectVertexValuesBlock000
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVertexValuesBlock001
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVertexValuesBlock002
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVertexValuesBlock003
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVertexValuesBlock004

/-! Composition of every original vertex_values block; no full-array reduction.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace VertexValuesValue

noncomputable def arrayOpenChars : List Char := ['[']
noncomputable def arrayAcc000 : List SourceJson := []
noncomputable def arrayAcc001 : List SourceJson := VertexValuesBlock000.blockPush arrayAcc000
noncomputable def arrayAcc002 : List SourceJson := VertexValuesBlock001.blockPush arrayAcc001
noncomputable def arrayAcc003 : List SourceJson := VertexValuesBlock002.blockPush arrayAcc002
noncomputable def arrayAcc004 : List SourceJson := VertexValuesBlock003.blockPush arrayAcc003
noncomputable def arrayAcc005 : List SourceJson := VertexValuesBlock004.blockPush arrayAcc004
noncomputable def arrayValue : SourceJson := .arr (arrayAcc005.reverse)

theorem array_open_prefix :
    (sourceRest 131778).take 1 = arrayOpenChars := by rfl

theorem array_open_split : sourceRest 131778 = arrayOpenChars ++ sourceRest 131779 := by
  calc
    sourceRest 131778 = (sourceRest 131778).take 1 ++ (sourceRest 131778).drop 1 :=
      (List.take_append_drop 1 (sourceRest 131778)).symm
    _ = arrayOpenChars ++ (sourceRest 131778).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 131778).drop 1) array_open_prefix
    _ = arrayOpenChars ++ sourceRest 131779 :=
      congrArg (fun tail => arrayOpenChars ++ tail) (sourceRest_drop 131778 1)

theorem value_array_open (fuel : Nat) :
    SourceJson.value (fuel + 76) (sourceRest 131778) =
      SourceJson.array (fuel + 75) (SourceJson.white (sourceRest 131779)) [] :=
  (congrArg (SourceJson.value (fuel + 76)) array_open_split).trans (by rfl)

theorem array_all_blocks (fuel : Nat) :
    SourceJson.array (fuel + 75) (SourceJson.white (sourceRest 131779)) [] =
      .ok (arrayValue, sourceRest 150826) := by
  calc
    SourceJson.array (fuel + 75) (SourceJson.white (sourceRest 131779)) [] = SourceJson.array (fuel + 67) (SourceJson.white (sourceRest 135711)) arrayAcc001 := VertexValuesBlock000.array_block_original fuel arrayAcc000
    _ = SourceJson.array (fuel + 59) (SourceJson.white (sourceRest 139523)) arrayAcc002 := VertexValuesBlock001.array_block_original fuel arrayAcc001
    _ = SourceJson.array (fuel + 51) (SourceJson.white (sourceRest 143200)) arrayAcc003 := VertexValuesBlock002.array_block_original fuel arrayAcc002
    _ = SourceJson.array (fuel + 43) (SourceJson.white (sourceRest 147030)) arrayAcc004 := VertexValuesBlock003.array_block_original fuel arrayAcc003
    _ = .ok (arrayValue, sourceRest 150826) := VertexValuesBlock004.array_block_original fuel arrayAcc004

theorem value_array_original (fuel : Nat) :
    SourceJson.value (fuel + 76) (sourceRest 131778) =
      .ok (arrayValue, sourceRest 150826) :=
  (value_array_open fuel).trans (array_all_blocks fuel)

#print axioms array_open_prefix
#print axioms array_open_split
#print axioms value_array_open
#print axioms array_all_blocks
#print axioms value_array_original

end VertexValuesValue

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
