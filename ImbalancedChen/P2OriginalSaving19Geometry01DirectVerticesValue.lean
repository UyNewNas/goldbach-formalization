import ImbalancedChen.P2OriginalSaving19Geometry01DirectVerticesBlock000
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVerticesBlock001
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVerticesBlock002

/-! Composition of every original vertices block; no full-array reduction.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace VerticesValue

noncomputable def arrayOpenChars : List Char := ['[']
noncomputable def arrayAcc000 : List SourceJson := []
noncomputable def arrayAcc001 : List SourceJson := VerticesBlock000.blockPush arrayAcc000
noncomputable def arrayAcc002 : List SourceJson := VerticesBlock001.blockPush arrayAcc001
noncomputable def arrayAcc003 : List SourceJson := VerticesBlock002.blockPush arrayAcc002
noncomputable def arrayValue : SourceJson := .arr (arrayAcc003.reverse)

theorem array_open_prefix :
    (sourceRest 122798).take 1 = arrayOpenChars := by rfl

theorem array_open_split : sourceRest 122798 = arrayOpenChars ++ sourceRest 122799 := by
  calc
    sourceRest 122798 = (sourceRest 122798).take 1 ++ (sourceRest 122798).drop 1 :=
      (List.take_append_drop 1 (sourceRest 122798)).symm
    _ = arrayOpenChars ++ (sourceRest 122798).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 122798).drop 1) array_open_prefix
    _ = arrayOpenChars ++ sourceRest 122799 :=
      congrArg (fun tail => arrayOpenChars ++ tail) (sourceRest_drop 122798 1)

theorem value_array_open (fuel : Nat) :
    SourceJson.value (fuel + 67) (sourceRest 122798) =
      SourceJson.array (fuel + 66) (SourceJson.white (sourceRest 122799)) [] :=
  (congrArg (SourceJson.value (fuel + 67)) array_open_split).trans (by rfl)

theorem array_all_blocks (fuel : Nat) :
    SourceJson.array (fuel + 66) (SourceJson.white (sourceRest 122799)) [] =
      .ok (arrayValue, sourceRest 131756) := by
  calc
    SourceJson.array (fuel + 66) (SourceJson.white (sourceRest 122799)) [] = SourceJson.array (fuel + 50) (SourceJson.white (sourceRest 126451)) arrayAcc001 := VerticesBlock000.array_block_original fuel arrayAcc000
    _ = SourceJson.array (fuel + 34) (SourceJson.white (sourceRest 129957)) arrayAcc002 := VerticesBlock001.array_block_original fuel arrayAcc001
    _ = .ok (arrayValue, sourceRest 131756) := VerticesBlock002.array_block_original fuel arrayAcc002

theorem value_array_original (fuel : Nat) :
    SourceJson.value (fuel + 67) (sourceRest 122798) =
      .ok (arrayValue, sourceRest 131756) :=
  (value_array_open fuel).trans (array_all_blocks fuel)

#print axioms array_open_prefix
#print axioms array_open_split
#print axioms value_array_open
#print axioms array_all_blocks
#print axioms value_array_original

end VerticesValue

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
