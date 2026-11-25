import ImbalancedChen.P2OriginalSaving19Geometry01DirectAllOriginalConstraintMinimaBlock000
import ImbalancedChen.P2OriginalSaving19Geometry01DirectAllOriginalConstraintMinimaBlock001
import ImbalancedChen.P2OriginalSaving19Geometry01DirectAllOriginalConstraintMinimaBlock002
import ImbalancedChen.P2OriginalSaving19Geometry01DirectAllOriginalConstraintMinimaBlock003
import ImbalancedChen.P2OriginalSaving19Geometry01DirectAllOriginalConstraintMinimaBlock004
import ImbalancedChen.P2OriginalSaving19Geometry01DirectAllOriginalConstraintMinimaBlock005
import ImbalancedChen.P2OriginalSaving19Geometry01DirectAllOriginalConstraintMinimaBlock006

/-! Composition of every original all_original_constraint_minima block; no full-array reduction.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace AllOriginalConstraintMinimaValue

noncomputable def arrayOpenChars : List Char := ['[']
noncomputable def arrayAcc000 : List SourceJson := []
noncomputable def arrayAcc001 : List SourceJson := AllOriginalConstraintMinimaBlock000.blockPush arrayAcc000
noncomputable def arrayAcc002 : List SourceJson := AllOriginalConstraintMinimaBlock001.blockPush arrayAcc001
noncomputable def arrayAcc003 : List SourceJson := AllOriginalConstraintMinimaBlock002.blockPush arrayAcc002
noncomputable def arrayAcc004 : List SourceJson := AllOriginalConstraintMinimaBlock003.blockPush arrayAcc003
noncomputable def arrayAcc005 : List SourceJson := AllOriginalConstraintMinimaBlock004.blockPush arrayAcc004
noncomputable def arrayAcc006 : List SourceJson := AllOriginalConstraintMinimaBlock005.blockPush arrayAcc005
noncomputable def arrayAcc007 : List SourceJson := AllOriginalConstraintMinimaBlock006.blockPush arrayAcc006
noncomputable def arrayValue : SourceJson := .arr (arrayAcc007.reverse)

theorem array_open_prefix :
    (sourceRest 150865).take 1 = arrayOpenChars := by rfl

theorem array_open_split : sourceRest 150865 = arrayOpenChars ++ sourceRest 150866 := by
  calc
    sourceRest 150865 = (sourceRest 150865).take 1 ++ (sourceRest 150865).drop 1 :=
      (List.take_append_drop 1 (sourceRest 150865)).symm
    _ = arrayOpenChars ++ (sourceRest 150865).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 150865).drop 1) array_open_prefix
    _ = arrayOpenChars ++ sourceRest 150866 :=
      congrArg (fun tail => arrayOpenChars ++ tail) (sourceRest_drop 150865 1)

theorem value_array_open (fuel : Nat) :
    SourceJson.value (fuel + 117) (sourceRest 150865) =
      SourceJson.array (fuel + 116) (SourceJson.white (sourceRest 150866)) [] :=
  (congrArg (SourceJson.value (fuel + 117)) array_open_split).trans (by rfl)

theorem array_all_blocks (fuel : Nat) :
    SourceJson.array (fuel + 116) (SourceJson.white (sourceRest 150866)) [] =
      .ok (arrayValue, sourceRest 152992) := by
  calc
    SourceJson.array (fuel + 116) (SourceJson.white (sourceRest 150866)) [] = SourceJson.array (fuel + 100) (SourceJson.white (sourceRest 151168)) arrayAcc001 := AllOriginalConstraintMinimaBlock000.array_block_original fuel arrayAcc000
    _ = SourceJson.array (fuel + 84) (SourceJson.white (sourceRest 151530)) arrayAcc002 := AllOriginalConstraintMinimaBlock001.array_block_original fuel arrayAcc001
    _ = SourceJson.array (fuel + 68) (SourceJson.white (sourceRest 151872)) arrayAcc003 := AllOriginalConstraintMinimaBlock002.array_block_original fuel arrayAcc002
    _ = SourceJson.array (fuel + 52) (SourceJson.white (sourceRest 152235)) arrayAcc004 := AllOriginalConstraintMinimaBlock003.array_block_original fuel arrayAcc003
    _ = SourceJson.array (fuel + 36) (SourceJson.white (sourceRest 152597)) arrayAcc005 := AllOriginalConstraintMinimaBlock004.array_block_original fuel arrayAcc004
    _ = SourceJson.array (fuel + 20) (SourceJson.white (sourceRest 152962)) arrayAcc006 := AllOriginalConstraintMinimaBlock005.array_block_original fuel arrayAcc005
    _ = .ok (arrayValue, sourceRest 152992) := AllOriginalConstraintMinimaBlock006.array_block_original fuel arrayAcc006

theorem value_array_original (fuel : Nat) :
    SourceJson.value (fuel + 117) (sourceRest 150865) =
      .ok (arrayValue, sourceRest 152992) :=
  (value_array_open fuel).trans (array_all_blocks fuel)

#print axioms array_open_prefix
#print axioms array_open_split
#print axioms value_array_open
#print axioms array_all_blocks
#print axioms value_array_original

end AllOriginalConstraintMinimaValue

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
