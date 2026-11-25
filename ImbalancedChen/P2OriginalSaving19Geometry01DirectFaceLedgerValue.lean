import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock000
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock001
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock002
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock003
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock004
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock005
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock006
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock007
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock008
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock009
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock010
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock011
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock012
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock013
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock014
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock015
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock016
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock017
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock018
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerBlock019

/-! Composition of every original face_ledger block; no full-array reduction.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FaceLedgerValue

noncomputable def arrayOpenChars : List Char := ['[']
noncomputable def arrayAcc000 : List SourceJson := []
noncomputable def arrayAcc001 : List SourceJson := FaceLedgerBlock000.blockPush arrayAcc000
noncomputable def arrayAcc002 : List SourceJson := FaceLedgerBlock001.blockPush arrayAcc001
noncomputable def arrayAcc003 : List SourceJson := FaceLedgerBlock002.blockPush arrayAcc002
noncomputable def arrayAcc004 : List SourceJson := FaceLedgerBlock003.blockPush arrayAcc003
noncomputable def arrayAcc005 : List SourceJson := FaceLedgerBlock004.blockPush arrayAcc004
noncomputable def arrayAcc006 : List SourceJson := FaceLedgerBlock005.blockPush arrayAcc005
noncomputable def arrayAcc007 : List SourceJson := FaceLedgerBlock006.blockPush arrayAcc006
noncomputable def arrayAcc008 : List SourceJson := FaceLedgerBlock007.blockPush arrayAcc007
noncomputable def arrayAcc009 : List SourceJson := FaceLedgerBlock008.blockPush arrayAcc008
noncomputable def arrayAcc010 : List SourceJson := FaceLedgerBlock009.blockPush arrayAcc009
noncomputable def arrayAcc011 : List SourceJson := FaceLedgerBlock010.blockPush arrayAcc010
noncomputable def arrayAcc012 : List SourceJson := FaceLedgerBlock011.blockPush arrayAcc011
noncomputable def arrayAcc013 : List SourceJson := FaceLedgerBlock012.blockPush arrayAcc012
noncomputable def arrayAcc014 : List SourceJson := FaceLedgerBlock013.blockPush arrayAcc013
noncomputable def arrayAcc015 : List SourceJson := FaceLedgerBlock014.blockPush arrayAcc014
noncomputable def arrayAcc016 : List SourceJson := FaceLedgerBlock015.blockPush arrayAcc015
noncomputable def arrayAcc017 : List SourceJson := FaceLedgerBlock016.blockPush arrayAcc016
noncomputable def arrayAcc018 : List SourceJson := FaceLedgerBlock017.blockPush arrayAcc017
noncomputable def arrayAcc019 : List SourceJson := FaceLedgerBlock018.blockPush arrayAcc018
noncomputable def arrayAcc020 : List SourceJson := FaceLedgerBlock019.blockPush arrayAcc019
noncomputable def arrayValue : SourceJson := .arr (arrayAcc020.reverse)

theorem array_open_prefix :
    (sourceRest 156648).take 1 = arrayOpenChars := by rfl

theorem array_open_split : sourceRest 156648 = arrayOpenChars ++ sourceRest 156649 := by
  calc
    sourceRest 156648 = (sourceRest 156648).take 1 ++ (sourceRest 156648).drop 1 :=
      (List.take_append_drop 1 (sourceRest 156648)).symm
    _ = arrayOpenChars ++ (sourceRest 156648).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 156648).drop 1) array_open_prefix
    _ = arrayOpenChars ++ sourceRest 156649 :=
      congrArg (fun tail => arrayOpenChars ++ tail) (sourceRest_drop 156648 1)

theorem value_array_open (fuel : Nat) :
    SourceJson.value (fuel + 100) (sourceRest 156648) =
      SourceJson.array (fuel + 99) (SourceJson.white (sourceRest 156649)) [] :=
  (congrArg (SourceJson.value (fuel + 100)) array_open_split).trans (by rfl)

theorem array_all_blocks (fuel : Nat) :
    SourceJson.array (fuel + 99) (SourceJson.white (sourceRest 156649)) [] =
      .ok (arrayValue, sourceRest 225544) := by
  calc
    SourceJson.array (fuel + 99) (SourceJson.white (sourceRest 156649)) [] = SourceJson.array (fuel + 97) (SourceJson.white (sourceRest 157275)) arrayAcc001 := FaceLedgerBlock000.array_block_original fuel arrayAcc000
    _ = SourceJson.array (fuel + 96) (SourceJson.white (sourceRest 162913)) arrayAcc002 := FaceLedgerBlock001.array_block_original fuel arrayAcc001
    _ = SourceJson.array (fuel + 95) (SourceJson.white (sourceRest 167230)) arrayAcc003 := FaceLedgerBlock002.array_block_original fuel arrayAcc002
    _ = SourceJson.array (fuel + 93) (SourceJson.white (sourceRest 171234)) arrayAcc004 := FaceLedgerBlock003.array_block_original fuel arrayAcc003
    _ = SourceJson.array (fuel + 90) (SourceJson.white (sourceRest 174209)) arrayAcc005 := FaceLedgerBlock004.array_block_original fuel arrayAcc004
    _ = SourceJson.array (fuel + 89) (SourceJson.white (sourceRest 176554)) arrayAcc006 := FaceLedgerBlock005.array_block_original fuel arrayAcc005
    _ = SourceJson.array (fuel + 87) (SourceJson.white (sourceRest 180508)) arrayAcc007 := FaceLedgerBlock006.array_block_original fuel arrayAcc006
    _ = SourceJson.array (fuel + 84) (SourceJson.white (sourceRest 183911)) arrayAcc008 := FaceLedgerBlock007.array_block_original fuel arrayAcc007
    _ = SourceJson.array (fuel + 78) (SourceJson.white (sourceRest 187823)) arrayAcc009 := FaceLedgerBlock008.array_block_original fuel arrayAcc008
    _ = SourceJson.array (fuel + 72) (SourceJson.white (sourceRest 191563)) arrayAcc010 := FaceLedgerBlock009.array_block_original fuel arrayAcc009
    _ = SourceJson.array (fuel + 62) (SourceJson.white (sourceRest 195205)) arrayAcc011 := FaceLedgerBlock010.array_block_original fuel arrayAcc010
    _ = SourceJson.array (fuel + 61) (SourceJson.white (sourceRest 197896)) arrayAcc012 := FaceLedgerBlock011.array_block_original fuel arrayAcc011
    _ = SourceJson.array (fuel + 58) (SourceJson.white (sourceRest 201950)) arrayAcc013 := FaceLedgerBlock012.array_block_original fuel arrayAcc012
    _ = SourceJson.array (fuel + 52) (SourceJson.white (sourceRest 205464)) arrayAcc014 := FaceLedgerBlock013.array_block_original fuel arrayAcc013
    _ = SourceJson.array (fuel + 47) (SourceJson.white (sourceRest 209064)) arrayAcc015 := FaceLedgerBlock014.array_block_original fuel arrayAcc014
    _ = SourceJson.array (fuel + 40) (SourceJson.white (sourceRest 211822)) arrayAcc016 := FaceLedgerBlock015.array_block_original fuel arrayAcc015
    _ = SourceJson.array (fuel + 38) (SourceJson.white (sourceRest 215368)) arrayAcc017 := FaceLedgerBlock016.array_block_original fuel arrayAcc016
    _ = SourceJson.array (fuel + 32) (SourceJson.white (sourceRest 219438)) arrayAcc018 := FaceLedgerBlock017.array_block_original fuel arrayAcc017
    _ = SourceJson.array (fuel + 23) (SourceJson.white (sourceRest 222919)) arrayAcc019 := FaceLedgerBlock018.array_block_original fuel arrayAcc018
    _ = .ok (arrayValue, sourceRest 225544) := FaceLedgerBlock019.array_block_original fuel arrayAcc019

theorem value_array_original (fuel : Nat) :
    SourceJson.value (fuel + 100) (sourceRest 156648) =
      .ok (arrayValue, sourceRest 225544) :=
  (value_array_open fuel).trans (array_all_blocks fuel)

#print axioms array_open_prefix
#print axioms array_open_split
#print axioms value_array_open
#print axioms array_all_blocks
#print axioms value_array_original

end FaceLedgerValue

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
