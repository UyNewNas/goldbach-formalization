import ImbalancedChen.P2OriginalSaving19Geometry06ScalableAllOriginalConstraintMinimaBlock002
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableAllOriginalConstraintMinimaBlock003

/-! Balanced original all_original_constraint_minima composition, leaf interval 2 through 3. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaNode002To003
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaBlock003.blockPush (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaBlock002.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 84) (SourceJson.white (sourceRest 64626)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white (sourceRest 65293)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaBlock002.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaBlock003.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaBlock002.blockPush acc))

#print axioms array_original
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaNode002To003
