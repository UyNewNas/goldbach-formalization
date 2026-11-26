import ImbalancedChen.P2OriginalSaving19Geometry05ScalableAllOriginalConstraintMinimaBlock004
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableAllOriginalConstraintMinimaBlock005

/-! Balanced original all_original_constraint_minima composition, leaf interval 4 through 5. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode004To005
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaBlock005.blockPush (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaBlock004.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 52) (SourceJson.white (sourceRest 62270)) acc =
      SourceJson.array (fuel + 20) (SourceJson.white (sourceRest 62996)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaBlock004.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaBlock005.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaBlock004.blockPush acc))

#print axioms array_original
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode004To005
