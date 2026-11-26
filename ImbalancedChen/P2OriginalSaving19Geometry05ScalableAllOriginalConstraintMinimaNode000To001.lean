import ImbalancedChen.P2OriginalSaving19Geometry05ScalableAllOriginalConstraintMinimaBlock000
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableAllOriginalConstraintMinimaBlock001

/-! Balanced original all_original_constraint_minima composition, leaf interval 0 through 1. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode000To001
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaBlock001.blockPush (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaBlock000.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 116) (SourceJson.white (sourceRest 60902)) acc =
      SourceJson.array (fuel + 84) (SourceJson.white (sourceRest 61585)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaBlock000.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaBlock001.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaBlock000.blockPush acc))

#print axioms array_original
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode000To001
