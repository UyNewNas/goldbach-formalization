import ImbalancedChen.P2OriginalSaving19Geometry05ScalableAllOriginalConstraintMinimaNode000To001
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableAllOriginalConstraintMinimaNode002To003

/-! Balanced original all_original_constraint_minima composition, leaf interval 0 through 3. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode000To003
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode002To003.blockPush (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode000To001.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 116) (SourceJson.white (sourceRest 60902)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white (sourceRest 62270)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode000To001.array_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode002To003.array_original fuel (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode000To001.blockPush acc))

#print axioms array_original
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode000To003
