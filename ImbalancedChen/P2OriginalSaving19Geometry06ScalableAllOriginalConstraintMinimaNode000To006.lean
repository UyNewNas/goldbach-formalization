import ImbalancedChen.P2OriginalSaving19Geometry06ScalableAllOriginalConstraintMinimaNode000To003
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableAllOriginalConstraintMinimaNode004To006

/-! Balanced original all_original_constraint_minima composition, leaf interval 0 through 6. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaNode000To006
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaNode004To006.blockPush (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaNode000To003.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 116) (SourceJson.white (sourceRest 63978)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 66061) :=
  (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaNode000To003.array_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaNode004To006.array_original fuel (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaNode000To003.blockPush acc))

#print axioms array_original
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaNode000To006
