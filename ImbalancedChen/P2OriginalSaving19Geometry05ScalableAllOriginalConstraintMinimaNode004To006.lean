import ImbalancedChen.P2OriginalSaving19Geometry05ScalableAllOriginalConstraintMinimaNode004To005
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableAllOriginalConstraintMinimaBlock006

/-! Balanced original all_original_constraint_minima composition, leaf interval 4 through 6. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode004To006
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaBlock006.blockPush (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode004To005.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 52) (SourceJson.white (sourceRest 62270)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 63026) :=
  (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode004To005.array_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaBlock006.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode004To005.blockPush acc))

#print axioms array_original
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.AllOriginalConstraintMinimaNode004To006
