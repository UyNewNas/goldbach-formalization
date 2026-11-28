import ImbalancedChen.P2OriginalSaving19Geometry06ScalableActive8EnumerationBlock000
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableActive8EnumerationBlock001

/-! Balanced original active8_enumeration composition, leaf interval 0 through 1. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationNode000To001
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock001.blockPush (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock000.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 193) (SourceJson.white (sourceRest 402)) acc =
      SourceJson.array (fuel + 161) (SourceJson.white (sourceRest 8445)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock000.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock001.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock000.blockPush acc))

#print axioms array_original
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationNode000To001
