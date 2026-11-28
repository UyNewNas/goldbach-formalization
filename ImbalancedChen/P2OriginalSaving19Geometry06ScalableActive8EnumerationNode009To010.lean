import ImbalancedChen.P2OriginalSaving19Geometry06ScalableActive8EnumerationBlock009
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableActive8EnumerationBlock010

/-! Balanced original active8_enumeration composition, leaf interval 9 through 10. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationNode009To010
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock010.blockPush (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock009.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 49) (SourceJson.white (sourceRest 35769)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 41101) :=
  (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock009.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock010.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock009.blockPush acc))

#print axioms array_original
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationNode009To010
