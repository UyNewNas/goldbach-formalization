import ImbalancedChen.P2OriginalSaving19Geometry06ScalableActive8EnumerationBlock003
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableActive8EnumerationBlock004

/-! Balanced original active8_enumeration composition, leaf interval 3 through 4. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationNode003To004
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock004.blockPush (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock003.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 145) (SourceJson.white (sourceRest 12358)) acc =
      SourceJson.array (fuel + 113) (SourceJson.white (sourceRest 19989)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock003.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock004.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationBlock003.blockPush acc))

#print axioms array_original
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationNode003To004
