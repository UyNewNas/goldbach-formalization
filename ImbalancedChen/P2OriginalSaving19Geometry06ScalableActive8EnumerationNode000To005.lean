import ImbalancedChen.P2OriginalSaving19Geometry06ScalableActive8EnumerationNode000To002
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableActive8EnumerationNode003To005

/-! Balanced original active8_enumeration composition, leaf interval 0 through 5. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationNode000To005
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationNode003To005.blockPush (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationNode000To002.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 193) (SourceJson.white (sourceRest 402)) acc =
      SourceJson.array (fuel + 97) (SourceJson.white (sourceRest 23832)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationNode000To002.array_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationNode003To005.array_original fuel (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationNode000To002.blockPush acc))

#print axioms array_original
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.Active8EnumerationNode000To005
