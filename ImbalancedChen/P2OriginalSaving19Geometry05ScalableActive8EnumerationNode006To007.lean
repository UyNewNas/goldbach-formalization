import ImbalancedChen.P2OriginalSaving19Geometry05ScalableActive8EnumerationBlock006
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableActive8EnumerationBlock007

/-! Balanced original active8_enumeration composition, leaf interval 6 through 7. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationNode006To007
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationBlock007.blockPush (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationBlock006.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 97) (SourceJson.white (sourceRest 23991)) acc =
      SourceJson.array (fuel + 65) (SourceJson.white (sourceRest 31892)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationBlock006.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationBlock007.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationBlock006.blockPush acc))

#print axioms array_original
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationNode006To007
