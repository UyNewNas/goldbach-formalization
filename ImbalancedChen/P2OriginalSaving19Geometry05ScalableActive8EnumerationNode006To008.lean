import ImbalancedChen.P2OriginalSaving19Geometry05ScalableActive8EnumerationNode006To007
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableActive8EnumerationBlock008

/-! Balanced original active8_enumeration composition, leaf interval 6 through 8. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationNode006To008
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationBlock008.blockPush (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationNode006To007.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 97) (SourceJson.white (sourceRest 23991)) acc =
      SourceJson.array (fuel + 49) (SourceJson.white (sourceRest 35950)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationNode006To007.array_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationBlock008.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationNode006To007.blockPush acc))

#print axioms array_original
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationNode006To008
