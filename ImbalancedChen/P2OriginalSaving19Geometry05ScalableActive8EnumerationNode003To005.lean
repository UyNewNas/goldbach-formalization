import ImbalancedChen.P2OriginalSaving19Geometry05ScalableActive8EnumerationNode003To004
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableActive8EnumerationBlock005

/-! Balanced original active8_enumeration composition, leaf interval 3 through 5. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationNode003To005
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationBlock005.blockPush (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationNode003To004.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 145) (SourceJson.white (sourceRest 12276)) acc =
      SourceJson.array (fuel + 97) (SourceJson.white (sourceRest 23991)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationNode003To004.array_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationBlock005.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationNode003To004.blockPush acc))

#print axioms array_original
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.Active8EnumerationNode003To005
