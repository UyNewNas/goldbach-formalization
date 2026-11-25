import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup000
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup001
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup002
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup003
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup004
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup005
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup006
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup007
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup008
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup009
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup010
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup011
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup012
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup013
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup014
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup015
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup016
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup017
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup018
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup019
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup020
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup021
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup022
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup023
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup024
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup025
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup026
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup027
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup028
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup029
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup030
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup031
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup032
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup033
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup034
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup035
import ImbalancedChen.P2OriginalSaving19GeometryPackedSpanGroup036
import ImbalancedChen.P2OriginalSaving19WholeParse00

/-! Closed equality of full input representations and transport of accepted original parser theorems.
The original parser certificates remain frozen; this owner only relates input
representations through exact complete character spans. -/
namespace ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometryChars00_eq_geometryPacked00 :
    geometryChars00 = geometryPacked00.toList := by
  have hend : geometryChars00.drop 195134 = compactRest00 195134 :=
    geometryChars00_end_drop.trans compactRest00_end.symm
  have hgroup036 := group036_rest_eq hend
  have hgroup035 := group035_rest_eq hgroup036
  have hgroup034 := group034_rest_eq hgroup035
  have hgroup033 := group033_rest_eq hgroup034
  have hgroup032 := group032_rest_eq hgroup033
  have hgroup031 := group031_rest_eq hgroup032
  have hgroup030 := group030_rest_eq hgroup031
  have hgroup029 := group029_rest_eq hgroup030
  have hgroup028 := group028_rest_eq hgroup029
  have hgroup027 := group027_rest_eq hgroup028
  have hgroup026 := group026_rest_eq hgroup027
  have hgroup025 := group025_rest_eq hgroup026
  have hgroup024 := group024_rest_eq hgroup025
  have hgroup023 := group023_rest_eq hgroup024
  have hgroup022 := group022_rest_eq hgroup023
  have hgroup021 := group021_rest_eq hgroup022
  have hgroup020 := group020_rest_eq hgroup021
  have hgroup019 := group019_rest_eq hgroup020
  have hgroup018 := group018_rest_eq hgroup019
  have hgroup017 := group017_rest_eq hgroup018
  have hgroup016 := group016_rest_eq hgroup017
  have hgroup015 := group015_rest_eq hgroup016
  have hgroup014 := group014_rest_eq hgroup015
  have hgroup013 := group013_rest_eq hgroup014
  have hgroup012 := group012_rest_eq hgroup013
  have hgroup011 := group011_rest_eq hgroup012
  have hgroup010 := group010_rest_eq hgroup011
  have hgroup009 := group009_rest_eq hgroup010
  have hgroup008 := group008_rest_eq hgroup009
  have hgroup007 := group007_rest_eq hgroup008
  have hgroup006 := group006_rest_eq hgroup007
  have hgroup005 := group005_rest_eq hgroup006
  have hgroup004 := group004_rest_eq hgroup005
  have hgroup003 := group003_rest_eq hgroup004
  have hgroup002 := group002_rest_eq hgroup003
  have hgroup001 := group001_rest_eq hgroup002
  have hgroup000 := group000_rest_eq hgroup001
  exact (by rfl : geometryChars00 = geometryChars00.drop 0).trans
    (hgroup000.trans compactRest00_zero)

theorem geometryPacked00_whole_value :
    SourceJson.value 195135 geometryPacked00.toList =
      .ok (originalGeometryJson00, geometryPacked00.toList.drop 195132) := by
  calc
    SourceJson.value 195135 geometryPacked00.toList = SourceJson.value 195135 geometryChars00 :=
      congrArg (SourceJson.value 195135) geometryChars00_eq_geometryPacked00.symm
    _ = .ok (originalGeometryJson00, geometryChars00.drop 195132) := geometryChars00_whole_value
    _ = .ok (originalGeometryJson00, geometryPacked00.toList.drop 195132) :=
      congrArg (fun chars => Except.ok (originalGeometryJson00, chars.drop 195132))
        geometryChars00_eq_geometryPacked00

theorem geometryPacked00_parseChars :
    SourceJson.parseChars geometryPacked00.toList = .ok originalGeometryJson00 :=
  (congrArg SourceJson.parseChars geometryChars00_eq_geometryPacked00.symm).trans
    geometryChars00_parseChars

theorem geometryPacked00_original_parse :
    SourceJson.parse (String.ofList geometryPacked00.toList) = .ok originalGeometryJson00 :=
  (SourceJson.parse_ofList geometryPacked00.toList).trans geometryPacked00_parseChars

#print axioms geometryChars00_eq_geometryPacked00
#print axioms geometryPacked00_whole_value
#print axioms geometryPacked00_parseChars
#print axioms geometryPacked00_original_parse

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
