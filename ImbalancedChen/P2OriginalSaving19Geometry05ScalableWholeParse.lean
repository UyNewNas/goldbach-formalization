import ImbalancedChen.P2OriginalSaving19Geometry05ScalableWholeValue
import ImbalancedChen.P2OriginalSaving19ParseFromValue00

/-! Original parser success for the complete production-packed cell05, including final CRLF.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

noncomputable def finalTailChars : List Char := ['\r', '\n']

theorem final_tail_prefix :
    (sourceRest 201040).take 2 = finalTailChars := by rfl

theorem final_tail_split : sourceRest 201040 = finalTailChars ++ sourceRest 201042 := by
  calc
    sourceRest 201040 = (sourceRest 201040).take 2 ++ (sourceRest 201040).drop 2 :=
      (List.take_append_drop 2 (sourceRest 201040)).symm
    _ = finalTailChars ++ (sourceRest 201040).drop 2 :=
      congrArg (fun part => part ++ (sourceRest 201040).drop 2) final_tail_prefix
    _ = finalTailChars ++ sourceRest 201042 :=
      congrArg (fun tail => finalTailChars ++ tail) (sourceRest_drop 201040 2)

theorem sourceRest_exact_tail : sourceRest 201040 = finalTailChars :=
  final_tail_split.trans (by rw [sourceRest_end, List.append_nil])

theorem sourceRest_white_tail : SourceJson.white (sourceRest 201040) = [] :=
  (congrArg SourceJson.white sourceRest_exact_tail).trans (by rfl)

theorem sourceChars_parseChars : SourceJson.parseChars sourceChars = .ok originalGeometryJson05 := by
  apply SourceJson.parseChars_of_value_eq
  · simpa only [sourceChars_length] using sourceChars_whole_value
  · exact sourceRest_white_tail

theorem geometryPacked05_parseChars :
    SourceJson.parseChars geometryPacked05.toList = .ok originalGeometryJson05 :=
  sourceChars_parseChars

theorem geometryPacked05_original_parse :
    SourceJson.parse (String.ofList geometryPacked05.toList) = .ok originalGeometryJson05 :=
  (SourceJson.parse_ofList sourceChars).trans sourceChars_parseChars

#print axioms final_tail_prefix
#print axioms final_tail_split
#print axioms sourceRest_exact_tail
#print axioms sourceRest_white_tail
#print axioms sourceChars_parseChars
#print axioms geometryPacked05_parseChars
#print axioms geometryPacked05_original_parse

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
