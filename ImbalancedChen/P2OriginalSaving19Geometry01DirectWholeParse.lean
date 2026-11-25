import ImbalancedChen.P2OriginalSaving19Geometry01DirectWholeValue
import ImbalancedChen.P2OriginalSaving19ParseFromValue00

/-! Original parser success for complete production-packed cell01, including its exact remaining CRLF.
Original-reader equations and exact production packed-input slices are checked
in Lean. This owner proves original parser success for cell01 only. Typed decoding is separate. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

noncomputable def finalTailChars : List Char := ['\r', '\n']

theorem final_tail_prefix :
    (sourceRest 470899).take 2 = finalTailChars := by rfl

theorem final_tail_split : sourceRest 470899 = finalTailChars ++ sourceRest 470901 := by
  calc
    sourceRest 470899 = (sourceRest 470899).take 2 ++ (sourceRest 470899).drop 2 :=
      (List.take_append_drop 2 (sourceRest 470899)).symm
    _ = finalTailChars ++ (sourceRest 470899).drop 2 :=
      congrArg (fun part => part ++ (sourceRest 470899).drop 2) final_tail_prefix
    _ = finalTailChars ++ sourceRest 470901 :=
      congrArg (fun tail => finalTailChars ++ tail) (sourceRest_drop 470899 2)

theorem sourceRest_exact_tail : sourceRest 470899 = finalTailChars :=
  final_tail_split.trans (by rw [sourceRest_end, List.append_nil])

theorem sourceRest_white_tail : SourceJson.white (sourceRest 470899) = [] :=
  (congrArg SourceJson.white sourceRest_exact_tail).trans (by rfl)

theorem sourceChars_parseChars : SourceJson.parseChars sourceChars = .ok originalGeometryJson01 := by
  apply SourceJson.parseChars_of_value_eq
  · simpa only [sourceChars_length] using sourceChars_whole_value
  · exact sourceRest_white_tail

theorem geometryPacked01_parseChars :
    SourceJson.parseChars geometryPacked01.toList = .ok originalGeometryJson01 :=
  sourceChars_parseChars

theorem geometryPacked01_original_parse :
    SourceJson.parse (String.ofList geometryPacked01.toList) = .ok originalGeometryJson01 :=
  (SourceJson.parse_ofList sourceChars).trans sourceChars_parseChars

#print axioms final_tail_prefix
#print axioms final_tail_split
#print axioms sourceRest_exact_tail
#print axioms sourceRest_white_tail
#print axioms sourceChars_parseChars
#print axioms geometryPacked01_parseChars
#print axioms geometryPacked01_original_parse

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
