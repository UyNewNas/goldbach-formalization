import ImbalancedChen.P2OriginalSaving19WholeValue00
import ImbalancedChen.P2OriginalSaving19ParseFromValue00

/-! Complete unchanged SourceJson parser success for the exact accepted geometryChars00 input and its explicitly defined geometryText00. The original remaining CRLF is checked and removed by original white.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def geometryTailChars00 : List Char := ['\r', '\n']

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 whole_parse_before_tail_binding"
  err.flush

theorem geometryChars00_final_tail_prefix :
    (geometryChars00.drop 195132).take 2 = geometryTailChars00 := by rfl

theorem geometryChars00_final_tail_split :
    geometryChars00.drop 195132 = geometryTailChars00 ++ geometryChars00.drop 195134 := by
  calc
    geometryChars00.drop 195132 =
        (geometryChars00.drop 195132).take 2 ++ (geometryChars00.drop 195132).drop 2 :=
      (List.take_append_drop 2 (geometryChars00.drop 195132)).symm
    _ = geometryTailChars00 ++ (geometryChars00.drop 195132).drop 2 :=
      congrArg (fun p => p ++ (geometryChars00.drop 195132).drop 2) geometryChars00_final_tail_prefix
    _ = geometryTailChars00 ++ geometryChars00.drop 195134 := by rw [List.drop_drop]

theorem geometryChars00_end_drop : geometryChars00.drop 195134 = [] := by
  simpa only [geometryChars00_length] using List.drop_length (l := geometryChars00)

theorem geometryChars00_exact_tail : geometryChars00.drop 195132 = geometryTailChars00 := by
  exact geometryChars00_final_tail_split.trans (by rw [geometryChars00_end_drop, List.append_nil])

theorem geometryChars00_white_tail : SourceJson.white (geometryChars00.drop 195132) = [] := by
  exact (congrArg SourceJson.white geometryChars00_exact_tail).trans (by rfl)

theorem geometryChars00_parseChars :
    SourceJson.parseChars geometryChars00 = .ok originalGeometryJson00 := by
  apply SourceJson.parseChars_of_value_eq
  · simpa only [geometryChars00_length] using geometryChars00_whole_value
  · exact geometryChars00_white_tail

theorem geometryText00_parse :
    SourceJson.parse geometryText00 = .ok originalGeometryJson00 := by
  exact (SourceJson.parse_ofList geometryChars00).trans geometryChars00_parseChars

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 whole_parse_complete"
  err.flush

#print axioms geometryChars00_final_tail_prefix
#print axioms geometryChars00_final_tail_split
#print axioms geometryChars00_end_drop
#print axioms geometryChars00_exact_tail
#print axioms geometryChars00_white_tail
#print axioms geometryChars00_parseChars
#print axioms geometryText00_parse

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
