import ImbalancedChen.P2OriginalSaving19PhysicalVolumePrefix00

/-! Exact final integral_gap field and the closing original root object. The full original value reader returns the certified AST and the untouched original CRLF tail.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def integralGapPrefixChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 'i', 'n', 't', 'e', 'g', 'r', 'a', 'l', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '0', '8', '9', '5', '6', '4', '3', '5', '8', '7', '2', '6', '9', '7', '8', '0', '5', '3', '6', '1', '2', '8', '9', '9', '6', '7', '3', '0', '5', '5', '9', '2', '3', '3', '2', '7', '1', '3', '3', '7', '7', '4', '6', '8', '6', '3', '4', '8', '6', '1', '4', '6', '6', '4', '0', '2', '7', '8', '3', '6', '6', '9', '2', '2', '5', '6', '5', '4', '3', '/', '1', '2', '3', '6', '8', '6', '1', '4', '9', '6', '7', '4', '2', '2', '4', '7', '5', '5', '5', '4', '2', '0', '2', '6', '4', '0', '8', '4', '4', '2', '2', '0', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', '}']
noncomputable def integralGapKey00 : String := String.ofList ['i', 'n', 't', 'e', 'g', 'r', 'a', 'l', '_', 'g', 'a', 'p']
noncomputable def integralGapValue00 : SourceJson := .str (String.ofList ['3', '0', '8', '9', '5', '6', '4', '3', '5', '8', '7', '2', '6', '9', '7', '8', '0', '5', '3', '6', '1', '2', '8', '9', '9', '6', '7', '3', '0', '5', '5', '9', '2', '3', '3', '2', '7', '1', '3', '3', '7', '7', '4', '6', '8', '6', '3', '4', '8', '6', '1', '4', '6', '6', '4', '0', '2', '7', '8', '3', '6', '6', '9', '2', '2', '5', '6', '5', '4', '3', '/', '1', '2', '3', '6', '8', '6', '1', '4', '9', '6', '7', '4', '2', '2', '4', '7', '5', '5', '5', '4', '2', '0', '2', '6', '4', '0', '8', '4', '4', '2', '2', '0', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def originalGeometryJson00 : SourceJson :=
  .obj (((integralGapKey00, integralGapValue00) :: physicalVolumeAcc00).reverse)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 integral_gap_before_binding"
  err.flush

theorem geometryChars00_integral_gap_prefix :
    (geometryChars00.drop 194942).take 190 = integralGapPrefixChars00 := by rfl

theorem geometryChars00_integral_gap_split :
    geometryChars00.drop 194942 = integralGapPrefixChars00 ++ geometryChars00.drop 195132 := by
  calc
    geometryChars00.drop 194942 =
        (geometryChars00.drop 194942).take 190 ++ (geometryChars00.drop 194942).drop 190 :=
      (List.take_append_drop 190 (geometryChars00.drop 194942)).symm
    _ = integralGapPrefixChars00 ++ (geometryChars00.drop 194942).drop 190 :=
      congrArg (fun p => p ++ (geometryChars00.drop 194942).drop 190) geometryChars00_integral_gap_prefix
    _ = integralGapPrefixChars00 ++ geometryChars00.drop 195132 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 integral_gap_after_binding"
  err.flush

theorem object_integral_gap_prefix (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 168) (SourceJson.white (integralGapPrefixChars00 ++ tail)) physicalVolumeAcc00 =
      .ok (originalGeometryJson00, tail) := by rfl

theorem geometryChars00_integral_gap_step :
    SourceJson.object 195121 (SourceJson.white (geometryChars00.drop 194942)) physicalVolumeAcc00 =
      .ok (originalGeometryJson00, geometryChars00.drop 195132) := by
  exact (congrArg (fun s => SourceJson.object 195121 (SourceJson.white s) physicalVolumeAcc00)
      geometryChars00_integral_gap_split).trans
    (object_integral_gap_prefix 194953 (geometryChars00.drop 195132))

theorem geometryChars00_whole_value :
    SourceJson.value 195135 geometryChars00 =
      .ok (originalGeometryJson00, geometryChars00.drop 195132) := by
  exact geometryChars00_through_physical_volume.trans geometryChars00_integral_gap_step

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 whole_value_complete"
  err.flush

#print axioms geometryChars00_integral_gap_prefix
#print axioms geometryChars00_integral_gap_split
#print axioms object_integral_gap_prefix
#print axioms geometryChars00_integral_gap_step
#print axioms geometryChars00_whole_value

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
