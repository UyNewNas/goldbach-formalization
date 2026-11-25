import ImbalancedChen.P2OriginalSaving19SimplicesField00

/-! Exact penultimate field physical_volume, including its original decimal-rational string and comma.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def physicalVolumePrefixChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '3', '8', '7', '9', '6', '3', '3', '4', '1', '7', '1', '6', '1', '3', '9', '9', '7', '1', '1', '8', '9', '3', '7', '6', '8', '4', '3', '8', '4', '2', '3', '6', '5', '2', '3', '5', '0', '8', '4', '7', '2', '4', '5', '1', '2', '3', '2', '7', '1', '2', '2', '4', '7', '4', '3', '8', '4', '7', '/', '2', '7', '8', '0', '1', '8', '5', '3', '6', '1', '4', '0', '0', '7', '4', '9', '3', '0', '4', '1', '1', '6', '6', '7', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def physicalVolumeKey00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def physicalVolumeValue00 : SourceJson := .str (String.ofList ['1', '3', '8', '7', '9', '6', '3', '3', '4', '1', '7', '1', '6', '1', '3', '9', '9', '7', '1', '1', '8', '9', '3', '7', '6', '8', '4', '3', '8', '4', '2', '3', '6', '5', '2', '3', '5', '0', '8', '4', '7', '2', '4', '5', '1', '2', '3', '2', '7', '1', '2', '2', '4', '7', '4', '3', '8', '4', '7', '/', '2', '7', '8', '0', '1', '8', '5', '3', '6', '1', '4', '0', '0', '7', '4', '9', '3', '0', '4', '1', '1', '6', '6', '7', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def physicalVolumeAcc00 : List (String × SourceJson) :=
  (physicalVolumeKey00, physicalVolumeValue00) :: simplicesFieldAcc00

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 physical_volume_before_binding"
  err.flush

theorem geometryChars00_physical_volume_prefix :
    (geometryChars00.drop 194777).take 165 = physicalVolumePrefixChars00 := by rfl

theorem geometryChars00_physical_volume_split :
    geometryChars00.drop 194777 = physicalVolumePrefixChars00 ++ geometryChars00.drop 194942 := by
  calc
    geometryChars00.drop 194777 =
        (geometryChars00.drop 194777).take 165 ++ (geometryChars00.drop 194777).drop 165 :=
      (List.take_append_drop 165 (geometryChars00.drop 194777)).symm
    _ = physicalVolumePrefixChars00 ++ (geometryChars00.drop 194777).drop 165 :=
      congrArg (fun p => p ++ (geometryChars00.drop 194777).drop 165) geometryChars00_physical_volume_prefix
    _ = physicalVolumePrefixChars00 ++ geometryChars00.drop 194942 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 physical_volume_after_binding"
  err.flush

theorem object_physical_volume_prefix (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 142) (SourceJson.white (physicalVolumePrefixChars00 ++ tail)) simplicesFieldAcc00 =
      SourceJson.object (fuel + 141) (SourceJson.white tail) physicalVolumeAcc00 := by rfl

theorem geometryChars00_physical_volume_step :
    SourceJson.object 195122 (SourceJson.white (geometryChars00.drop 194777)) simplicesFieldAcc00 =
      SourceJson.object 195121 (SourceJson.white (geometryChars00.drop 194942)) physicalVolumeAcc00 := by
  exact (congrArg (fun s => SourceJson.object 195122 (SourceJson.white s) simplicesFieldAcc00)
      geometryChars00_physical_volume_split).trans
    (object_physical_volume_prefix 194980 (geometryChars00.drop 194942))

theorem geometryChars00_through_physical_volume :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195121 (SourceJson.white (geometryChars00.drop 194942)) physicalVolumeAcc00 := by
  exact geometryChars00_through_simplices.trans geometryChars00_physical_volume_step

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 physical_volume_complete"
  err.flush

#print axioms geometryChars00_physical_volume_prefix
#print axioms geometryChars00_physical_volume_split
#print axioms object_physical_volume_prefix
#print axioms geometryChars00_physical_volume_step
#print axioms geometryChars00_through_physical_volume

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
