import ImbalancedChen.P2OriginalSaving19Geometry01DirectPhysicalVolumeField

/-! Last original field, closing object and complete original value success.
Original-reader equations and exact production packed-input slices are checked
in Lean. This owner proves the complete original value equation; typed decoding is separate. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

noncomputable def finalFieldChars : List Char := ['\r', '\n', ' ', ' ', '"', 'i', 'n', 't', 'e', 'g', 'r', 'a', 'l', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '2', '1', '2', '7', '1', '5', '7', '0', '2', '9', '7', '2', '9', '5', '3', '9', '7', '6', '1', '7', '4', '9', '0', '3', '3', '7', '4', '2', '3', '4', '1', '8', '3', '9', '6', '6', '3', '2', '6', '8', '7', '8', '7', '9', '8', '4', '3', '0', '7', '6', '0', '0', '1', '0', '8', '2', '0', '2', '4', '2', '9', '5', '8', '1', '6', '1', '8', '1', '8', '5', '3', '8', '6', '4', '0', '4', '0', '6', '7', '3', '/', '1', '2', '0', '3', '7', '2', '2', '2', '4', '2', '7', '9', '4', '4', '9', '9', '9', '3', '7', '2', '4', '4', '6', '0', '4', '1', '2', '9', '0', '2', '0', '4', '4', '6', '8', '2', '1', '7', '7', '9', '4', '4', '2', '2', '3', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', '}']
noncomputable def finalFieldKey : String := String.ofList ['i', 'n', 't', 'e', 'g', 'r', 'a', 'l', '_', 'g', 'a', 'p']
noncomputable def finalFieldValue : SourceJson := .str (String.ofList ['6', '0', '8', '2', '1', '2', '7', '1', '5', '7', '0', '2', '9', '7', '2', '9', '5', '3', '9', '7', '6', '1', '7', '4', '9', '0', '3', '3', '7', '4', '2', '3', '4', '1', '8', '3', '9', '6', '6', '3', '2', '6', '8', '7', '8', '7', '9', '8', '4', '3', '0', '7', '6', '0', '0', '1', '0', '8', '2', '0', '2', '4', '2', '9', '5', '8', '1', '6', '1', '8', '1', '8', '5', '3', '8', '6', '4', '0', '4', '0', '6', '7', '3', '/', '1', '2', '0', '3', '7', '2', '2', '2', '4', '2', '7', '9', '4', '4', '9', '9', '9', '3', '7', '2', '4', '4', '6', '0', '4', '1', '2', '9', '0', '2', '0', '4', '4', '6', '8', '2', '1', '7', '7', '9', '4', '4', '2', '2', '3', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def originalGeometryJson01 : SourceJson :=
  .obj (((finalFieldKey, finalFieldValue) :: PhysicalVolumeField.fieldAcc).reverse)

theorem object_final_field (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 192) (SourceJson.white (finalFieldChars ++ tail)) PhysicalVolumeField.fieldAcc =
      .ok (originalGeometryJson01, tail) := by rfl

theorem final_field_prefix :
    (sourceRest 470685).take 214 = finalFieldChars := by rfl

theorem final_field_split : sourceRest 470685 = finalFieldChars ++ sourceRest 470899 := by
  calc
    sourceRest 470685 = (sourceRest 470685).take 214 ++ (sourceRest 470685).drop 214 :=
      (List.take_append_drop 214 (sourceRest 470685)).symm
    _ = finalFieldChars ++ (sourceRest 470685).drop 214 :=
      congrArg (fun part => part ++ (sourceRest 470685).drop 214) final_field_prefix
    _ = finalFieldChars ++ sourceRest 470899 :=
      congrArg (fun tail => finalFieldChars ++ tail) (sourceRest_drop 470685 214)

theorem final_field_original :
    SourceJson.object 470888 (SourceJson.white (sourceRest 470685)) PhysicalVolumeField.fieldAcc =
      .ok (originalGeometryJson01, sourceRest 470899) :=
  (congrArg (fun chars => SourceJson.object 470888 (SourceJson.white chars) PhysicalVolumeField.fieldAcc)
    final_field_split).trans (object_final_field 470696 (sourceRest 470899))

theorem sourceChars_whole_value :
    SourceJson.value 470902 sourceChars =
      .ok (originalGeometryJson01, sourceRest 470899) :=
  PhysicalVolumeField.sourceChars_through_field.trans final_field_original

theorem geometryPacked01_whole_value :
    SourceJson.value 470902 geometryPacked01.toList =
      .ok (originalGeometryJson01, (geometryPacked01.drop 470899).toList) :=
  sourceChars_whole_value

#print axioms object_final_field
#print axioms final_field_prefix
#print axioms final_field_split
#print axioms final_field_original
#print axioms sourceChars_whole_value
#print axioms geometryPacked01_whole_value

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
