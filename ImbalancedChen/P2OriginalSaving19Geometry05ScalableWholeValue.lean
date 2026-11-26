import ImbalancedChen.P2OriginalSaving19Geometry05ScalablePhysicalVolumeField

/-! Original integral_gap, closing object and complete original value equation.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

noncomputable def finalFieldChars : List Char := ['\r', '\n', ' ', ' ', '"', 'i', 'n', 't', 'e', 'g', 'r', 'a', 'l', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '5', '2', '6', '0', '0', '6', '1', '7', '3', '6', '3', '8', '6', '4', '2', '1', '6', '2', '0', '4', '6', '5', '0', '8', '9', '7', '6', '4', '0', '4', '8', '6', '5', '3', '8', '6', '7', '6', '8', '2', '2', '5', '3', '7', '3', '9', '8', '1', '6', '4', '9', '3', '5', '7', '7', '9', '4', '1', '3', '5', '1', '8', '8', '1', '/', '5', '4', '9', '3', '1', '0', '8', '6', '7', '6', '7', '2', '0', '9', '9', '5', '6', '9', '5', '0', '5', '2', '2', '2', '1', '0', '5', '4', '9', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', '}']
noncomputable def finalFieldKey : String := String.ofList ['i', 'n', 't', 'e', 'g', 'r', 'a', 'l', '_', 'g', 'a', 'p']
noncomputable def finalFieldValue : SourceJson := .str (String.ofList ['3', '5', '2', '6', '0', '0', '6', '1', '7', '3', '6', '3', '8', '6', '4', '2', '1', '6', '2', '0', '4', '6', '5', '0', '8', '9', '7', '6', '4', '0', '4', '8', '6', '5', '3', '8', '6', '7', '6', '8', '2', '2', '5', '3', '7', '3', '9', '8', '1', '6', '4', '9', '3', '5', '7', '7', '9', '4', '1', '3', '5', '1', '8', '8', '1', '/', '5', '4', '9', '3', '1', '0', '8', '6', '7', '6', '7', '2', '0', '9', '9', '5', '6', '9', '5', '0', '5', '2', '2', '2', '1', '0', '5', '4', '9', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def originalGeometryJson05 : SourceJson :=
  .obj (((finalFieldKey, finalFieldValue) :: PhysicalVolumeField.fieldAcc).reverse)

theorem object_final_field (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 158) (SourceJson.white (finalFieldChars ++ tail)) PhysicalVolumeField.fieldAcc =
      .ok (originalGeometryJson05, tail) := by rfl

theorem final_field_prefix :
    (sourceRest 200860).take 180 = finalFieldChars := by rfl

theorem final_field_split : sourceRest 200860 = finalFieldChars ++ sourceRest 201040 := by
  calc
    sourceRest 200860 = (sourceRest 200860).take 180 ++ (sourceRest 200860).drop 180 :=
      (List.take_append_drop 180 (sourceRest 200860)).symm
    _ = finalFieldChars ++ (sourceRest 200860).drop 180 :=
      congrArg (fun part => part ++ (sourceRest 200860).drop 180) final_field_prefix
    _ = finalFieldChars ++ sourceRest 201040 :=
      congrArg (fun tail => finalFieldChars ++ tail) (sourceRest_drop 200860 180)

theorem final_field_original :
    SourceJson.object 201029 (SourceJson.white (sourceRest 200860)) PhysicalVolumeField.fieldAcc =
      .ok (originalGeometryJson05, sourceRest 201040) :=
  (congrArg (fun chars => SourceJson.object 201029 (SourceJson.white chars) PhysicalVolumeField.fieldAcc)
    final_field_split).trans (object_final_field 200871 (sourceRest 201040))

theorem sourceChars_whole_value :
    SourceJson.value 201043 sourceChars =
      .ok (originalGeometryJson05, sourceRest 201040) :=
  PhysicalVolumeField.sourceChars_through_field.trans final_field_original

theorem geometryPacked05_whole_value :
    SourceJson.value 201043 geometryPacked05.toList =
      .ok (originalGeometryJson05, (geometryPacked05.drop 201040).toList) :=
  sourceChars_whole_value

#print axioms object_final_field
#print axioms final_field_prefix
#print axioms final_field_split
#print axioms final_field_original
#print axioms sourceChars_whole_value
#print axioms geometryPacked05_whole_value

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
