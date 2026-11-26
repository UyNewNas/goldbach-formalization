import ImbalancedChen.P2OriginalSaving19Geometry05ScalableSimplicesField

/-! Exact original physical_volume field and original comma.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace PhysicalVolumeField

noncomputable def fieldChars : List Char := ['\r', '\n', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '8', '6', '5', '1', '9', '7', '8', '8', '2', '4', '4', '5', '6', '9', '3', '9', '1', '9', '8', '7', '9', '6', '1', '3', '2', '8', '1', '4', '3', '8', '1', '2', '8', '6', '0', '4', '4', '4', '1', '1', '4', '7', '8', '2', '4', '9', '3', '2', '4', '9', '5', '0', '5', '8', '6', '1', '/', '4', '3', '1', '5', '2', '2', '4', '8', '9', '0', '5', '8', '6', '5', '0', '3', '6', '5', '6', '8', '7', '2', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def fieldKey : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fieldValue : SourceJson := .str (String.ofList ['8', '6', '5', '1', '9', '7', '8', '8', '2', '4', '4', '5', '6', '9', '3', '9', '1', '9', '8', '7', '9', '6', '1', '3', '2', '8', '1', '4', '3', '8', '1', '2', '8', '6', '0', '4', '4', '4', '1', '1', '4', '7', '8', '2', '4', '9', '3', '2', '4', '9', '5', '0', '5', '8', '6', '1', '/', '4', '3', '1', '5', '2', '2', '4', '8', '9', '0', '5', '8', '6', '5', '0', '3', '6', '5', '6', '8', '7', '2', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, fieldValue) :: SimplicesField.fieldAcc

theorem object_scalar (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 137) (SourceJson.white (fieldChars ++ tail)) SimplicesField.fieldAcc =
      SourceJson.object (fuel + 136) (SourceJson.white tail) fieldAcc := by rfl

theorem field_original_prefix :
    (sourceRest 200700).take 160 = fieldChars := by rfl

theorem field_original_split : sourceRest 200700 = fieldChars ++ sourceRest 200860 := by
  calc
    sourceRest 200700 = (sourceRest 200700).take 160 ++ (sourceRest 200700).drop 160 :=
      (List.take_append_drop 160 (sourceRest 200700)).symm
    _ = fieldChars ++ (sourceRest 200700).drop 160 :=
      congrArg (fun part => part ++ (sourceRest 200700).drop 160) field_original_prefix
    _ = fieldChars ++ sourceRest 200860 :=
      congrArg (fun tail => fieldChars ++ tail) (sourceRest_drop 200700 160)

theorem object_original_field :
    SourceJson.object 201030 (SourceJson.white (sourceRest 200700)) SimplicesField.fieldAcc =
      SourceJson.object 201029 (SourceJson.white (sourceRest 200860)) fieldAcc :=
  (congrArg (fun chars => SourceJson.object 201030 (SourceJson.white chars) SimplicesField.fieldAcc)
    field_original_split).trans (object_scalar 200893 (sourceRest 200860))

theorem sourceChars_through_field :
    SourceJson.value 201043 sourceChars =
      SourceJson.object 201029 (SourceJson.white (sourceRest 200860)) fieldAcc :=
  SimplicesField.sourceChars_through_field.trans object_original_field

#print axioms object_scalar
#print axioms field_original_prefix
#print axioms field_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end PhysicalVolumeField

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
