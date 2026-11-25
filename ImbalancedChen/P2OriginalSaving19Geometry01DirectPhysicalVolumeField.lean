import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesField

/-! Exact original scalar field, including its original separator.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace PhysicalVolumeField

noncomputable def fieldChars : List Char := ['\r', '\n', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '4', '0', '0', '7', '7', '5', '4', '3', '8', '1', '1', '2', '5', '6', '4', '1', '4', '1', '2', '2', '1', '2', '9', '0', '1', '4', '5', '0', '3', '3', '0', '5', '2', '3', '9', '7', '5', '5', '9', '9', '8', '7', '0', '3', '9', '1', '5', '3', '2', '4', '4', '2', '2', '5', '8', '2', '0', '6', '2', '2', '7', '7', '6', '8', '5', '4', '2', '5', '1', '/', '7', '0', '4', '6', '3', '1', '0', '0', '8', '2', '9', '0', '1', '0', '9', '6', '3', '9', '7', '1', '3', '6', '3', '0', '0', '0', '6', '7', '6', '1', '2', '7', '8', '6', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def fieldKey : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fieldValue : SourceJson := .str (String.ofList ['5', '4', '0', '0', '7', '7', '5', '4', '3', '8', '1', '1', '2', '5', '6', '4', '1', '4', '1', '2', '2', '1', '2', '9', '0', '1', '4', '5', '0', '3', '3', '0', '5', '2', '3', '9', '7', '5', '5', '9', '9', '8', '7', '0', '3', '9', '1', '5', '3', '2', '4', '4', '2', '2', '5', '8', '2', '0', '6', '2', '2', '7', '7', '6', '8', '5', '4', '2', '5', '1', '/', '7', '0', '4', '6', '3', '1', '0', '0', '8', '2', '9', '0', '1', '0', '9', '6', '3', '9', '7', '1', '3', '6', '3', '0', '0', '0', '6', '7', '6', '1', '2', '7', '8', '6', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, fieldValue) :: SimplicesField.fieldAcc

theorem object_scalar (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 162) (SourceJson.white (fieldChars ++ tail)) SimplicesField.fieldAcc =
      SourceJson.object (fuel + 161) (SourceJson.white tail) fieldAcc := by rfl

theorem field_original_prefix :
    (sourceRest 470500).take 185 = fieldChars := by rfl

theorem field_original_split : sourceRest 470500 = fieldChars ++ sourceRest 470685 := by
  calc
    sourceRest 470500 = (sourceRest 470500).take 185 ++ (sourceRest 470500).drop 185 :=
      (List.take_append_drop 185 (sourceRest 470500)).symm
    _ = fieldChars ++ (sourceRest 470500).drop 185 :=
      congrArg (fun part => part ++ (sourceRest 470500).drop 185) field_original_prefix
    _ = fieldChars ++ sourceRest 470685 :=
      congrArg (fun tail => fieldChars ++ tail) (sourceRest_drop 470500 185)

theorem object_original_field :
    SourceJson.object 470889 (SourceJson.white (sourceRest 470500)) SimplicesField.fieldAcc =
      SourceJson.object 470888 (SourceJson.white (sourceRest 470685)) fieldAcc :=
  (congrArg (fun chars => SourceJson.object 470889 (SourceJson.white chars) SimplicesField.fieldAcc)
    field_original_split).trans (object_scalar 470727 (sourceRest 470685))

theorem sourceChars_through_field :
    SourceJson.value 470902 sourceChars =
      SourceJson.object 470888 (SourceJson.white (sourceRest 470685)) fieldAcc :=
  SimplicesField.sourceChars_through_field.trans object_original_field

#print axioms object_scalar
#print axioms field_original_prefix
#print axioms field_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end PhysicalVolumeField

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
