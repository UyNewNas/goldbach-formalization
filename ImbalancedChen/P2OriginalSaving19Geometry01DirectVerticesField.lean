import ImbalancedChen.P2OriginalSaving19Geometry01DirectVerticesHeader
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVerticesValue

/-! Insert the completed original array into its original parent object.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace VerticesField

noncomputable def separatorChars : List Char := [',']
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, VerticesValue.arrayValue) :: Active8EnumerationField.fieldAcc

theorem after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (VerticesValue.arrayValue, separatorChars ++ tail)).bind (afterValue (fuel + 67)) =
      SourceJson.object (fuel + 67) (SourceJson.white tail) fieldAcc := by rfl

theorem separator_original_prefix :
    (sourceRest 131756).take 1 = separatorChars := by rfl

theorem separator_original_split : sourceRest 131756 = separatorChars ++ sourceRest 131757 := by
  calc
    sourceRest 131756 = (sourceRest 131756).take 1 ++ (sourceRest 131756).drop 1 :=
      (List.take_append_drop 1 (sourceRest 131756)).symm
    _ = separatorChars ++ (sourceRest 131756).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 131756).drop 1) separator_original_prefix
    _ = separatorChars ++ sourceRest 131757 :=
      congrArg (fun tail => separatorChars ++ tail) (sourceRest_drop 131756 1)

theorem object_original_field (fuel : Nat) :
    SourceJson.object (fuel + 68) (SourceJson.white (sourceRest 122782)) Active8EnumerationField.fieldAcc =
      SourceJson.object (fuel + 67) (SourceJson.white (sourceRest 131757)) fieldAcc := by
  calc
    SourceJson.object (fuel + 68) (SourceJson.white (sourceRest 122782)) Active8EnumerationField.fieldAcc =
        (SourceJson.value (fuel + 67) (sourceRest 122798)).bind (afterValue (fuel + 67)) :=
      object_original_header fuel
    _ = (Except.ok (VerticesValue.arrayValue, sourceRest 131756)).bind (afterValue (fuel + 67)) :=
      congrArg (fun result => result.bind (afterValue (fuel + 67)))
        (VerticesValue.value_array_original (fuel + 0))
    _ = (Except.ok (VerticesValue.arrayValue, separatorChars ++ sourceRest 131757)).bind
          (afterValue (fuel + 67)) :=
      congrArg (fun rest => (Except.ok (VerticesValue.arrayValue, rest)).bind (afterValue (fuel + 67)))
        separator_original_split
    _ = SourceJson.object (fuel + 67) (SourceJson.white (sourceRest 131757)) fieldAcc :=
      after_value_separator fuel (sourceRest 131757)

theorem sourceChars_through_field :
    SourceJson.value 470902 sourceChars =
      SourceJson.object 470894 (SourceJson.white (sourceRest 131757)) fieldAcc :=
  Active8EnumerationField.sourceChars_through_field.trans (object_original_field 470827)

#print axioms after_value_separator
#print axioms separator_original_prefix
#print axioms separator_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end VerticesField

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
