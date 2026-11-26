import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVerticesHeader
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVerticesValue

/-! Insert the completed original array into its original parent object.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace VerticesField

noncomputable def separatorChars : List Char := [',']
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, VerticesValue.arrayValue) :: Active8EnumerationField.fieldAcc

theorem after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (VerticesValue.arrayValue, separatorChars ++ tail)).bind (afterValue (fuel + 57)) =
      SourceJson.object (fuel + 57) (SourceJson.white tail) fieldAcc := by rfl

theorem separator_original_prefix :
    (sourceRest 47411).take 1 = separatorChars := by rfl

theorem separator_original_split : sourceRest 47411 = separatorChars ++ sourceRest 47412 := by
  calc
    sourceRest 47411 = (sourceRest 47411).take 1 ++ (sourceRest 47411).drop 1 :=
      (List.take_append_drop 1 (sourceRest 47411)).symm
    _ = separatorChars ++ (sourceRest 47411).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 47411).drop 1) separator_original_prefix
    _ = separatorChars ++ sourceRest 47412 :=
      congrArg (fun tail => separatorChars ++ tail) (sourceRest_drop 47411 1)

theorem object_original_field (fuel : Nat) :
    SourceJson.object (fuel + 58) (SourceJson.white (sourceRest 41066)) Active8EnumerationField.fieldAcc =
      SourceJson.object (fuel + 57) (SourceJson.white (sourceRest 47412)) fieldAcc := by
  calc
    SourceJson.object (fuel + 58) (SourceJson.white (sourceRest 41066)) Active8EnumerationField.fieldAcc =
        (SourceJson.value (fuel + 57) (sourceRest 41082)).bind (afterValue (fuel + 57)) :=
      object_original_header fuel
    _ = (Except.ok (VerticesValue.arrayValue, sourceRest 47411)).bind (afterValue (fuel + 57)) :=
      congrArg (fun result => result.bind (afterValue (fuel + 57)))
        (VerticesValue.value_array_original (fuel + 0))
    _ = (Except.ok (VerticesValue.arrayValue, separatorChars ++ sourceRest 47412)).bind
          (afterValue (fuel + 57)) :=
      congrArg (fun rest => (Except.ok (VerticesValue.arrayValue, rest)).bind (afterValue (fuel + 57)))
        separator_original_split
    _ = SourceJson.object (fuel + 57) (SourceJson.white (sourceRest 47412)) fieldAcc :=
      after_value_separator fuel (sourceRest 47412)

theorem sourceChars_through_field :
    SourceJson.value 201043 sourceChars =
      SourceJson.object 201035 (SourceJson.white (sourceRest 47412)) fieldAcc :=
  Active8EnumerationField.sourceChars_through_field.trans (object_original_field 200978)

#print axioms after_value_separator
#print axioms separator_original_prefix
#print axioms separator_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end VerticesField

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
