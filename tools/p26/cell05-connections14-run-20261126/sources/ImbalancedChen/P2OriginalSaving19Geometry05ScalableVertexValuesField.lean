import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVertexValuesHeader
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVertexValuesValue

/-! Insert the completed original array into its original parent object.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace VertexValuesField

noncomputable def separatorChars : List Char := [',']
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, VertexValuesValue.arrayValue) :: VerticesField.fieldAcc

theorem after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (VertexValuesValue.arrayValue, separatorChars ++ tail)).bind (afterValue (fuel + 66)) =
      SourceJson.object (fuel + 66) (SourceJson.white tail) fieldAcc := by rfl

theorem separator_original_prefix :
    (sourceRest 60862).take 1 = separatorChars := by rfl

theorem separator_original_split : sourceRest 60862 = separatorChars ++ sourceRest 60863 := by
  calc
    sourceRest 60862 = (sourceRest 60862).take 1 ++ (sourceRest 60862).drop 1 :=
      (List.take_append_drop 1 (sourceRest 60862)).symm
    _ = separatorChars ++ (sourceRest 60862).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 60862).drop 1) separator_original_prefix
    _ = separatorChars ++ sourceRest 60863 :=
      congrArg (fun tail => separatorChars ++ tail) (sourceRest_drop 60862 1)

theorem object_original_field (fuel : Nat) :
    SourceJson.object (fuel + 67) (SourceJson.white (sourceRest 47412)) VerticesField.fieldAcc =
      SourceJson.object (fuel + 66) (SourceJson.white (sourceRest 60863)) fieldAcc := by
  calc
    SourceJson.object (fuel + 67) (SourceJson.white (sourceRest 47412)) VerticesField.fieldAcc =
        (SourceJson.value (fuel + 66) (sourceRest 47433)).bind (afterValue (fuel + 66)) :=
      object_original_header fuel
    _ = (Except.ok (VertexValuesValue.arrayValue, sourceRest 60862)).bind (afterValue (fuel + 66)) :=
      congrArg (fun result => result.bind (afterValue (fuel + 66)))
        (VertexValuesValue.value_array_original (fuel + 0))
    _ = (Except.ok (VertexValuesValue.arrayValue, separatorChars ++ sourceRest 60863)).bind
          (afterValue (fuel + 66)) :=
      congrArg (fun rest => (Except.ok (VertexValuesValue.arrayValue, rest)).bind (afterValue (fuel + 66)))
        separator_original_split
    _ = SourceJson.object (fuel + 66) (SourceJson.white (sourceRest 60863)) fieldAcc :=
      after_value_separator fuel (sourceRest 60863)

theorem sourceChars_through_field :
    SourceJson.value 201043 sourceChars =
      SourceJson.object 201034 (SourceJson.white (sourceRest 60863)) fieldAcc :=
  VerticesField.sourceChars_through_field.trans (object_original_field 200968)

#print axioms after_value_separator
#print axioms separator_original_prefix
#print axioms separator_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end VertexValuesField

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
