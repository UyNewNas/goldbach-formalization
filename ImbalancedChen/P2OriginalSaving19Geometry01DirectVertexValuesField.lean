import ImbalancedChen.P2OriginalSaving19Geometry01DirectVertexValuesHeader
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVertexValuesValue

/-! Insert the completed original array into its original parent object.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace VertexValuesField

noncomputable def separatorChars : List Char := [',']
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, VertexValuesValue.arrayValue) :: VerticesField.fieldAcc

theorem after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (VertexValuesValue.arrayValue, separatorChars ++ tail)).bind (afterValue (fuel + 76)) =
      SourceJson.object (fuel + 76) (SourceJson.white tail) fieldAcc := by rfl

theorem separator_original_prefix :
    (sourceRest 150826).take 1 = separatorChars := by rfl

theorem separator_original_split : sourceRest 150826 = separatorChars ++ sourceRest 150827 := by
  calc
    sourceRest 150826 = (sourceRest 150826).take 1 ++ (sourceRest 150826).drop 1 :=
      (List.take_append_drop 1 (sourceRest 150826)).symm
    _ = separatorChars ++ (sourceRest 150826).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 150826).drop 1) separator_original_prefix
    _ = separatorChars ++ sourceRest 150827 :=
      congrArg (fun tail => separatorChars ++ tail) (sourceRest_drop 150826 1)

theorem object_original_field (fuel : Nat) :
    SourceJson.object (fuel + 77) (SourceJson.white (sourceRest 131757)) VerticesField.fieldAcc =
      SourceJson.object (fuel + 76) (SourceJson.white (sourceRest 150827)) fieldAcc := by
  calc
    SourceJson.object (fuel + 77) (SourceJson.white (sourceRest 131757)) VerticesField.fieldAcc =
        (SourceJson.value (fuel + 76) (sourceRest 131778)).bind (afterValue (fuel + 76)) :=
      object_original_header fuel
    _ = (Except.ok (VertexValuesValue.arrayValue, sourceRest 150826)).bind (afterValue (fuel + 76)) :=
      congrArg (fun result => result.bind (afterValue (fuel + 76)))
        (VertexValuesValue.value_array_original (fuel + 0))
    _ = (Except.ok (VertexValuesValue.arrayValue, separatorChars ++ sourceRest 150827)).bind
          (afterValue (fuel + 76)) :=
      congrArg (fun rest => (Except.ok (VertexValuesValue.arrayValue, rest)).bind (afterValue (fuel + 76)))
        separator_original_split
    _ = SourceJson.object (fuel + 76) (SourceJson.white (sourceRest 150827)) fieldAcc :=
      after_value_separator fuel (sourceRest 150827)

theorem sourceChars_through_field :
    SourceJson.value 470902 sourceChars =
      SourceJson.object 470893 (SourceJson.white (sourceRest 150827)) fieldAcc :=
  VerticesField.sourceChars_through_field.trans (object_original_field 470817)

#print axioms after_value_separator
#print axioms separator_original_prefix
#print axioms separator_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end VertexValuesField

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
