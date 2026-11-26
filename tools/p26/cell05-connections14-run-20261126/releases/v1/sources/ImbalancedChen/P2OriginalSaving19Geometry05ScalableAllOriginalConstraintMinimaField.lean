import ImbalancedChen.P2OriginalSaving19Geometry05ScalableAllOriginalConstraintMinimaHeader
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableAllOriginalConstraintMinimaValue

/-! Insert the completed original array into its original parent object.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace AllOriginalConstraintMinimaField

noncomputable def separatorChars : List Char := [',']
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, AllOriginalConstraintMinimaValue.arrayValue) :: VertexValuesField.fieldAcc

theorem after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (AllOriginalConstraintMinimaValue.arrayValue, separatorChars ++ tail)).bind (afterValue (fuel + 117)) =
      SourceJson.object (fuel + 117) (SourceJson.white tail) fieldAcc := by rfl

theorem separator_original_prefix :
    (sourceRest 63026).take 1 = separatorChars := by rfl

theorem separator_original_split : sourceRest 63026 = separatorChars ++ sourceRest 63027 := by
  calc
    sourceRest 63026 = (sourceRest 63026).take 1 ++ (sourceRest 63026).drop 1 :=
      (List.take_append_drop 1 (sourceRest 63026)).symm
    _ = separatorChars ++ (sourceRest 63026).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 63026).drop 1) separator_original_prefix
    _ = separatorChars ++ sourceRest 63027 :=
      congrArg (fun tail => separatorChars ++ tail) (sourceRest_drop 63026 1)

theorem object_original_field (fuel : Nat) :
    SourceJson.object (fuel + 118) (SourceJson.white (sourceRest 60863)) VertexValuesField.fieldAcc =
      SourceJson.object (fuel + 117) (SourceJson.white (sourceRest 63027)) fieldAcc := by
  calc
    SourceJson.object (fuel + 118) (SourceJson.white (sourceRest 60863)) VertexValuesField.fieldAcc =
        (SourceJson.value (fuel + 117) (sourceRest 60901)).bind (afterValue (fuel + 117)) :=
      object_original_header fuel
    _ = (Except.ok (AllOriginalConstraintMinimaValue.arrayValue, sourceRest 63026)).bind (afterValue (fuel + 117)) :=
      congrArg (fun result => result.bind (afterValue (fuel + 117)))
        (AllOriginalConstraintMinimaValue.value_array_original (fuel + 0))
    _ = (Except.ok (AllOriginalConstraintMinimaValue.arrayValue, separatorChars ++ sourceRest 63027)).bind
          (afterValue (fuel + 117)) :=
      congrArg (fun rest => (Except.ok (AllOriginalConstraintMinimaValue.arrayValue, rest)).bind (afterValue (fuel + 117)))
        separator_original_split
    _ = SourceJson.object (fuel + 117) (SourceJson.white (sourceRest 63027)) fieldAcc :=
      after_value_separator fuel (sourceRest 63027)

theorem sourceChars_through_field :
    SourceJson.value 201043 sourceChars =
      SourceJson.object 201033 (SourceJson.white (sourceRest 63027)) fieldAcc :=
  VertexValuesField.sourceChars_through_field.trans (object_original_field 200916)

#print axioms after_value_separator
#print axioms separator_original_prefix
#print axioms separator_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end AllOriginalConstraintMinimaField

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
