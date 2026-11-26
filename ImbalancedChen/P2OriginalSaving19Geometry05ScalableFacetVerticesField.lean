import ImbalancedChen.P2OriginalSaving19Geometry05ScalableFacetVerticesHeader
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableFacetVerticesValue

/-! Insert the completed original array into its original parent object.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FacetVerticesField

noncomputable def separatorChars : List Char := [',']
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, FacetVerticesValue.arrayValue) :: AllOriginalConstraintMinimaField.fieldAcc

theorem after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (FacetVerticesValue.arrayValue, separatorChars ++ tail)).bind (afterValue (fuel + 38)) =
      SourceJson.object (fuel + 38) (SourceJson.white tail) fieldAcc := by rfl

theorem separator_original_prefix :
    (sourceRest 65592).take 1 = separatorChars := by rfl

theorem separator_original_split : sourceRest 65592 = separatorChars ++ sourceRest 65593 := by
  calc
    sourceRest 65592 = (sourceRest 65592).take 1 ++ (sourceRest 65592).drop 1 :=
      (List.take_append_drop 1 (sourceRest 65592)).symm
    _ = separatorChars ++ (sourceRest 65592).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 65592).drop 1) separator_original_prefix
    _ = separatorChars ++ sourceRest 65593 :=
      congrArg (fun tail => separatorChars ++ tail) (sourceRest_drop 65592 1)

theorem object_original_field (fuel : Nat) :
    SourceJson.object (fuel + 39) (SourceJson.white (sourceRest 63027)) AllOriginalConstraintMinimaField.fieldAcc =
      SourceJson.object (fuel + 38) (SourceJson.white (sourceRest 65593)) fieldAcc := by
  calc
    SourceJson.object (fuel + 39) (SourceJson.white (sourceRest 63027)) AllOriginalConstraintMinimaField.fieldAcc =
        (SourceJson.value (fuel + 38) (sourceRest 63049)).bind (afterValue (fuel + 38)) :=
      object_original_header fuel
    _ = (Except.ok (FacetVerticesValue.arrayValue, sourceRest 65592)).bind (afterValue (fuel + 38)) :=
      congrArg (fun result => result.bind (afterValue (fuel + 38)))
        (FacetVerticesValue.value_array_original (fuel + 0))
    _ = (Except.ok (FacetVerticesValue.arrayValue, separatorChars ++ sourceRest 65593)).bind
          (afterValue (fuel + 38)) :=
      congrArg (fun rest => (Except.ok (FacetVerticesValue.arrayValue, rest)).bind (afterValue (fuel + 38)))
        separator_original_split
    _ = SourceJson.object (fuel + 38) (SourceJson.white (sourceRest 65593)) fieldAcc :=
      after_value_separator fuel (sourceRest 65593)

theorem sourceChars_through_field :
    SourceJson.value 201043 sourceChars =
      SourceJson.object 201032 (SourceJson.white (sourceRest 65593)) fieldAcc :=
  AllOriginalConstraintMinimaField.sourceChars_through_field.trans (object_original_field 200994)

#print axioms after_value_separator
#print axioms separator_original_prefix
#print axioms separator_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end FacetVerticesField

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
