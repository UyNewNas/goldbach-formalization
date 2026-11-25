import ImbalancedChen.P2OriginalSaving19Geometry01DirectFacetVerticesHeader
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFacetVerticesValue

/-! Insert the completed original array into its original parent object.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FacetVerticesField

noncomputable def separatorChars : List Char := [',']
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, FacetVerticesValue.arrayValue) :: AllOriginalConstraintMinimaField.fieldAcc

theorem after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (FacetVerticesValue.arrayValue, separatorChars ++ tail)).bind (afterValue (fuel + 49)) =
      SourceJson.object (fuel + 49) (SourceJson.white tail) fieldAcc := by rfl

theorem separator_original_prefix :
    (sourceRest 156628).take 1 = separatorChars := by rfl

theorem separator_original_split : sourceRest 156628 = separatorChars ++ sourceRest 156629 := by
  calc
    sourceRest 156628 = (sourceRest 156628).take 1 ++ (sourceRest 156628).drop 1 :=
      (List.take_append_drop 1 (sourceRest 156628)).symm
    _ = separatorChars ++ (sourceRest 156628).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 156628).drop 1) separator_original_prefix
    _ = separatorChars ++ sourceRest 156629 :=
      congrArg (fun tail => separatorChars ++ tail) (sourceRest_drop 156628 1)

theorem object_original_field (fuel : Nat) :
    SourceJson.object (fuel + 50) (SourceJson.white (sourceRest 152993)) AllOriginalConstraintMinimaField.fieldAcc =
      SourceJson.object (fuel + 49) (SourceJson.white (sourceRest 156629)) fieldAcc := by
  calc
    SourceJson.object (fuel + 50) (SourceJson.white (sourceRest 152993)) AllOriginalConstraintMinimaField.fieldAcc =
        (SourceJson.value (fuel + 49) (sourceRest 153015)).bind (afterValue (fuel + 49)) :=
      object_original_header fuel
    _ = (Except.ok (FacetVerticesValue.arrayValue, sourceRest 156628)).bind (afterValue (fuel + 49)) :=
      congrArg (fun result => result.bind (afterValue (fuel + 49)))
        (FacetVerticesValue.value_array_original (fuel + 0))
    _ = (Except.ok (FacetVerticesValue.arrayValue, separatorChars ++ sourceRest 156629)).bind
          (afterValue (fuel + 49)) :=
      congrArg (fun rest => (Except.ok (FacetVerticesValue.arrayValue, rest)).bind (afterValue (fuel + 49)))
        separator_original_split
    _ = SourceJson.object (fuel + 49) (SourceJson.white (sourceRest 156629)) fieldAcc :=
      after_value_separator fuel (sourceRest 156629)

theorem sourceChars_through_field :
    SourceJson.value 470902 sourceChars =
      SourceJson.object 470891 (SourceJson.white (sourceRest 156629)) fieldAcc :=
  AllOriginalConstraintMinimaField.sourceChars_through_field.trans (object_original_field 470842)

#print axioms after_value_separator
#print axioms separator_original_prefix
#print axioms separator_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end FacetVerticesField

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
