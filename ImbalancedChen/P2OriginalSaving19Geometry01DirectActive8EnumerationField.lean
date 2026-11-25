import ImbalancedChen.P2OriginalSaving19Geometry01DirectActive8EnumerationHeader
import ImbalancedChen.P2OriginalSaving19Geometry01DirectActive8EnumerationValue

/-! Insert the completed original array into its original parent object.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace Active8EnumerationField

noncomputable def separatorChars : List Char := [',']
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, Active8EnumerationValue.arrayValue) :: Metadata05.metadataAcc

theorem after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (Active8EnumerationValue.arrayValue, separatorChars ++ tail)).bind (afterValue (fuel + 524)) =
      SourceJson.object (fuel + 524) (SourceJson.white tail) fieldAcc := by rfl

theorem separator_original_prefix :
    (sourceRest 122781).take 1 = separatorChars := by rfl

theorem separator_original_split : sourceRest 122781 = separatorChars ++ sourceRest 122782 := by
  calc
    sourceRest 122781 = (sourceRest 122781).take 1 ++ (sourceRest 122781).drop 1 :=
      (List.take_append_drop 1 (sourceRest 122781)).symm
    _ = separatorChars ++ (sourceRest 122781).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 122781).drop 1) separator_original_prefix
    _ = separatorChars ++ sourceRest 122782 :=
      congrArg (fun tail => separatorChars ++ tail) (sourceRest_drop 122781 1)

theorem object_original_field (fuel : Nat) :
    SourceJson.object (fuel + 525) (SourceJson.white (sourceRest 394)) Metadata05.metadataAcc =
      SourceJson.object (fuel + 524) (SourceJson.white (sourceRest 122782)) fieldAcc := by
  calc
    SourceJson.object (fuel + 525) (SourceJson.white (sourceRest 394)) Metadata05.metadataAcc =
        (SourceJson.value (fuel + 524) (sourceRest 421)).bind (afterValue (fuel + 524)) :=
      object_original_header fuel
    _ = (Except.ok (Active8EnumerationValue.arrayValue, sourceRest 122781)).bind (afterValue (fuel + 524)) :=
      congrArg (fun result => result.bind (afterValue (fuel + 524)))
        (Active8EnumerationValue.value_array_original (fuel + 0))
    _ = (Except.ok (Active8EnumerationValue.arrayValue, separatorChars ++ sourceRest 122782)).bind
          (afterValue (fuel + 524)) :=
      congrArg (fun rest => (Except.ok (Active8EnumerationValue.arrayValue, rest)).bind (afterValue (fuel + 524)))
        separator_original_split
    _ = SourceJson.object (fuel + 524) (SourceJson.white (sourceRest 122782)) fieldAcc :=
      after_value_separator fuel (sourceRest 122782)

theorem sourceChars_through_field :
    SourceJson.value 470902 sourceChars =
      SourceJson.object 470895 (SourceJson.white (sourceRest 122782)) fieldAcc :=
  Metadata05.sourceChars_through_metadata.trans (object_original_field 470371)

#print axioms after_value_separator
#print axioms separator_original_prefix
#print axioms separator_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end Active8EnumerationField

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
