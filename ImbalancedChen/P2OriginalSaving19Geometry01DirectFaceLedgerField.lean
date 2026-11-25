import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerHeader
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue

/-! Insert the completed original array into its original parent object.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FaceLedgerField

noncomputable def separatorChars : List Char := [',']
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, FaceLedgerValue.arrayValue) :: FacetVerticesField.fieldAcc

theorem after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (FaceLedgerValue.arrayValue, separatorChars ++ tail)).bind (afterValue (fuel + 100)) =
      SourceJson.object (fuel + 100) (SourceJson.white tail) fieldAcc := by rfl

theorem separator_original_prefix :
    (sourceRest 225544).take 1 = separatorChars := by rfl

theorem separator_original_split : sourceRest 225544 = separatorChars ++ sourceRest 225545 := by
  calc
    sourceRest 225544 = (sourceRest 225544).take 1 ++ (sourceRest 225544).drop 1 :=
      (List.take_append_drop 1 (sourceRest 225544)).symm
    _ = separatorChars ++ (sourceRest 225544).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 225544).drop 1) separator_original_prefix
    _ = separatorChars ++ sourceRest 225545 :=
      congrArg (fun tail => separatorChars ++ tail) (sourceRest_drop 225544 1)

theorem object_original_field (fuel : Nat) :
    SourceJson.object (fuel + 101) (SourceJson.white (sourceRest 156629)) FacetVerticesField.fieldAcc =
      SourceJson.object (fuel + 100) (SourceJson.white (sourceRest 225545)) fieldAcc := by
  calc
    SourceJson.object (fuel + 101) (SourceJson.white (sourceRest 156629)) FacetVerticesField.fieldAcc =
        (SourceJson.value (fuel + 100) (sourceRest 156648)).bind (afterValue (fuel + 100)) :=
      object_original_header fuel
    _ = (Except.ok (FaceLedgerValue.arrayValue, sourceRest 225544)).bind (afterValue (fuel + 100)) :=
      congrArg (fun result => result.bind (afterValue (fuel + 100)))
        (FaceLedgerValue.value_array_original (fuel + 0))
    _ = (Except.ok (FaceLedgerValue.arrayValue, separatorChars ++ sourceRest 225545)).bind
          (afterValue (fuel + 100)) :=
      congrArg (fun rest => (Except.ok (FaceLedgerValue.arrayValue, rest)).bind (afterValue (fuel + 100)))
        separator_original_split
    _ = SourceJson.object (fuel + 100) (SourceJson.white (sourceRest 225545)) fieldAcc :=
      after_value_separator fuel (sourceRest 225545)

theorem sourceChars_through_field :
    SourceJson.value 470902 sourceChars =
      SourceJson.object 470890 (SourceJson.white (sourceRest 225545)) fieldAcc :=
  FacetVerticesField.sourceChars_through_field.trans (object_original_field 470790)

#print axioms after_value_separator
#print axioms separator_original_prefix
#print axioms separator_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end FaceLedgerField

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
