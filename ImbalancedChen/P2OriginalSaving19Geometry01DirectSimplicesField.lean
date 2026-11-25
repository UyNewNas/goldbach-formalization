import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesHeader
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue

/-! Insert the completed original array into its original parent object.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesField

noncomputable def separatorChars : List Char := [',']
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, SimplicesValue.arrayValue) :: FaceLedgerField.fieldAcc

theorem after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (SimplicesValue.arrayValue, separatorChars ++ tail)).bind (afterValue (fuel + 605)) =
      SourceJson.object (fuel + 605) (SourceJson.white tail) fieldAcc := by rfl

theorem separator_original_prefix :
    (sourceRest 470499).take 1 = separatorChars := by rfl

theorem separator_original_split : sourceRest 470499 = separatorChars ++ sourceRest 470500 := by
  calc
    sourceRest 470499 = (sourceRest 470499).take 1 ++ (sourceRest 470499).drop 1 :=
      (List.take_append_drop 1 (sourceRest 470499)).symm
    _ = separatorChars ++ (sourceRest 470499).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 470499).drop 1) separator_original_prefix
    _ = separatorChars ++ sourceRest 470500 :=
      congrArg (fun tail => separatorChars ++ tail) (sourceRest_drop 470499 1)

theorem object_original_field (fuel : Nat) :
    SourceJson.object (fuel + 606) (SourceJson.white (sourceRest 225545)) FaceLedgerField.fieldAcc =
      SourceJson.object (fuel + 605) (SourceJson.white (sourceRest 470500)) fieldAcc := by
  calc
    SourceJson.object (fuel + 606) (SourceJson.white (sourceRest 225545)) FaceLedgerField.fieldAcc =
        (SourceJson.value (fuel + 605) (sourceRest 225562)).bind (afterValue (fuel + 605)) :=
      object_original_header fuel
    _ = (Except.ok (SimplicesValue.arrayValue, sourceRest 470499)).bind (afterValue (fuel + 605)) :=
      congrArg (fun result => result.bind (afterValue (fuel + 605)))
        (SimplicesValue.value_array_original (fuel + 0))
    _ = (Except.ok (SimplicesValue.arrayValue, separatorChars ++ sourceRest 470500)).bind
          (afterValue (fuel + 605)) :=
      congrArg (fun rest => (Except.ok (SimplicesValue.arrayValue, rest)).bind (afterValue (fuel + 605)))
        separator_original_split
    _ = SourceJson.object (fuel + 605) (SourceJson.white (sourceRest 470500)) fieldAcc :=
      after_value_separator fuel (sourceRest 470500)

theorem sourceChars_through_field :
    SourceJson.value 470902 sourceChars =
      SourceJson.object 470889 (SourceJson.white (sourceRest 470500)) fieldAcc :=
  FaceLedgerField.sourceChars_through_field.trans (object_original_field 470284)

#print axioms after_value_separator
#print axioms separator_original_prefix
#print axioms separator_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end SimplicesField

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
