import ImbalancedChen.P2OriginalSaving19Geometry05ScalableSimplicesHeader
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableSimplicesValue

/-! Insert the completed original array into its original parent object.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesField

noncomputable def separatorChars : List Char := [',']
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, SimplicesValue.arrayValue) :: FaceLedgerField.fieldAcc

theorem after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (SimplicesValue.arrayValue, separatorChars ++ tail)).bind (afterValue (fuel + 474)) =
      SourceJson.object (fuel + 474) (SourceJson.white tail) fieldAcc := by rfl

theorem separator_original_prefix :
    (sourceRest 200699).take 1 = separatorChars := by rfl

theorem separator_original_split : sourceRest 200699 = separatorChars ++ sourceRest 200700 := by
  calc
    sourceRest 200699 = (sourceRest 200699).take 1 ++ (sourceRest 200699).drop 1 :=
      (List.take_append_drop 1 (sourceRest 200699)).symm
    _ = separatorChars ++ (sourceRest 200699).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 200699).drop 1) separator_original_prefix
    _ = separatorChars ++ sourceRest 200700 :=
      congrArg (fun tail => separatorChars ++ tail) (sourceRest_drop 200699 1)

theorem object_original_field (fuel : Nat) :
    SourceJson.object (fuel + 475) (SourceJson.white (sourceRest 104479)) FaceLedgerField.fieldAcc =
      SourceJson.object (fuel + 474) (SourceJson.white (sourceRest 200700)) fieldAcc := by
  calc
    SourceJson.object (fuel + 475) (SourceJson.white (sourceRest 104479)) FaceLedgerField.fieldAcc =
        (SourceJson.value (fuel + 474) (sourceRest 104496)).bind (afterValue (fuel + 474)) :=
      object_original_header fuel
    _ = (Except.ok (SimplicesValue.arrayValue, sourceRest 200699)).bind (afterValue (fuel + 474)) :=
      congrArg (fun result => result.bind (afterValue (fuel + 474)))
        (SimplicesValue.value_array_original (fuel + 0))
    _ = (Except.ok (SimplicesValue.arrayValue, separatorChars ++ sourceRest 200700)).bind
          (afterValue (fuel + 474)) :=
      congrArg (fun rest => (Except.ok (SimplicesValue.arrayValue, rest)).bind (afterValue (fuel + 474)))
        separator_original_split
    _ = SourceJson.object (fuel + 474) (SourceJson.white (sourceRest 200700)) fieldAcc :=
      after_value_separator fuel (sourceRest 200700)

theorem sourceChars_through_field :
    SourceJson.value 201043 sourceChars =
      SourceJson.object 201030 (SourceJson.white (sourceRest 200700)) fieldAcc :=
  FaceLedgerField.sourceChars_through_field.trans (object_original_field 200556)

#print axioms after_value_separator
#print axioms separator_original_prefix
#print axioms separator_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end SimplicesField

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
