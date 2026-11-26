import ImbalancedChen.P2OriginalSaving19Geometry05ScalableFaceLedgerHeader
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableFaceLedgerValue

/-! Insert the completed original array into its original parent object.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FaceLedgerField

noncomputable def separatorChars : List Char := [',']
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, FaceLedgerValue.arrayValue) :: FacetVerticesField.fieldAcc

theorem after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (FaceLedgerValue.arrayValue, separatorChars ++ tail)).bind (afterValue (fuel + 62)) =
      SourceJson.object (fuel + 62) (SourceJson.white tail) fieldAcc := by rfl

theorem separator_original_prefix :
    (sourceRest 104478).take 1 = separatorChars := by rfl

theorem separator_original_split : sourceRest 104478 = separatorChars ++ sourceRest 104479 := by
  calc
    sourceRest 104478 = (sourceRest 104478).take 1 ++ (sourceRest 104478).drop 1 :=
      (List.take_append_drop 1 (sourceRest 104478)).symm
    _ = separatorChars ++ (sourceRest 104478).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 104478).drop 1) separator_original_prefix
    _ = separatorChars ++ sourceRest 104479 :=
      congrArg (fun tail => separatorChars ++ tail) (sourceRest_drop 104478 1)

theorem object_original_field (fuel : Nat) :
    SourceJson.object (fuel + 63) (SourceJson.white (sourceRest 65593)) FacetVerticesField.fieldAcc =
      SourceJson.object (fuel + 62) (SourceJson.white (sourceRest 104479)) fieldAcc := by
  calc
    SourceJson.object (fuel + 63) (SourceJson.white (sourceRest 65593)) FacetVerticesField.fieldAcc =
        (SourceJson.value (fuel + 62) (sourceRest 65612)).bind (afterValue (fuel + 62)) :=
      object_original_header fuel
    _ = (Except.ok (FaceLedgerValue.arrayValue, sourceRest 104478)).bind (afterValue (fuel + 62)) :=
      congrArg (fun result => result.bind (afterValue (fuel + 62)))
        (FaceLedgerValue.value_array_original (fuel + 0))
    _ = (Except.ok (FaceLedgerValue.arrayValue, separatorChars ++ sourceRest 104479)).bind
          (afterValue (fuel + 62)) :=
      congrArg (fun rest => (Except.ok (FaceLedgerValue.arrayValue, rest)).bind (afterValue (fuel + 62)))
        separator_original_split
    _ = SourceJson.object (fuel + 62) (SourceJson.white (sourceRest 104479)) fieldAcc :=
      after_value_separator fuel (sourceRest 104479)

theorem sourceChars_through_field :
    SourceJson.value 201043 sourceChars =
      SourceJson.object 201031 (SourceJson.white (sourceRest 104479)) fieldAcc :=
  FacetVerticesField.sourceChars_through_field.trans (object_original_field 200969)

#print axioms after_value_separator
#print axioms separator_original_prefix
#print axioms separator_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end FaceLedgerField

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
