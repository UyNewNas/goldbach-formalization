import ImbalancedChen.P2OriginalSaving19Geometry05ScalableActive8EnumerationHeader
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableActive8EnumerationValue

/-! Insert the completed original array into its original parent object.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace Active8EnumerationField

noncomputable def separatorChars : List Char := [',']
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, Active8EnumerationValue.arrayValue) :: Metadata05.metadataAcc

theorem after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (Active8EnumerationValue.arrayValue, separatorChars ++ tail)).bind (afterValue (fuel + 194)) =
      SourceJson.object (fuel + 194) (SourceJson.white tail) fieldAcc := by rfl

theorem separator_original_prefix :
    (sourceRest 41065).take 1 = separatorChars := by rfl

theorem separator_original_split : sourceRest 41065 = separatorChars ++ sourceRest 41066 := by
  calc
    sourceRest 41065 = (sourceRest 41065).take 1 ++ (sourceRest 41065).drop 1 :=
      (List.take_append_drop 1 (sourceRest 41065)).symm
    _ = separatorChars ++ (sourceRest 41065).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 41065).drop 1) separator_original_prefix
    _ = separatorChars ++ sourceRest 41066 :=
      congrArg (fun tail => separatorChars ++ tail) (sourceRest_drop 41065 1)

theorem object_original_field (fuel : Nat) :
    SourceJson.object (fuel + 195) (SourceJson.white (sourceRest 389)) Metadata05.metadataAcc =
      SourceJson.object (fuel + 194) (SourceJson.white (sourceRest 41066)) fieldAcc := by
  calc
    SourceJson.object (fuel + 195) (SourceJson.white (sourceRest 389)) Metadata05.metadataAcc =
        (SourceJson.value (fuel + 194) (sourceRest 416)).bind (afterValue (fuel + 194)) :=
      object_original_header fuel
    _ = (Except.ok (Active8EnumerationValue.arrayValue, sourceRest 41065)).bind (afterValue (fuel + 194)) :=
      congrArg (fun result => result.bind (afterValue (fuel + 194)))
        (Active8EnumerationValue.value_array_original (fuel + 0))
    _ = (Except.ok (Active8EnumerationValue.arrayValue, separatorChars ++ sourceRest 41066)).bind
          (afterValue (fuel + 194)) :=
      congrArg (fun rest => (Except.ok (Active8EnumerationValue.arrayValue, rest)).bind (afterValue (fuel + 194)))
        separator_original_split
    _ = SourceJson.object (fuel + 194) (SourceJson.white (sourceRest 41066)) fieldAcc :=
      after_value_separator fuel (sourceRest 41066)

theorem sourceChars_through_field :
    SourceJson.value 201043 sourceChars =
      SourceJson.object 201036 (SourceJson.white (sourceRest 41066)) fieldAcc :=
  Metadata05.sourceChars_through_metadata.trans (object_original_field 200842)

#print axioms after_value_separator
#print axioms separator_original_prefix
#print axioms separator_original_split
#print axioms object_original_field
#print axioms sourceChars_through_field

end Active8EnumerationField

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
