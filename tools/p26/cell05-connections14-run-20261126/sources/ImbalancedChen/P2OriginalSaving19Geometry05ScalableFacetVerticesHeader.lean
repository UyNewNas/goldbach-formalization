import ImbalancedChen.P2OriginalSaving19Geometry05ScalableAllOriginalConstraintMinimaField

/-! Exact original object header; unchanged duplicate-key and error branches.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FacetVerticesField

noncomputable def headerChars : List Char := ['\r', '\n', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ']
noncomputable def fieldKey : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def afterValue (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fieldKey, result.1) :: AllOriginalConstraintMinimaField.fieldAcc).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fieldKey, result.1) :: AllOriginalConstraintMinimaField.fieldAcc)
  | _ => .error "object separator missing"

theorem object_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 39) (SourceJson.white (headerChars ++ rest)) AllOriginalConstraintMinimaField.fieldAcc =
      (SourceJson.value (fuel + 38) rest).bind (afterValue (fuel + 38)) := by rfl

theorem header_original_prefix :
    (sourceRest 63027).take 22 = headerChars := by rfl

theorem header_original_split : sourceRest 63027 = headerChars ++ sourceRest 63049 := by
  calc
    sourceRest 63027 = (sourceRest 63027).take 22 ++ (sourceRest 63027).drop 22 :=
      (List.take_append_drop 22 (sourceRest 63027)).symm
    _ = headerChars ++ (sourceRest 63027).drop 22 :=
      congrArg (fun part => part ++ (sourceRest 63027).drop 22) header_original_prefix
    _ = headerChars ++ sourceRest 63049 :=
      congrArg (fun tail => headerChars ++ tail) (sourceRest_drop 63027 22)

theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + 39) (SourceJson.white (sourceRest 63027)) AllOriginalConstraintMinimaField.fieldAcc =
      (SourceJson.value (fuel + 38) (sourceRest 63049)).bind (afterValue (fuel + 38)) :=
  (congrArg (fun chars => SourceJson.object (fuel + 39) (SourceJson.white chars) AllOriginalConstraintMinimaField.fieldAcc)
    header_original_split).trans (object_header fuel (sourceRest 63049))

theorem sourceChars_pending_value :
    SourceJson.value 201043 sourceChars =
      (SourceJson.value 201032 (sourceRest 63049)).bind (afterValue 201032) :=
  AllOriginalConstraintMinimaField.sourceChars_through_field.trans (object_original_header 200994)

#print axioms object_header
#print axioms header_original_prefix
#print axioms header_original_split
#print axioms object_original_header
#print axioms sourceChars_pending_value

end FacetVerticesField

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
