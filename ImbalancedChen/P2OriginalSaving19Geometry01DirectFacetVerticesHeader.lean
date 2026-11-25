import ImbalancedChen.P2OriginalSaving19Geometry01DirectAllOriginalConstraintMinimaField

/-! Exact original object header; unchanged duplicate-key and error branches.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
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
    SourceJson.object (fuel + 50) (SourceJson.white (headerChars ++ rest)) AllOriginalConstraintMinimaField.fieldAcc =
      (SourceJson.value (fuel + 49) rest).bind (afterValue (fuel + 49)) := by rfl

theorem header_original_prefix :
    (sourceRest 152993).take 22 = headerChars := by rfl

theorem header_original_split : sourceRest 152993 = headerChars ++ sourceRest 153015 := by
  calc
    sourceRest 152993 = (sourceRest 152993).take 22 ++ (sourceRest 152993).drop 22 :=
      (List.take_append_drop 22 (sourceRest 152993)).symm
    _ = headerChars ++ (sourceRest 152993).drop 22 :=
      congrArg (fun part => part ++ (sourceRest 152993).drop 22) header_original_prefix
    _ = headerChars ++ sourceRest 153015 :=
      congrArg (fun tail => headerChars ++ tail) (sourceRest_drop 152993 22)

theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + 50) (SourceJson.white (sourceRest 152993)) AllOriginalConstraintMinimaField.fieldAcc =
      (SourceJson.value (fuel + 49) (sourceRest 153015)).bind (afterValue (fuel + 49)) :=
  (congrArg (fun chars => SourceJson.object (fuel + 50) (SourceJson.white chars) AllOriginalConstraintMinimaField.fieldAcc)
    header_original_split).trans (object_header fuel (sourceRest 153015))

theorem sourceChars_pending_value :
    SourceJson.value 470902 sourceChars =
      (SourceJson.value 470891 (sourceRest 153015)).bind (afterValue 470891) :=
  AllOriginalConstraintMinimaField.sourceChars_through_field.trans (object_original_header 470842)

#print axioms object_header
#print axioms header_original_prefix
#print axioms header_original_split
#print axioms object_original_header
#print axioms sourceChars_pending_value

end FacetVerticesField

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
