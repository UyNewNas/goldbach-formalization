import ImbalancedChen.P2OriginalSaving19Geometry01DirectActive8EnumerationField

/-! Exact original object header; unchanged duplicate-key and error branches.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace VerticesField

noncomputable def headerChars : List Char := ['\r', '\n', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ']
noncomputable def fieldKey : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def afterValue (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fieldKey, result.1) :: Active8EnumerationField.fieldAcc).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fieldKey, result.1) :: Active8EnumerationField.fieldAcc)
  | _ => .error "object separator missing"

theorem object_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 68) (SourceJson.white (headerChars ++ rest)) Active8EnumerationField.fieldAcc =
      (SourceJson.value (fuel + 67) rest).bind (afterValue (fuel + 67)) := by rfl

theorem header_original_prefix :
    (sourceRest 122782).take 16 = headerChars := by rfl

theorem header_original_split : sourceRest 122782 = headerChars ++ sourceRest 122798 := by
  calc
    sourceRest 122782 = (sourceRest 122782).take 16 ++ (sourceRest 122782).drop 16 :=
      (List.take_append_drop 16 (sourceRest 122782)).symm
    _ = headerChars ++ (sourceRest 122782).drop 16 :=
      congrArg (fun part => part ++ (sourceRest 122782).drop 16) header_original_prefix
    _ = headerChars ++ sourceRest 122798 :=
      congrArg (fun tail => headerChars ++ tail) (sourceRest_drop 122782 16)

theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + 68) (SourceJson.white (sourceRest 122782)) Active8EnumerationField.fieldAcc =
      (SourceJson.value (fuel + 67) (sourceRest 122798)).bind (afterValue (fuel + 67)) :=
  (congrArg (fun chars => SourceJson.object (fuel + 68) (SourceJson.white chars) Active8EnumerationField.fieldAcc)
    header_original_split).trans (object_header fuel (sourceRest 122798))

theorem sourceChars_pending_value :
    SourceJson.value 470902 sourceChars =
      (SourceJson.value 470894 (sourceRest 122798)).bind (afterValue 470894) :=
  Active8EnumerationField.sourceChars_through_field.trans (object_original_header 470827)

#print axioms object_header
#print axioms header_original_prefix
#print axioms header_original_split
#print axioms object_original_header
#print axioms sourceChars_pending_value

end VerticesField

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
