import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVerticesField

/-! Exact original object header; unchanged duplicate-key and error branches.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace VertexValuesField

noncomputable def headerChars : List Char := ['\r', '\n', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'v', 'a', 'l', 'u', 'e', 's', '"', ':', ' ']
noncomputable def fieldKey : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'v', 'a', 'l', 'u', 'e', 's']
noncomputable def afterValue (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fieldKey, result.1) :: VerticesField.fieldAcc).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fieldKey, result.1) :: VerticesField.fieldAcc)
  | _ => .error "object separator missing"

theorem object_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 67) (SourceJson.white (headerChars ++ rest)) VerticesField.fieldAcc =
      (SourceJson.value (fuel + 66) rest).bind (afterValue (fuel + 66)) := by rfl

theorem header_original_prefix :
    (sourceRest 47412).take 21 = headerChars := by rfl

theorem header_original_split : sourceRest 47412 = headerChars ++ sourceRest 47433 := by
  calc
    sourceRest 47412 = (sourceRest 47412).take 21 ++ (sourceRest 47412).drop 21 :=
      (List.take_append_drop 21 (sourceRest 47412)).symm
    _ = headerChars ++ (sourceRest 47412).drop 21 :=
      congrArg (fun part => part ++ (sourceRest 47412).drop 21) header_original_prefix
    _ = headerChars ++ sourceRest 47433 :=
      congrArg (fun tail => headerChars ++ tail) (sourceRest_drop 47412 21)

theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + 67) (SourceJson.white (sourceRest 47412)) VerticesField.fieldAcc =
      (SourceJson.value (fuel + 66) (sourceRest 47433)).bind (afterValue (fuel + 66)) :=
  (congrArg (fun chars => SourceJson.object (fuel + 67) (SourceJson.white chars) VerticesField.fieldAcc)
    header_original_split).trans (object_header fuel (sourceRest 47433))

theorem sourceChars_pending_value :
    SourceJson.value 201043 sourceChars =
      (SourceJson.value 201034 (sourceRest 47433)).bind (afterValue 201034) :=
  VerticesField.sourceChars_through_field.trans (object_original_header 200968)

#print axioms object_header
#print axioms header_original_prefix
#print axioms header_original_split
#print axioms object_original_header
#print axioms sourceChars_pending_value

end VertexValuesField

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
