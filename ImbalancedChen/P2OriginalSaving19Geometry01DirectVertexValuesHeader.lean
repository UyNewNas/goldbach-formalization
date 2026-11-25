import ImbalancedChen.P2OriginalSaving19Geometry01DirectVerticesField

/-! Exact original object header; unchanged duplicate-key and error branches.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
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
    SourceJson.object (fuel + 77) (SourceJson.white (headerChars ++ rest)) VerticesField.fieldAcc =
      (SourceJson.value (fuel + 76) rest).bind (afterValue (fuel + 76)) := by rfl

theorem header_original_prefix :
    (sourceRest 131757).take 21 = headerChars := by rfl

theorem header_original_split : sourceRest 131757 = headerChars ++ sourceRest 131778 := by
  calc
    sourceRest 131757 = (sourceRest 131757).take 21 ++ (sourceRest 131757).drop 21 :=
      (List.take_append_drop 21 (sourceRest 131757)).symm
    _ = headerChars ++ (sourceRest 131757).drop 21 :=
      congrArg (fun part => part ++ (sourceRest 131757).drop 21) header_original_prefix
    _ = headerChars ++ sourceRest 131778 :=
      congrArg (fun tail => headerChars ++ tail) (sourceRest_drop 131757 21)

theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + 77) (SourceJson.white (sourceRest 131757)) VerticesField.fieldAcc =
      (SourceJson.value (fuel + 76) (sourceRest 131778)).bind (afterValue (fuel + 76)) :=
  (congrArg (fun chars => SourceJson.object (fuel + 77) (SourceJson.white chars) VerticesField.fieldAcc)
    header_original_split).trans (object_header fuel (sourceRest 131778))

theorem sourceChars_pending_value :
    SourceJson.value 470902 sourceChars =
      (SourceJson.value 470893 (sourceRest 131778)).bind (afterValue 470893) :=
  VerticesField.sourceChars_through_field.trans (object_original_header 470817)

#print axioms object_header
#print axioms header_original_prefix
#print axioms header_original_split
#print axioms object_original_header
#print axioms sourceChars_pending_value

end VertexValuesField

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
