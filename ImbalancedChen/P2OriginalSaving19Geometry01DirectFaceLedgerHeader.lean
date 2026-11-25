import ImbalancedChen.P2OriginalSaving19Geometry01DirectFacetVerticesField

/-! Exact original object header; unchanged duplicate-key and error branches.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FaceLedgerField

noncomputable def headerChars : List Char := ['\r', '\n', ' ', ' ', '"', 'f', 'a', 'c', 'e', '_', 'l', 'e', 'd', 'g', 'e', 'r', '"', ':', ' ']
noncomputable def fieldKey : String := String.ofList ['f', 'a', 'c', 'e', '_', 'l', 'e', 'd', 'g', 'e', 'r']
noncomputable def afterValue (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fieldKey, result.1) :: FacetVerticesField.fieldAcc).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fieldKey, result.1) :: FacetVerticesField.fieldAcc)
  | _ => .error "object separator missing"

theorem object_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 101) (SourceJson.white (headerChars ++ rest)) FacetVerticesField.fieldAcc =
      (SourceJson.value (fuel + 100) rest).bind (afterValue (fuel + 100)) := by rfl

theorem header_original_prefix :
    (sourceRest 156629).take 19 = headerChars := by rfl

theorem header_original_split : sourceRest 156629 = headerChars ++ sourceRest 156648 := by
  calc
    sourceRest 156629 = (sourceRest 156629).take 19 ++ (sourceRest 156629).drop 19 :=
      (List.take_append_drop 19 (sourceRest 156629)).symm
    _ = headerChars ++ (sourceRest 156629).drop 19 :=
      congrArg (fun part => part ++ (sourceRest 156629).drop 19) header_original_prefix
    _ = headerChars ++ sourceRest 156648 :=
      congrArg (fun tail => headerChars ++ tail) (sourceRest_drop 156629 19)

theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + 101) (SourceJson.white (sourceRest 156629)) FacetVerticesField.fieldAcc =
      (SourceJson.value (fuel + 100) (sourceRest 156648)).bind (afterValue (fuel + 100)) :=
  (congrArg (fun chars => SourceJson.object (fuel + 101) (SourceJson.white chars) FacetVerticesField.fieldAcc)
    header_original_split).trans (object_header fuel (sourceRest 156648))

theorem sourceChars_pending_value :
    SourceJson.value 470902 sourceChars =
      (SourceJson.value 470890 (sourceRest 156648)).bind (afterValue 470890) :=
  FacetVerticesField.sourceChars_through_field.trans (object_original_header 470790)

#print axioms object_header
#print axioms header_original_prefix
#print axioms header_original_split
#print axioms object_original_header
#print axioms sourceChars_pending_value

end FaceLedgerField

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
