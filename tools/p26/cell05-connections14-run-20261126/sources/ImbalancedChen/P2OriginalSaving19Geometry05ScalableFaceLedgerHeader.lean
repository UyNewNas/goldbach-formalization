import ImbalancedChen.P2OriginalSaving19Geometry05ScalableFacetVerticesField

/-! Exact original object header; unchanged duplicate-key and error branches.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
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
    SourceJson.object (fuel + 63) (SourceJson.white (headerChars ++ rest)) FacetVerticesField.fieldAcc =
      (SourceJson.value (fuel + 62) rest).bind (afterValue (fuel + 62)) := by rfl

theorem header_original_prefix :
    (sourceRest 65593).take 19 = headerChars := by rfl

theorem header_original_split : sourceRest 65593 = headerChars ++ sourceRest 65612 := by
  calc
    sourceRest 65593 = (sourceRest 65593).take 19 ++ (sourceRest 65593).drop 19 :=
      (List.take_append_drop 19 (sourceRest 65593)).symm
    _ = headerChars ++ (sourceRest 65593).drop 19 :=
      congrArg (fun part => part ++ (sourceRest 65593).drop 19) header_original_prefix
    _ = headerChars ++ sourceRest 65612 :=
      congrArg (fun tail => headerChars ++ tail) (sourceRest_drop 65593 19)

theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + 63) (SourceJson.white (sourceRest 65593)) FacetVerticesField.fieldAcc =
      (SourceJson.value (fuel + 62) (sourceRest 65612)).bind (afterValue (fuel + 62)) :=
  (congrArg (fun chars => SourceJson.object (fuel + 63) (SourceJson.white chars) FacetVerticesField.fieldAcc)
    header_original_split).trans (object_header fuel (sourceRest 65612))

theorem sourceChars_pending_value :
    SourceJson.value 201043 sourceChars =
      (SourceJson.value 201031 (sourceRest 65612)).bind (afterValue 201031) :=
  FacetVerticesField.sourceChars_through_field.trans (object_original_header 200969)

#print axioms object_header
#print axioms header_original_prefix
#print axioms header_original_split
#print axioms object_original_header
#print axioms sourceChars_pending_value

end FaceLedgerField

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
