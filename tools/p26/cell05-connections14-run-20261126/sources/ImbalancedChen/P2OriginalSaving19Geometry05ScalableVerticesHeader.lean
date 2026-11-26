import ImbalancedChen.P2OriginalSaving19Geometry05ScalableActive8EnumerationField

/-! Exact original object header; unchanged duplicate-key and error branches.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
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
    SourceJson.object (fuel + 58) (SourceJson.white (headerChars ++ rest)) Active8EnumerationField.fieldAcc =
      (SourceJson.value (fuel + 57) rest).bind (afterValue (fuel + 57)) := by rfl

theorem header_original_prefix :
    (sourceRest 41066).take 16 = headerChars := by rfl

theorem header_original_split : sourceRest 41066 = headerChars ++ sourceRest 41082 := by
  calc
    sourceRest 41066 = (sourceRest 41066).take 16 ++ (sourceRest 41066).drop 16 :=
      (List.take_append_drop 16 (sourceRest 41066)).symm
    _ = headerChars ++ (sourceRest 41066).drop 16 :=
      congrArg (fun part => part ++ (sourceRest 41066).drop 16) header_original_prefix
    _ = headerChars ++ sourceRest 41082 :=
      congrArg (fun tail => headerChars ++ tail) (sourceRest_drop 41066 16)

theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + 58) (SourceJson.white (sourceRest 41066)) Active8EnumerationField.fieldAcc =
      (SourceJson.value (fuel + 57) (sourceRest 41082)).bind (afterValue (fuel + 57)) :=
  (congrArg (fun chars => SourceJson.object (fuel + 58) (SourceJson.white chars) Active8EnumerationField.fieldAcc)
    header_original_split).trans (object_header fuel (sourceRest 41082))

theorem sourceChars_pending_value :
    SourceJson.value 201043 sourceChars =
      (SourceJson.value 201035 (sourceRest 41082)).bind (afterValue 201035) :=
  Active8EnumerationField.sourceChars_through_field.trans (object_original_header 200978)

#print axioms object_header
#print axioms header_original_prefix
#print axioms header_original_split
#print axioms object_original_header
#print axioms sourceChars_pending_value

end VerticesField

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
