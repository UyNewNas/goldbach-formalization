import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVertexValuesField

/-! Exact original object header; unchanged duplicate-key and error branches.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace AllOriginalConstraintMinimaField

noncomputable def headerChars : List Char := ['\r', '\n', ' ', ' ', '"', 'a', 'l', 'l', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'c', 'o', 'n', 's', 't', 'r', 'a', 'i', 'n', 't', '_', 'm', 'i', 'n', 'i', 'm', 'a', '"', ':', ' ']
noncomputable def fieldKey : String := String.ofList ['a', 'l', 'l', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'c', 'o', 'n', 's', 't', 'r', 'a', 'i', 'n', 't', '_', 'm', 'i', 'n', 'i', 'm', 'a']
noncomputable def afterValue (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fieldKey, result.1) :: VertexValuesField.fieldAcc).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fieldKey, result.1) :: VertexValuesField.fieldAcc)
  | _ => .error "object separator missing"

theorem object_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 118) (SourceJson.white (headerChars ++ rest)) VertexValuesField.fieldAcc =
      (SourceJson.value (fuel + 117) rest).bind (afterValue (fuel + 117)) := by rfl

theorem header_original_prefix :
    (sourceRest 60863).take 38 = headerChars := by rfl

theorem header_original_split : sourceRest 60863 = headerChars ++ sourceRest 60901 := by
  calc
    sourceRest 60863 = (sourceRest 60863).take 38 ++ (sourceRest 60863).drop 38 :=
      (List.take_append_drop 38 (sourceRest 60863)).symm
    _ = headerChars ++ (sourceRest 60863).drop 38 :=
      congrArg (fun part => part ++ (sourceRest 60863).drop 38) header_original_prefix
    _ = headerChars ++ sourceRest 60901 :=
      congrArg (fun tail => headerChars ++ tail) (sourceRest_drop 60863 38)

theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + 118) (SourceJson.white (sourceRest 60863)) VertexValuesField.fieldAcc =
      (SourceJson.value (fuel + 117) (sourceRest 60901)).bind (afterValue (fuel + 117)) :=
  (congrArg (fun chars => SourceJson.object (fuel + 118) (SourceJson.white chars) VertexValuesField.fieldAcc)
    header_original_split).trans (object_header fuel (sourceRest 60901))

theorem sourceChars_pending_value :
    SourceJson.value 201043 sourceChars =
      (SourceJson.value 201033 (sourceRest 60901)).bind (afterValue 201033) :=
  VertexValuesField.sourceChars_through_field.trans (object_original_header 200916)

#print axioms object_header
#print axioms header_original_prefix
#print axioms header_original_split
#print axioms object_original_header
#print axioms sourceChars_pending_value

end AllOriginalConstraintMinimaField

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
