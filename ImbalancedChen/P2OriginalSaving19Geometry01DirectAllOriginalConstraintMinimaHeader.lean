import ImbalancedChen.P2OriginalSaving19Geometry01DirectVertexValuesField

/-! Exact original object header; unchanged duplicate-key and error branches.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
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
    (sourceRest 150827).take 38 = headerChars := by rfl

theorem header_original_split : sourceRest 150827 = headerChars ++ sourceRest 150865 := by
  calc
    sourceRest 150827 = (sourceRest 150827).take 38 ++ (sourceRest 150827).drop 38 :=
      (List.take_append_drop 38 (sourceRest 150827)).symm
    _ = headerChars ++ (sourceRest 150827).drop 38 :=
      congrArg (fun part => part ++ (sourceRest 150827).drop 38) header_original_prefix
    _ = headerChars ++ sourceRest 150865 :=
      congrArg (fun tail => headerChars ++ tail) (sourceRest_drop 150827 38)

theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + 118) (SourceJson.white (sourceRest 150827)) VertexValuesField.fieldAcc =
      (SourceJson.value (fuel + 117) (sourceRest 150865)).bind (afterValue (fuel + 117)) :=
  (congrArg (fun chars => SourceJson.object (fuel + 118) (SourceJson.white chars) VertexValuesField.fieldAcc)
    header_original_split).trans (object_header fuel (sourceRest 150865))

theorem sourceChars_pending_value :
    SourceJson.value 470902 sourceChars =
      (SourceJson.value 470892 (sourceRest 150865)).bind (afterValue 470892) :=
  VertexValuesField.sourceChars_through_field.trans (object_original_header 470775)

#print axioms object_header
#print axioms header_original_prefix
#print axioms header_original_split
#print axioms object_original_header
#print axioms sourceChars_pending_value

end AllOriginalConstraintMinimaField

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
