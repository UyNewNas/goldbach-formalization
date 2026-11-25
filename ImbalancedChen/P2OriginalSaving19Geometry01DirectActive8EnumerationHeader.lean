import ImbalancedChen.P2OriginalSaving19Geometry01DirectMetadata05

/-! Exact original object header; unchanged duplicate-key and error branches.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace Active8EnumerationField

noncomputable def headerChars : List Char := ['\r', '\n', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '8', '_', 'e', 'n', 'u', 'm', 'e', 'r', 'a', 't', 'i', 'o', 'n', '"', ':', ' ']
noncomputable def fieldKey : String := String.ofList ['a', 'c', 't', 'i', 'v', 'e', '8', '_', 'e', 'n', 'u', 'm', 'e', 'r', 'a', 't', 'i', 'o', 'n']
noncomputable def afterValue (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fieldKey, result.1) :: Metadata05.metadataAcc).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fieldKey, result.1) :: Metadata05.metadataAcc)
  | _ => .error "object separator missing"

theorem object_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 525) (SourceJson.white (headerChars ++ rest)) Metadata05.metadataAcc =
      (SourceJson.value (fuel + 524) rest).bind (afterValue (fuel + 524)) := by rfl

theorem header_original_prefix :
    (sourceRest 394).take 27 = headerChars := by rfl

theorem header_original_split : sourceRest 394 = headerChars ++ sourceRest 421 := by
  calc
    sourceRest 394 = (sourceRest 394).take 27 ++ (sourceRest 394).drop 27 :=
      (List.take_append_drop 27 (sourceRest 394)).symm
    _ = headerChars ++ (sourceRest 394).drop 27 :=
      congrArg (fun part => part ++ (sourceRest 394).drop 27) header_original_prefix
    _ = headerChars ++ sourceRest 421 :=
      congrArg (fun tail => headerChars ++ tail) (sourceRest_drop 394 27)

theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + 525) (SourceJson.white (sourceRest 394)) Metadata05.metadataAcc =
      (SourceJson.value (fuel + 524) (sourceRest 421)).bind (afterValue (fuel + 524)) :=
  (congrArg (fun chars => SourceJson.object (fuel + 525) (SourceJson.white chars) Metadata05.metadataAcc)
    header_original_split).trans (object_header fuel (sourceRest 421))

theorem sourceChars_pending_value :
    SourceJson.value 470902 sourceChars =
      (SourceJson.value 470895 (sourceRest 421)).bind (afterValue 470895) :=
  Metadata05.sourceChars_through_metadata.trans (object_original_header 470371)

#print axioms object_header
#print axioms header_original_prefix
#print axioms header_original_split
#print axioms object_original_header
#print axioms sourceChars_pending_value

end Active8EnumerationField

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
