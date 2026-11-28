import ImbalancedChen.P2OriginalSaving19Geometry06ScalableMetadata05

/-! Exact original object header; unchanged duplicate-key and error branches.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
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
    SourceJson.object (fuel + 195) (SourceJson.white (headerChars ++ rest)) Metadata05.metadataAcc =
      (SourceJson.value (fuel + 194) rest).bind (afterValue (fuel + 194)) := by rfl

theorem header_original_prefix :
    (sourceRest 374).take 27 = headerChars := by rfl

theorem header_original_split : sourceRest 374 = headerChars ++ sourceRest 401 := by
  calc
    sourceRest 374 = (sourceRest 374).take 27 ++ (sourceRest 374).drop 27 :=
      (List.take_append_drop 27 (sourceRest 374)).symm
    _ = headerChars ++ (sourceRest 374).drop 27 :=
      congrArg (fun part => part ++ (sourceRest 374).drop 27) header_original_prefix
    _ = headerChars ++ sourceRest 401 :=
      congrArg (fun tail => headerChars ++ tail) (sourceRest_drop 374 27)

theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + 195) (SourceJson.white (sourceRest 374)) Metadata05.metadataAcc =
      (SourceJson.value (fuel + 194) (sourceRest 401)).bind (afterValue (fuel + 194)) :=
  (congrArg (fun chars => SourceJson.object (fuel + 195) (SourceJson.white chars) Metadata05.metadataAcc)
    header_original_split).trans (object_header fuel (sourceRest 401))

theorem sourceChars_pending_value :
    SourceJson.value 335850 sourceChars =
      (SourceJson.value 335843 (sourceRest 401)).bind (afterValue 335843) :=
  Metadata05.sourceChars_through_metadata.trans (object_original_header 335649)

#print axioms object_header
#print axioms header_original_prefix
#print axioms header_original_split
#print axioms object_original_header
#print axioms sourceChars_pending_value

end Active8EnumerationField

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
