import ImbalancedChen.P2OriginalSaving19Geometry05ScalableFaceLedgerField

/-! Exact original object header; unchanged duplicate-key and error branches.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesField

noncomputable def headerChars : List Char := ['\r', '\n', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ']
noncomputable def fieldKey : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def afterValue (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fieldKey, result.1) :: FaceLedgerField.fieldAcc).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fieldKey, result.1) :: FaceLedgerField.fieldAcc)
  | _ => .error "object separator missing"

theorem object_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 475) (SourceJson.white (headerChars ++ rest)) FaceLedgerField.fieldAcc =
      (SourceJson.value (fuel + 474) rest).bind (afterValue (fuel + 474)) := by rfl

theorem header_original_prefix :
    (sourceRest 104479).take 17 = headerChars := by rfl

theorem header_original_split : sourceRest 104479 = headerChars ++ sourceRest 104496 := by
  calc
    sourceRest 104479 = (sourceRest 104479).take 17 ++ (sourceRest 104479).drop 17 :=
      (List.take_append_drop 17 (sourceRest 104479)).symm
    _ = headerChars ++ (sourceRest 104479).drop 17 :=
      congrArg (fun part => part ++ (sourceRest 104479).drop 17) header_original_prefix
    _ = headerChars ++ sourceRest 104496 :=
      congrArg (fun tail => headerChars ++ tail) (sourceRest_drop 104479 17)

theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + 475) (SourceJson.white (sourceRest 104479)) FaceLedgerField.fieldAcc =
      (SourceJson.value (fuel + 474) (sourceRest 104496)).bind (afterValue (fuel + 474)) :=
  (congrArg (fun chars => SourceJson.object (fuel + 475) (SourceJson.white chars) FaceLedgerField.fieldAcc)
    header_original_split).trans (object_header fuel (sourceRest 104496))

theorem sourceChars_pending_value :
    SourceJson.value 201043 sourceChars =
      (SourceJson.value 201030 (sourceRest 104496)).bind (afterValue 201030) :=
  FaceLedgerField.sourceChars_through_field.trans (object_original_header 200556)

#print axioms object_header
#print axioms header_original_prefix
#print axioms header_original_split
#print axioms object_original_header
#print axioms sourceChars_pending_value

end SimplicesField

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
