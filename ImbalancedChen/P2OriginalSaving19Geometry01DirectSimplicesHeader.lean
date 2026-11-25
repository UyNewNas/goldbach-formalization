import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerField

/-! Exact original object header; unchanged duplicate-key and error branches.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
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
    SourceJson.object (fuel + 606) (SourceJson.white (headerChars ++ rest)) FaceLedgerField.fieldAcc =
      (SourceJson.value (fuel + 605) rest).bind (afterValue (fuel + 605)) := by rfl

theorem header_original_prefix :
    (sourceRest 225545).take 17 = headerChars := by rfl

theorem header_original_split : sourceRest 225545 = headerChars ++ sourceRest 225562 := by
  calc
    sourceRest 225545 = (sourceRest 225545).take 17 ++ (sourceRest 225545).drop 17 :=
      (List.take_append_drop 17 (sourceRest 225545)).symm
    _ = headerChars ++ (sourceRest 225545).drop 17 :=
      congrArg (fun part => part ++ (sourceRest 225545).drop 17) header_original_prefix
    _ = headerChars ++ sourceRest 225562 :=
      congrArg (fun tail => headerChars ++ tail) (sourceRest_drop 225545 17)

theorem object_original_header (fuel : Nat) :
    SourceJson.object (fuel + 606) (SourceJson.white (sourceRest 225545)) FaceLedgerField.fieldAcc =
      (SourceJson.value (fuel + 605) (sourceRest 225562)).bind (afterValue (fuel + 605)) :=
  (congrArg (fun chars => SourceJson.object (fuel + 606) (SourceJson.white chars) FaceLedgerField.fieldAcc)
    header_original_split).trans (object_header fuel (sourceRest 225562))

theorem sourceChars_pending_value :
    SourceJson.value 470902 sourceChars =
      (SourceJson.value 470889 (sourceRest 225562)).bind (afterValue 470889) :=
  FaceLedgerField.sourceChars_through_field.trans (object_original_header 470284)

#print axioms object_header
#print axioms header_original_prefix
#print axioms header_original_split
#print axioms object_original_header
#print axioms sourceChars_pending_value

end SimplicesField

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
