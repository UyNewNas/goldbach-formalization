import ImbalancedChen.P2OriginalSaving19Geometry05ScalableInput

/-! First 5 original fields grouped without dropping duplicate-key checks.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace Metadata05

noncomputable def metadataChars : List Char := ['{', '\r', '\n', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'j', 'a', 'c', 'o', 'b', 'i', 'a', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', '7', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', '"', 'p', 'o', 's', 'i', 't', 'i', 'v', 'e', '_', 'n', 'o', 'r', 'm', 'a', 'l', '_', 'b', 'a', 'l', 'a', 'n', 'c', 'e', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '5', '2', '/', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '/', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '9', '/', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '/', '3', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '/', '9', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '1', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '4', '1', '7', '/', '3', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '3', '8', '/', '3', '0', '5', '"', '\r', '\n', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', '"', 'n', 'o', 'r', 'm', 'a', 'l', '_', 'r', 'a', 'n', 'k', '"', ':', ' ', '8', ',']
noncomputable def metadataAcc : List (String × SourceJson) := [(String.ofList ['n', 'o', 'r', 'm', 'a', 'l', '_', 'r', 'a', 'n', 'k'], .number (String.ofList ['8'])), (String.ofList ['p', 'o', 's', 'i', 't', 'i', 'v', 'e', '_', 'n', 'o', 'r', 'm', 'a', 'l', '_', 'b', 'a', 'l', 'a', 'n', 'c', 'e'], .arr [.str (String.ofList ['1']), .str (String.ofList ['5', '2', '/', '6', '1']), .str (String.ofList ['1']), .str (String.ofList ['2', '8', '5', '/', '6', '1']), .str (String.ofList ['1']), .str (String.ofList ['9', '/', '6', '1']), .str (String.ofList ['1', '2', '8', '/', '3', '0', '5']), .str (String.ofList ['2', '4', '8', '/', '9', '1', '5']), .str (String.ofList ['1', '1', '/', '1', '8', '3']), .str (String.ofList ['4', '1', '7', '/', '3', '0', '5']), .str (String.ofList ['3', '3', '8', '/', '3', '0', '5'])]), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['7', '7']), .number (String.ofList ['8', '2'])]), (String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'j', 'a', 'c', 'o', 'b', 'i', 'a', 'n'], .number (String.ofList ['1'])), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['8']))]

theorem value_metadata (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 29) (metadataChars ++ tail) =
      SourceJson.object (fuel + 23) (SourceJson.white tail) metadataAcc := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED metadata_before_packed_binding"
  err.flush

theorem metadata_original_prefix :
    (sourceRest 0).take 389 = metadataChars := by rfl

theorem metadata_original_split : sourceRest 0 = metadataChars ++ sourceRest 389 := by
  calc
    sourceRest 0 = (sourceRest 0).take 389 ++ (sourceRest 0).drop 389 :=
      (List.take_append_drop 389 (sourceRest 0)).symm
    _ = metadataChars ++ (sourceRest 0).drop 389 :=
      congrArg (fun part => part ++ (sourceRest 0).drop 389) metadata_original_prefix
    _ = metadataChars ++ sourceRest 389 :=
      congrArg (fun tail => metadataChars ++ tail) (sourceRest_drop 0 389)

theorem sourceChars_metadata_split : sourceChars = metadataChars ++ sourceRest 389 :=
  sourceRest_zero.symm.trans metadata_original_split

theorem sourceChars_through_metadata :
    SourceJson.value 201043 sourceChars =
      SourceJson.object 201037 (SourceJson.white (sourceRest 389)) metadataAcc :=
  (congrArg (SourceJson.value 201043) sourceChars_metadata_split).trans
    (value_metadata 201014 (sourceRest 389))

#print axioms value_metadata
#print axioms metadata_original_prefix
#print axioms metadata_original_split
#print axioms sourceChars_metadata_split
#print axioms sourceChars_through_metadata

end Metadata05

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
