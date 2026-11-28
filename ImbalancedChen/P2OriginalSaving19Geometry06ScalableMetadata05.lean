import ImbalancedChen.P2OriginalSaving19Geometry06ScalableInput

/-! First 5 original fields grouped without dropping duplicate-key checks.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace Metadata05

noncomputable def metadataChars : List Char := ['{', '\r', '\n', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'j', 'a', 'c', 'o', 'b', 'i', 'a', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', '7', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', '"', 'p', 'o', 's', 'i', 't', 'i', 'v', 'e', '_', 'n', 'o', 'r', 'm', 'a', 'l', '_', 'b', 'a', 'l', 'a', 'n', 'c', 'e', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '5', '/', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '7', '/', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '8', '8', '/', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '/', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '4', '/', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '0', '/', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '2', '/', '7', '"', '\r', '\n', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', '"', 'n', 'o', 'r', 'm', 'a', 'l', '_', 'r', 'a', 'n', 'k', '"', ':', ' ', '8', ',']
noncomputable def metadataAcc : List (String × SourceJson) := [(String.ofList ['n', 'o', 'r', 'm', 'a', 'l', '_', 'r', 'a', 'n', 'k'], .number (String.ofList ['8'])), (String.ofList ['p', 'o', 's', 'i', 't', 'i', 'v', 'e', '_', 'n', 'o', 'r', 'm', 'a', 'l', '_', 'b', 'a', 'l', 'a', 'n', 'c', 'e'], .arr [.str (String.ofList ['1']), .str (String.ofList ['1']), .str (String.ofList ['2', '5', '/', '1', '4']), .str (String.ofList ['1', '7', '/', '1', '4']), .str (String.ofList ['1']), .str (String.ofList ['8', '8', '/', '2', '1']), .str (String.ofList ['1', '2', '1', '/', '8', '4']), .str (String.ofList ['4', '/', '7']), .str (String.ofList ['1', '0', '/', '2', '1']), .str (String.ofList ['1', '/', '7']), .str (String.ofList ['2', '2', '/', '7'])]), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '7']), .number (String.ofList ['8', '2'])]), (String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'j', 'a', 'c', 'o', 'b', 'i', 'a', 'n'], .number (String.ofList ['1'])), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['8']))]

theorem value_metadata (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 29) (metadataChars ++ tail) =
      SourceJson.object (fuel + 23) (SourceJson.white tail) metadataAcc := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED metadata_before_packed_binding"
  err.flush

theorem metadata_original_prefix :
    (sourceRest 0).take 374 = metadataChars := by rfl

theorem metadata_original_split : sourceRest 0 = metadataChars ++ sourceRest 374 := by
  calc
    sourceRest 0 = (sourceRest 0).take 374 ++ (sourceRest 0).drop 374 :=
      (List.take_append_drop 374 (sourceRest 0)).symm
    _ = metadataChars ++ (sourceRest 0).drop 374 :=
      congrArg (fun part => part ++ (sourceRest 0).drop 374) metadata_original_prefix
    _ = metadataChars ++ sourceRest 374 :=
      congrArg (fun tail => metadataChars ++ tail) (sourceRest_drop 0 374)

theorem sourceChars_metadata_split : sourceChars = metadataChars ++ sourceRest 374 :=
  sourceRest_zero.symm.trans metadata_original_split

theorem sourceChars_through_metadata :
    SourceJson.value 335850 sourceChars =
      SourceJson.object 335844 (SourceJson.white (sourceRest 374)) metadataAcc :=
  (congrArg (SourceJson.value 335850) sourceChars_metadata_split).trans
    (value_metadata 335821 (sourceRest 374))

#print axioms value_metadata
#print axioms metadata_original_prefix
#print axioms metadata_original_split
#print axioms sourceChars_metadata_split
#print axioms sourceChars_through_metadata

end Metadata05

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
