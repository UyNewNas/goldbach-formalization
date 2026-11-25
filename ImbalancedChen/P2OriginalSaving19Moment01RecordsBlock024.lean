import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock023

/-! Original moment records block 24. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk096Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '1', '5', '9', '5', '2', '2', '8', '5', '9', '4', '1', '6', '0', '1', '5', '0', '5', '8', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '1', '6', '1', '3', '6', '1', '3', '2', '3', '1', '2', '2', '6', '0', '5', '7', '2', '4', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '0', '7', '8', '3', '5', '5', '2', '5', '9', '1', '9', '7', '1', '3', '4', '9', '7', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '9', '4', '6', '9', '6', '8', '9', '0', '8', '1', '7', '9', '8', '6', '4', '7', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '7', '5', '4', '7', '4', '0', '8', '8', '2', '2', '4', '7', '0', '3', '0', '2', '6', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '8', '9', '7', '1', '9', '0', '5', '6', '8', '7', '0', '8', '6', '6', '2', '1', '0', '1', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '0', '2', '1', '0', '4', '8', '1', '9', '3', '6', '8', '4', '4', '0', '8', '4', '6', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '4', '5', '5', '2', '1', '4', '5', '7', '1', '3', '7', '9', '6', '9', '5', '2', '5', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '1', '1', '0', '0', '9', '8', '0', '5', '5', '7', '6', '3', '3', '1', '5', '5', '7', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '7', '6', '5', '6', '1', '5', '4', '3', '3', '1', '0', '1', '7', '1', '0', '7', '0', '6', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '6', '4', '6', '7', '1', '0', '1', '4', '9', '6', '4', '8', '6', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '6', '9', '6', '8', '4', '6', '7', '7', '0', '1', '4', '3', '3', '7', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk096Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['9', '6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '9', '1', '5', '9', '5', '2', '2', '8', '5', '9', '4', '1', '6', '0', '1', '5', '0', '5', '8', '5', '1']), .str (String.ofList ['1', '8', '6', '1', '6', '1', '3', '6', '1', '3', '2', '3', '1', '2', '2', '6', '0', '5', '7', '2', '4', '7']), .str (String.ofList ['2', '2', '0', '7', '8', '3', '5', '5', '2', '5', '9', '1', '9', '7', '1', '3', '4', '9', '7', '0', '6']), .str (String.ofList ['7', '3', '4', '9', '4', '6', '9', '6', '8', '9', '0', '8', '1', '7', '9', '8', '6', '4', '7', '6', '0']), .str (String.ofList ['1', '1', '0', '7', '5', '4', '7', '4', '0', '8', '8', '2', '2', '4', '7', '0', '3', '0', '2', '6', '1', '5']), .str (String.ofList ['1', '8', '8', '9', '7', '1', '9', '0', '5', '6', '8', '7', '0', '8', '6', '6', '2', '1', '0', '1', '5', '0']), .str (String.ofList ['1', '4', '0', '0', '2', '1', '0', '4', '8', '1', '9', '3', '6', '8', '4', '4', '0', '8', '4', '6', '2', '5']), .str (String.ofList ['1', '2', '4', '4', '5', '5', '2', '1', '4', '5', '7', '1', '3', '7', '9', '6', '9', '5', '2', '5', '7', '4']), .str (String.ofList ['1', '1', '3', '1', '1', '0', '0', '9', '8', '0', '5', '5', '7', '6', '3', '3', '1', '5', '5', '7', '1', '5']), .str (String.ofList ['1', '4', '6', '7', '6', '5', '6', '1', '5', '4', '3', '3', '1', '0', '1', '7', '1', '0', '7', '0', '6', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '6', '4', '6', '7', '1', '0', '1', '4', '9', '6', '4', '8', '6', '8', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '6', '9', '6', '8', '4', '6', '7', '7', '0', '1', '4', '3', '3', '7', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_096_before_generic"
  err.flush

theorem array_moment_records_chunk_096 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 85)
      (SourceJson.white (momentRecordsChunk096Chars ++ tail)) acc =
      SourceJson.array (fuel + 84) (SourceJson.white tail) (momentRecordsChunk096Push acc) := by rfl

noncomputable def momentRecordsAcc097 : List SourceJson := momentRecordsChunk096Push momentRecordsAcc096

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_096_generic_complete"
  err.flush

noncomputable def momentRecordsChunk097Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '5', '4', '8', '1', '3', '8', '3', '5', '4', '0', '5', '6', '2', '0', '3', '7', '1', '8', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '6', '3', '9', '9', '9', '8', '0', '7', '2', '8', '6', '3', '3', '1', '4', '8', '2', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '5', '1', '2', '9', '2', '2', '8', '6', '1', '1', '2', '5', '5', '7', '9', '7', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '5', '0', '0', '1', '9', '4', '3', '0', '9', '1', '3', '0', '8', '0', '1', '2', '4', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '4', '6', '1', '9', '5', '6', '0', '3', '6', '8', '6', '5', '0', '1', '6', '4', '4', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '8', '9', '1', '7', '7', '5', '2', '7', '1', '4', '5', '0', '6', '0', '1', '3', '4', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '8', '9', '7', '3', '0', '6', '3', '0', '1', '8', '6', '1', '6', '4', '7', '4', '1', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '8', '0', '1', '7', '7', '2', '4', '8', '2', '2', '0', '7', '7', '3', '5', '1', '8', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '5', '4', '4', '3', '9', '7', '4', '4', '0', '0', '7', '1', '8', '0', '8', '8', '3', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '1', '2', '0', '7', '1', '7', '8', '9', '5', '2', '0', '0', '5', '8', '7', '4', '1', '0', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '5', '3', '5', '0', '5', '0', '1', '6', '9', '9', '8', '0', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '6', '9', '8', '4', '3', '2', '6', '4', '8', '4', '1', '4', '8', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk097Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['9', '7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '9', '5', '4', '8', '1', '3', '8', '3', '5', '4', '0', '5', '6', '2', '0', '3', '7', '1', '8', '6', '2']), .str (String.ofList ['1', '9', '0', '6', '3', '9', '9', '9', '8', '0', '7', '2', '8', '6', '3', '3', '1', '4', '8', '2', '4', '3']), .str (String.ofList ['2', '0', '4', '5', '1', '2', '9', '2', '2', '8', '6', '1', '1', '2', '5', '5', '7', '9', '7', '8', '0']), .str (String.ofList ['7', '8', '5', '0', '0', '1', '9', '4', '3', '0', '9', '1', '3', '0', '8', '0', '1', '2', '4', '8', '3']), .str (String.ofList ['1', '0', '2', '4', '6', '1', '9', '5', '6', '0', '3', '6', '8', '6', '5', '0', '1', '6', '4', '4', '7', '2']), .str (String.ofList ['1', '9', '0', '8', '9', '1', '7', '7', '5', '2', '7', '1', '4', '5', '0', '6', '0', '1', '3', '4', '6', '2']), .str (String.ofList ['1', '3', '7', '8', '9', '7', '3', '0', '6', '3', '0', '1', '8', '6', '1', '6', '4', '7', '4', '1', '7', '8']), .str (String.ofList ['1', '2', '4', '8', '0', '1', '7', '7', '2', '4', '8', '2', '2', '0', '7', '7', '3', '5', '1', '8', '3', '9']), .str (String.ofList ['1', '1', '5', '5', '4', '4', '3', '9', '7', '4', '4', '0', '0', '7', '1', '8', '0', '8', '8', '3', '3', '5']), .str (String.ofList ['1', '0', '8', '1', '2', '0', '7', '1', '7', '8', '9', '5', '2', '0', '0', '5', '8', '7', '4', '1', '0', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '5', '5', '3', '5', '0', '5', '0', '1', '6', '9', '9', '8', '0', '3', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '5', '6', '9', '8', '4', '3', '2', '6', '4', '8', '4', '1', '4', '8', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_097_before_generic"
  err.flush

theorem array_moment_records_chunk_097 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 84)
      (SourceJson.white (momentRecordsChunk097Chars ++ tail)) acc =
      SourceJson.array (fuel + 83) (SourceJson.white tail) (momentRecordsChunk097Push acc) := by rfl

noncomputable def momentRecordsAcc098 : List SourceJson := momentRecordsChunk097Push momentRecordsAcc097

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_097_generic_complete"
  err.flush

noncomputable def momentRecordsChunk098Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '1', '0', '5', '0', '2', '3', '9', '9', '4', '1', '1', '1', '1', '3', '0', '3', '4', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '1', '1', '5', '1', '0', '9', '3', '5', '4', '0', '8', '2', '1', '2', '7', '4', '7', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '9', '8', '9', '7', '9', '5', '0', '7', '1', '8', '6', '5', '4', '0', '3', '4', '1', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '4', '8', '3', '0', '5', '0', '0', '0', '7', '2', '7', '3', '5', '3', '6', '9', '7', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '5', '0', '4', '8', '7', '2', '5', '6', '6', '8', '3', '1', '4', '1', '9', '7', '9', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '0', '3', '8', '0', '4', '8', '8', '4', '2', '0', '3', '2', '7', '9', '3', '8', '7', '8', '7', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '7', '3', '4', '5', '1', '9', '3', '4', '4', '6', '5', '1', '1', '4', '7', '1', '2', '0', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '9', '4', '6', '5', '1', '0', '0', '7', '6', '9', '1', '5', '1', '2', '8', '1', '3', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '8', '8', '6', '5', '8', '8', '6', '1', '2', '0', '2', '6', '7', '7', '0', '9', '6', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '9', '6', '2', '2', '2', '1', '3', '8', '0', '0', '2', '5', '9', '4', '8', '8', '4', '9', '5', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '7', '3', '5', '5', '5', '0', '6', '4', '9', '9', '3', '9', '8', '1', '3', '9', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '8', '7', '4', '0', '2', '5', '1', '9', '1', '1', '2', '9', '9', '7', '0', '7', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk098Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['9', '8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '4', '6', '1', '0', '5', '0', '2', '3', '9', '9', '4', '1', '1', '1', '1', '3', '0', '3', '4', '3', '6']), .str (String.ofList ['1', '5', '4', '1', '1', '5', '1', '0', '9', '3', '5', '4', '0', '8', '2', '1', '2', '7', '4', '7', '0', '9']), .str (String.ofList ['2', '8', '9', '8', '9', '7', '9', '5', '0', '7', '1', '8', '6', '5', '4', '0', '3', '4', '1', '1', '0']), .str (String.ofList ['6', '3', '4', '8', '3', '0', '5', '0', '0', '0', '7', '2', '7', '3', '5', '3', '6', '9', '7', '9', '8']), .str (String.ofList ['1', '3', '7', '5', '0', '4', '8', '7', '2', '5', '6', '6', '8', '3', '1', '4', '1', '9', '7', '9', '7', '4']), .str (String.ofList ['2', '0', '0', '3', '8', '0', '4', '8', '8', '4', '2', '0', '3', '2', '7', '9', '3', '8', '7', '8', '7', '7']), .str (String.ofList ['1', '4', '7', '3', '4', '5', '1', '9', '3', '4', '4', '6', '5', '1', '1', '4', '7', '1', '2', '0', '8', '2']), .str (String.ofList ['1', '2', '0', '9', '4', '6', '5', '1', '0', '0', '7', '6', '9', '1', '5', '1', '2', '8', '1', '3', '1', '7']), .str (String.ofList ['1', '0', '8', '8', '8', '6', '5', '8', '8', '6', '1', '2', '0', '2', '6', '7', '7', '0', '9', '6', '2', '6']), .str (String.ofList ['1', '9', '9', '6', '2', '2', '2', '1', '3', '8', '0', '0', '2', '5', '9', '4', '8', '8', '4', '9', '5', '2'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '2', '7', '3', '5', '5', '5', '0', '6', '4', '9', '9', '3', '9', '8', '1', '3', '9', '9'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '2', '8', '7', '4', '0', '2', '5', '1', '9', '1', '1', '2', '9', '9', '7', '0', '7', '0']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_098_before_generic"
  err.flush

theorem array_moment_records_chunk_098 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 83)
      (SourceJson.white (momentRecordsChunk098Chars ++ tail)) acc =
      SourceJson.array (fuel + 82) (SourceJson.white tail) (momentRecordsChunk098Push acc) := by rfl

noncomputable def momentRecordsAcc099 : List SourceJson := momentRecordsChunk098Push momentRecordsAcc098

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_098_generic_complete"
  err.flush

noncomputable def momentRecordsChunk099Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '3', '1', '0', '5', '6', '9', '0', '1', '0', '7', '8', '4', '6', '7', '7', '5', '3', '4', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '3', '5', '5', '1', '8', '3', '0', '2', '4', '1', '0', '1', '1', '8', '8', '4', '2', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '1', '8', '7', '2', '8', '9', '8', '6', '6', '4', '3', '6', '1', '1', '1', '1', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '7', '5', '9', '9', '4', '3', '9', '5', '6', '0', '3', '6', '3', '0', '9', '9', '0', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '5', '1', '6', '8', '7', '6', '2', '5', '5', '7', '8', '6', '9', '1', '5', '4', '8', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '0', '4', '4', '6', '2', '3', '1', '7', '3', '4', '9', '4', '4', '7', '8', '1', '6', '3', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '1', '5', '5', '1', '2', '6', '6', '5', '3', '4', '6', '4', '1', '3', '7', '4', '5', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '1', '7', '1', '5', '8', '9', '7', '8', '1', '7', '3', '0', '5', '1', '0', '7', '1', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '3', '8', '8', '0', '1', '5', '9', '8', '0', '7', '9', '9', '5', '9', '7', '7', '4', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '4', '1', '1', '6', '6', '8', '0', '7', '6', '8', '0', '8', '8', '7', '1', '3', '4', '1', '3', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '9', '0', '4', '8', '6', '4', '0', '2', '8', '4', '9', '5', '3', '6', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '9', '4', '6', '9', '9', '7', '1', '9', '2', '3', '9', '7', '6', '4', '9', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk099Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['9', '9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '7', '3', '1', '0', '5', '6', '9', '0', '1', '0', '7', '8', '4', '6', '7', '7', '5', '3', '4', '9', '1']), .str (String.ofList ['1', '6', '7', '3', '5', '5', '1', '8', '3', '0', '2', '4', '1', '0', '1', '1', '8', '8', '4', '2', '3', '7']), .str (String.ofList ['2', '3', '4', '1', '8', '7', '2', '8', '9', '8', '6', '6', '4', '3', '6', '1', '1', '1', '1', '7', '2']), .str (String.ofList ['6', '9', '7', '5', '9', '9', '4', '3', '9', '5', '6', '0', '3', '6', '3', '0', '9', '9', '0', '1', '6']), .str (String.ofList ['1', '1', '0', '5', '1', '6', '8', '7', '6', '2', '5', '5', '7', '8', '6', '9', '1', '5', '4', '8', '8', '0']), .str (String.ofList ['2', '0', '0', '4', '4', '6', '2', '3', '1', '7', '3', '4', '9', '4', '4', '7', '8', '1', '6', '3', '3', '9']), .str (String.ofList ['1', '3', '4', '1', '5', '5', '1', '2', '6', '6', '5', '3', '4', '6', '4', '1', '3', '7', '4', '5', '3', '5']), .str (String.ofList ['1', '1', '6', '1', '7', '1', '5', '8', '9', '7', '8', '1', '7', '3', '0', '5', '1', '0', '7', '1', '1', '7']), .str (String.ofList ['1', '0', '8', '3', '8', '8', '0', '1', '5', '9', '8', '0', '7', '9', '9', '5', '9', '7', '7', '4', '1', '7']), .str (String.ofList ['1', '9', '4', '1', '1', '6', '6', '8', '0', '7', '6', '8', '0', '8', '8', '7', '1', '3', '4', '1', '3', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '9', '0', '4', '8', '6', '4', '0', '2', '8', '4', '9', '5', '3', '6', '8', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '9', '4', '6', '9', '9', '7', '1', '9', '2', '3', '9', '7', '6', '4', '9', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_099_before_generic"
  err.flush

theorem array_moment_records_chunk_099 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 82)
      (SourceJson.white (momentRecordsChunk099Chars ++ tail)) acc =
      SourceJson.array (fuel + 81) (SourceJson.white tail) (momentRecordsChunk099Push acc) := by rfl

noncomputable def momentRecordsAcc100 : List SourceJson := momentRecordsChunk099Push momentRecordsAcc099

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_099_generic_complete"
  err.flush

noncomputable def momentRecordsBlock024Chars : List Char := momentRecordsChunk096Chars ++ momentRecordsChunk097Chars ++ momentRecordsChunk098Chars ++ momentRecordsChunk099Chars
noncomputable def momentRecordsBlock024Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk099Push (momentRecordsChunk098Push (momentRecordsChunk097Push (momentRecordsChunk096Push (acc))))

theorem array_moment_records_block_024 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 85)
      (SourceJson.white (momentRecordsBlock024Chars ++ tail)) acc =
      SourceJson.array (fuel + 81) (SourceJson.white tail) (momentRecordsBlock024Push acc) := by
  have hinput : momentRecordsBlock024Chars ++ tail = momentRecordsChunk096Chars ++ (momentRecordsChunk097Chars ++ (momentRecordsChunk098Chars ++ (momentRecordsChunk099Chars ++ (tail)))) := by
    simp only [momentRecordsBlock024Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 85) (SourceJson.white (momentRecordsBlock024Chars ++ tail)) acc =
        SourceJson.array (fuel + 85) (SourceJson.white (momentRecordsChunk096Chars ++ (momentRecordsChunk097Chars ++ (momentRecordsChunk098Chars ++ (momentRecordsChunk099Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 85) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 84) (SourceJson.white (momentRecordsChunk097Chars ++ (momentRecordsChunk098Chars ++ (momentRecordsChunk099Chars ++ (tail))))) (momentRecordsChunk096Push (acc)) := array_moment_records_chunk_096 fuel (momentRecordsChunk097Chars ++ (momentRecordsChunk098Chars ++ (momentRecordsChunk099Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 83) (SourceJson.white (momentRecordsChunk098Chars ++ (momentRecordsChunk099Chars ++ (tail)))) (momentRecordsChunk097Push (momentRecordsChunk096Push (acc))) := array_moment_records_chunk_097 fuel (momentRecordsChunk098Chars ++ (momentRecordsChunk099Chars ++ (tail))) (momentRecordsChunk096Push (acc))
    _ = SourceJson.array (fuel + 82) (SourceJson.white (momentRecordsChunk099Chars ++ (tail))) (momentRecordsChunk098Push (momentRecordsChunk097Push (momentRecordsChunk096Push (acc)))) := array_moment_records_chunk_098 fuel (momentRecordsChunk099Chars ++ (tail)) (momentRecordsChunk097Push (momentRecordsChunk096Push (acc)))
    _ = SourceJson.array (fuel + 81) (SourceJson.white tail) (momentRecordsBlock024Push acc) := array_moment_records_chunk_099 fuel (tail) (momentRecordsChunk098Push (momentRecordsChunk097Push (momentRecordsChunk096Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_024_before_raw_binding"
  err.flush

theorem moment_records_block_024_prefix :
    (momentRest01 50292).take 2096 = momentRecordsBlock024Chars := by rfl

theorem moment_records_block_024_split :
    momentRest01 50292 = momentRecordsBlock024Chars ++ momentRest01 52388 := by
  calc
    momentRest01 50292 =
        (momentRest01 50292).take 2096 ++ (momentRest01 50292).drop 2096 :=
      (List.take_append_drop 2096 (momentRest01 50292)).symm
    _ = momentRecordsBlock024Chars ++ (momentRest01 50292).drop 2096 :=
      congrArg (fun p => p ++ (momentRest01 50292).drop 2096) moment_records_block_024_prefix
    _ = momentRecordsBlock024Chars ++ momentRest01 52388 :=
      congrArg (fun rest => momentRecordsBlock024Chars ++ rest) (momentRest01_drop 50292 2096)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_024_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_024 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 85)
      (SourceJson.white (momentRest01 50292)) acc =
      SourceJson.array (fuel + 81) (SourceJson.white (momentRest01 52388)) (momentRecordsBlock024Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 85) (SourceJson.white s) acc)
      moment_records_block_024_split).trans (array_moment_records_block_024 fuel (momentRest01 52388) acc)

theorem moment_records_through_block_024 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 81) (SourceJson.white (momentRest01 52388)) momentRecordsAcc100 := by
  exact (moment_records_through_block_023 fuel).trans (array_moment_records_original_block_024 fuel momentRecordsAcc096)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_024_complete"
  err.flush

#print axioms array_moment_records_chunk_096
#print axioms array_moment_records_chunk_097
#print axioms array_moment_records_chunk_098
#print axioms array_moment_records_chunk_099
#print axioms array_moment_records_block_024
#print axioms moment_records_block_024_prefix
#print axioms moment_records_block_024_split
#print axioms array_moment_records_original_block_024
#print axioms moment_records_through_block_024

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
