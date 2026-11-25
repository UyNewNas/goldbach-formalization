import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock028

/-! Original moment records block 29. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk116Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '6', '8', '2', '1', '4', '1', '0', '8', '0', '8', '5', '8', '8', '3', '9', '2', '0', '9', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '4', '4', '7', '2', '0', '0', '2', '0', '1', '4', '1', '1', '3', '9', '7', '7', '1', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '9', '9', '2', '1', '4', '5', '5', '4', '6', '1', '9', '4', '8', '8', '5', '0', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '5', '8', '4', '6', '5', '3', '6', '7', '5', '0', '4', '9', '0', '3', '3', '4', '1', '0', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '8', '6', '9', '8', '1', '3', '4', '5', '3', '7', '6', '3', '4', '9', '9', '8', '9', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '7', '6', '4', '8', '0', '4', '6', '3', '5', '2', '8', '7', '2', '3', '3', '6', '3', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '5', '2', '8', '0', '3', '8', '2', '5', '5', '5', '8', '4', '6', '4', '8', '6', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '5', '1', '3', '5', '2', '3', '5', '5', '5', '2', '2', '5', '0', '1', '7', '8', '3', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '3', '8', '1', '9', '9', '1', '9', '8', '8', '4', '5', '2', '2', '0', '5', '8', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '0', '2', '1', '9', '0', '5', '8', '5', '3', '8', '0', '0', '5', '6', '8', '8', '6', '8', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '7', '3', '9', '1', '2', '8', '5', '7', '0', '6', '7', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '9', '9', '5', '6', '6', '7', '1', '7', '7', '9', '7', '9', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk116Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '1', '6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '6', '8', '2', '1', '4', '1', '0', '8', '0', '8', '5', '8', '8', '3', '9', '2', '0', '9', '9', '2']), .str (String.ofList ['1', '3', '3', '4', '4', '7', '2', '0', '0', '2', '0', '1', '4', '1', '1', '3', '9', '7', '7', '1', '2', '7']), .str (String.ofList ['1', '3', '8', '9', '9', '2', '1', '4', '5', '5', '4', '6', '1', '9', '4', '8', '8', '5', '0', '6', '4']), .str (String.ofList ['7', '4', '5', '8', '4', '6', '5', '3', '6', '7', '5', '0', '4', '9', '0', '3', '3', '4', '1', '0', '3']), .str (String.ofList ['7', '9', '8', '6', '9', '8', '1', '3', '4', '5', '3', '7', '6', '3', '4', '9', '9', '8', '9', '8', '7']), .str (String.ofList ['1', '3', '5', '7', '6', '4', '8', '0', '4', '6', '3', '5', '2', '8', '7', '2', '3', '3', '6', '3', '4', '6']), .str (String.ofList ['1', '1', '0', '9', '5', '2', '8', '0', '3', '8', '2', '5', '5', '5', '8', '4', '6', '4', '8', '6', '4', '9']), .str (String.ofList ['1', '0', '1', '5', '1', '3', '5', '2', '3', '5', '5', '5', '2', '2', '5', '0', '1', '7', '8', '3', '6', '5']), .str (String.ofList ['9', '5', '3', '3', '8', '1', '9', '9', '1', '9', '8', '8', '4', '5', '2', '2', '0', '5', '8', '2', '0']), .str (String.ofList ['9', '1', '0', '2', '1', '9', '0', '5', '8', '5', '3', '8', '0', '0', '5', '6', '8', '8', '6', '8', '0'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '1', '7', '3', '9', '1', '2', '8', '5', '7', '0', '6', '7', '1', '5'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '1', '9', '9', '5', '6', '6', '7', '1', '7', '7', '9', '7', '9', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_116_before_generic"
  err.flush

theorem array_moment_records_chunk_116 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 65)
      (SourceJson.white (momentRecordsChunk116Chars ++ tail)) acc =
      SourceJson.array (fuel + 64) (SourceJson.white tail) (momentRecordsChunk116Push acc) := by rfl

noncomputable def momentRecordsAcc117 : List SourceJson := momentRecordsChunk116Push momentRecordsAcc116

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_116_generic_complete"
  err.flush

noncomputable def momentRecordsChunk117Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '0', '7', '8', '3', '8', '0', '5', '8', '5', '4', '5', '7', '3', '2', '0', '8', '2', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '5', '7', '4', '4', '8', '7', '2', '8', '5', '7', '8', '5', '5', '8', '9', '8', '7', '9', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '5', '0', '2', '0', '7', '9', '1', '9', '9', '8', '0', '1', '4', '4', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '5', '9', '8', '3', '0', '2', '4', '9', '2', '5', '6', '7', '2', '0', '9', '5', '0', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '6', '9', '4', '4', '8', '0', '1', '4', '0', '3', '2', '2', '8', '9', '1', '0', '8', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '4', '6', '5', '7', '2', '1', '2', '4', '5', '1', '8', '3', '1', '9', '5', '4', '5', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '4', '0', '2', '3', '8', '3', '1', '3', '9', '0', '7', '1', '2', '3', '0', '4', '4', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '0', '4', '6', '6', '1', '1', '4', '2', '8', '3', '1', '8', '2', '0', '9', '6', '3', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '0', '4', '6', '1', '0', '7', '1', '8', '6', '1', '4', '0', '9', '4', '4', '7', '6', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '8', '6', '5', '0', '4', '8', '9', '5', '4', '7', '2', '7', '2', '3', '4', '7', '1', '8', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '3', '2', '5', '7', '2', '5', '4', '8', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '5', '9', '4', '5', '3', '4', '6', '1', '5', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk117Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '1', '7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '2', '0', '7', '8', '3', '8', '0', '5', '8', '5', '4', '5', '7', '3', '2', '0', '8', '2', '0', '7']), .str (String.ofList ['1', '2', '8', '5', '7', '4', '4', '8', '7', '2', '8', '5', '7', '8', '5', '5', '8', '9', '8', '7', '9', '9']), .str (String.ofList ['1', '4', '4', '5', '0', '2', '0', '7', '9', '1', '9', '9', '8', '0', '1', '4', '4', '8', '7', '5', '0']), .str (String.ofList ['7', '1', '5', '9', '8', '3', '0', '2', '4', '9', '2', '5', '6', '7', '2', '0', '9', '5', '0', '3', '6']), .str (String.ofList ['8', '0', '6', '9', '4', '4', '8', '0', '1', '4', '0', '3', '2', '2', '8', '9', '1', '0', '8', '8', '6']), .str (String.ofList ['1', '4', '2', '4', '6', '5', '7', '2', '1', '2', '4', '5', '1', '8', '3', '1', '9', '5', '4', '5', '7', '5']), .str (String.ofList ['1', '1', '5', '4', '0', '2', '3', '8', '3', '1', '3', '9', '0', '7', '1', '2', '3', '0', '4', '4', '3', '0']), .str (String.ofList ['9', '5', '0', '4', '6', '6', '1', '1', '4', '2', '8', '3', '1', '8', '2', '0', '9', '6', '3', '1', '8']), .str (String.ofList ['9', '5', '0', '4', '6', '1', '0', '7', '1', '8', '6', '1', '4', '0', '9', '4', '4', '7', '6', '9', '5']), .str (String.ofList ['9', '5', '8', '6', '5', '0', '4', '8', '9', '5', '4', '7', '2', '7', '2', '3', '4', '7', '1', '8', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '3', '3', '2', '5', '7', '2', '5', '4', '8', '4', '5'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '3', '5', '9', '4', '5', '3', '4', '6', '1', '5', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_117_before_generic"
  err.flush

theorem array_moment_records_chunk_117 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 64)
      (SourceJson.white (momentRecordsChunk117Chars ++ tail)) acc =
      SourceJson.array (fuel + 63) (SourceJson.white tail) (momentRecordsChunk117Push acc) := by rfl

noncomputable def momentRecordsAcc118 : List SourceJson := momentRecordsChunk117Push momentRecordsAcc117

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_117_generic_complete"
  err.flush

noncomputable def momentRecordsChunk118Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '0', '2', '9', '3', '1', '2', '6', '7', '4', '9', '0', '4', '4', '3', '9', '5', '2', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '0', '2', '1', '8', '0', '0', '4', '9', '7', '2', '4', '2', '6', '0', '2', '3', '5', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '5', '0', '2', '6', '3', '3', '9', '6', '9', '7', '0', '3', '6', '2', '1', '5', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '9', '4', '4', '5', '1', '0', '1', '4', '6', '4', '1', '8', '1', '5', '6', '6', '1', '5', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '1', '7', '2', '7', '0', '1', '8', '0', '7', '8', '5', '0', '4', '2', '1', '0', '0', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '2', '5', '5', '7', '9', '8', '3', '8', '5', '7', '5', '5', '7', '4', '1', '1', '4', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '6', '1', '3', '8', '0', '2', '0', '1', '6', '5', '2', '9', '4', '5', '0', '9', '0', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '4', '4', '2', '2', '1', '1', '9', '9', '5', '4', '2', '4', '1', '0', '5', '5', '9', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '5', '8', '7', '5', '3', '5', '8', '6', '9', '0', '5', '7', '8', '4', '8', '7', '1', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '5', '9', '6', '1', '3', '6', '7', '1', '4', '4', '1', '4', '1', '5', '4', '4', '1', '4', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '2', '9', '9', '9', '5', '5', '9', '6', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '3', '4', '3', '0', '8', '1', '3', '3', '9', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk118Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '1', '8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '8', '0', '2', '9', '3', '1', '2', '6', '7', '4', '9', '0', '4', '4', '3', '9', '5', '2', '6', '2']), .str (String.ofList ['1', '3', '5', '0', '2', '1', '8', '0', '0', '4', '9', '7', '2', '4', '2', '6', '0', '2', '3', '5', '7', '8']), .str (String.ofList ['1', '3', '0', '5', '0', '2', '6', '3', '3', '9', '6', '9', '7', '0', '3', '6', '2', '1', '5', '2', '5']), .str (String.ofList ['7', '3', '9', '4', '4', '5', '1', '0', '1', '4', '6', '4', '1', '8', '1', '5', '6', '6', '1', '5', '8']), .str (String.ofList ['8', '2', '1', '7', '2', '7', '0', '1', '8', '0', '7', '8', '5', '0', '4', '2', '1', '0', '0', '6', '9']), .str (String.ofList ['1', '3', '4', '2', '5', '5', '7', '9', '8', '3', '8', '5', '7', '5', '5', '7', '4', '1', '1', '4', '5', '1']), .str (String.ofList ['1', '1', '1', '6', '1', '3', '8', '0', '2', '0', '1', '6', '5', '2', '9', '4', '5', '0', '9', '0', '4', '2']), .str (String.ofList ['1', '0', '2', '4', '4', '2', '2', '1', '1', '9', '9', '5', '4', '2', '4', '1', '0', '5', '5', '9', '6', '5']), .str (String.ofList ['9', '4', '5', '8', '7', '5', '3', '5', '8', '6', '9', '0', '5', '7', '8', '4', '8', '7', '1', '8', '1']), .str (String.ofList ['9', '4', '5', '9', '6', '1', '3', '6', '7', '1', '4', '4', '1', '4', '1', '5', '4', '4', '1', '4', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '2', '9', '9', '9', '5', '5', '9', '6', '3', '6'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '3', '4', '3', '0', '8', '1', '3', '3', '9', '8']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_118_before_generic"
  err.flush

theorem array_moment_records_chunk_118 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 63)
      (SourceJson.white (momentRecordsChunk118Chars ++ tail)) acc =
      SourceJson.array (fuel + 62) (SourceJson.white tail) (momentRecordsChunk118Push acc) := by rfl

noncomputable def momentRecordsAcc119 : List SourceJson := momentRecordsChunk118Push momentRecordsAcc118

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_118_generic_complete"
  err.flush

noncomputable def momentRecordsChunk119Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '9', '9', '4', '9', '4', '4', '9', '1', '1', '2', '1', '5', '8', '2', '3', '4', '0', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '2', '8', '3', '4', '0', '4', '7', '8', '0', '9', '6', '1', '4', '8', '5', '1', '3', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '7', '2', '2', '3', '1', '1', '0', '6', '0', '8', '0', '8', '4', '8', '6', '8', '6', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '1', '7', '9', '2', '8', '3', '5', '1', '9', '6', '0', '7', '2', '2', '4', '4', '9', '4', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '2', '5', '9', '5', '3', '6', '0', '8', '3', '5', '8', '0', '7', '7', '3', '9', '4', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '8', '4', '7', '0', '9', '8', '3', '8', '3', '4', '7', '8', '9', '8', '9', '9', '5', '3', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '0', '3', '1', '9', '9', '3', '4', '2', '0', '5', '2', '6', '8', '9', '3', '2', '3', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '1', '2', '4', '2', '3', '2', '7', '7', '4', '7', '5', '6', '7', '1', '2', '9', '9', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '0', '4', '2', '7', '2', '6', '7', '8', '8', '9', '7', '0', '2', '9', '5', '0', '9', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '0', '4', '4', '0', '7', '1', '9', '0', '2', '2', '7', '7', '8', '5', '1', '6', '3', '0', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '3', '0', '0', '5', '9', '3', '1', '2', '5', '9', '4', '4', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '3', '5', '4', '9', '8', '4', '4', '1', '2', '9', '2', '1', '7', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk119Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '1', '9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '5', '9', '9', '4', '9', '4', '4', '9', '1', '1', '2', '1', '5', '8', '2', '3', '4', '0', '5', '1']), .str (String.ofList ['1', '4', '8', '2', '8', '3', '4', '0', '4', '7', '8', '0', '9', '6', '1', '4', '8', '5', '1', '3', '0', '0']), .str (String.ofList ['3', '2', '7', '2', '2', '3', '1', '1', '0', '6', '0', '8', '0', '8', '4', '8', '6', '8', '6', '4', '5']), .str (String.ofList ['4', '6', '1', '7', '9', '2', '8', '3', '5', '1', '9', '6', '0', '7', '2', '2', '4', '4', '9', '4', '4']), .str (String.ofList ['7', '3', '2', '5', '9', '5', '3', '6', '0', '8', '3', '5', '8', '0', '7', '7', '3', '9', '4', '7', '5']), .str (String.ofList ['2', '5', '8', '4', '7', '0', '9', '8', '3', '8', '3', '4', '7', '8', '9', '8', '9', '9', '5', '3', '4', '3']), .str (String.ofList ['1', '1', '3', '0', '3', '1', '9', '9', '3', '4', '2', '0', '5', '2', '6', '8', '9', '3', '2', '3', '3', '1']), .str (String.ofList ['7', '9', '1', '2', '4', '2', '3', '2', '7', '7', '4', '7', '5', '6', '7', '1', '2', '9', '9', '2', '0']), .str (String.ofList ['7', '6', '0', '4', '2', '7', '2', '6', '7', '8', '8', '9', '7', '0', '2', '9', '5', '0', '9', '8', '6']), .str (String.ofList ['7', '6', '0', '4', '4', '0', '7', '1', '9', '0', '2', '2', '7', '7', '8', '5', '1', '6', '3', '0', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '3', '0', '0', '5', '9', '3', '1', '2', '5', '9', '4', '4', '6', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '3', '5', '4', '9', '8', '4', '4', '1', '2', '9', '2', '1', '7', '0']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_119_before_generic"
  err.flush

theorem array_moment_records_chunk_119 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 62)
      (SourceJson.white (momentRecordsChunk119Chars ++ tail)) acc =
      SourceJson.array (fuel + 61) (SourceJson.white tail) (momentRecordsChunk119Push acc) := by rfl

noncomputable def momentRecordsAcc120 : List SourceJson := momentRecordsChunk119Push momentRecordsAcc119

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_119_generic_complete"
  err.flush

noncomputable def momentRecordsBlock029Chars : List Char := momentRecordsChunk116Chars ++ momentRecordsChunk117Chars ++ momentRecordsChunk118Chars ++ momentRecordsChunk119Chars
noncomputable def momentRecordsBlock029Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk119Push (momentRecordsChunk118Push (momentRecordsChunk117Push (momentRecordsChunk116Push (acc))))

theorem array_moment_records_block_029 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 65)
      (SourceJson.white (momentRecordsBlock029Chars ++ tail)) acc =
      SourceJson.array (fuel + 61) (SourceJson.white tail) (momentRecordsBlock029Push acc) := by
  have hinput : momentRecordsBlock029Chars ++ tail = momentRecordsChunk116Chars ++ (momentRecordsChunk117Chars ++ (momentRecordsChunk118Chars ++ (momentRecordsChunk119Chars ++ (tail)))) := by
    simp only [momentRecordsBlock029Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 65) (SourceJson.white (momentRecordsBlock029Chars ++ tail)) acc =
        SourceJson.array (fuel + 65) (SourceJson.white (momentRecordsChunk116Chars ++ (momentRecordsChunk117Chars ++ (momentRecordsChunk118Chars ++ (momentRecordsChunk119Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 65) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 64) (SourceJson.white (momentRecordsChunk117Chars ++ (momentRecordsChunk118Chars ++ (momentRecordsChunk119Chars ++ (tail))))) (momentRecordsChunk116Push (acc)) := array_moment_records_chunk_116 fuel (momentRecordsChunk117Chars ++ (momentRecordsChunk118Chars ++ (momentRecordsChunk119Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 63) (SourceJson.white (momentRecordsChunk118Chars ++ (momentRecordsChunk119Chars ++ (tail)))) (momentRecordsChunk117Push (momentRecordsChunk116Push (acc))) := array_moment_records_chunk_117 fuel (momentRecordsChunk118Chars ++ (momentRecordsChunk119Chars ++ (tail))) (momentRecordsChunk116Push (acc))
    _ = SourceJson.array (fuel + 62) (SourceJson.white (momentRecordsChunk119Chars ++ (tail))) (momentRecordsChunk118Push (momentRecordsChunk117Push (momentRecordsChunk116Push (acc)))) := array_moment_records_chunk_118 fuel (momentRecordsChunk119Chars ++ (tail)) (momentRecordsChunk117Push (momentRecordsChunk116Push (acc)))
    _ = SourceJson.array (fuel + 61) (SourceJson.white tail) (momentRecordsBlock029Push acc) := array_moment_records_chunk_119 fuel (tail) (momentRecordsChunk118Push (momentRecordsChunk117Push (momentRecordsChunk116Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_029_before_raw_binding"
  err.flush

theorem moment_records_block_029_prefix :
    (momentRest01 60672).take 2056 = momentRecordsBlock029Chars := by rfl

theorem moment_records_block_029_split :
    momentRest01 60672 = momentRecordsBlock029Chars ++ momentRest01 62728 := by
  calc
    momentRest01 60672 =
        (momentRest01 60672).take 2056 ++ (momentRest01 60672).drop 2056 :=
      (List.take_append_drop 2056 (momentRest01 60672)).symm
    _ = momentRecordsBlock029Chars ++ (momentRest01 60672).drop 2056 :=
      congrArg (fun p => p ++ (momentRest01 60672).drop 2056) moment_records_block_029_prefix
    _ = momentRecordsBlock029Chars ++ momentRest01 62728 :=
      congrArg (fun rest => momentRecordsBlock029Chars ++ rest) (momentRest01_drop 60672 2056)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_029_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_029 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 65)
      (SourceJson.white (momentRest01 60672)) acc =
      SourceJson.array (fuel + 61) (SourceJson.white (momentRest01 62728)) (momentRecordsBlock029Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 65) (SourceJson.white s) acc)
      moment_records_block_029_split).trans (array_moment_records_block_029 fuel (momentRest01 62728) acc)

theorem moment_records_through_block_029 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 61) (SourceJson.white (momentRest01 62728)) momentRecordsAcc120 := by
  exact (moment_records_through_block_028 fuel).trans (array_moment_records_original_block_029 fuel momentRecordsAcc116)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_029_complete"
  err.flush

#print axioms array_moment_records_chunk_116
#print axioms array_moment_records_chunk_117
#print axioms array_moment_records_chunk_118
#print axioms array_moment_records_chunk_119
#print axioms array_moment_records_block_029
#print axioms moment_records_block_029_prefix
#print axioms moment_records_block_029_split
#print axioms array_moment_records_original_block_029
#print axioms moment_records_through_block_029

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
