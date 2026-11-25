import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock005

/-! Original moment records block 6. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk024Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '7', '8', '2', '2', '5', '0', '7', '5', '8', '4', '5', '7', '0', '2', '8', '1', '9', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '3', '4', '9', '5', '6', '9', '0', '8', '3', '1', '2', '7', '5', '8', '0', '7', '7', '7', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '8', '1', '0', '3', '9', '2', '7', '8', '0', '7', '5', '0', '9', '2', '0', '8', '5', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '2', '9', '5', '4', '7', '8', '1', '8', '3', '1', '7', '3', '9', '3', '9', '5', '9', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '8', '4', '2', '4', '1', '8', '4', '5', '1', '0', '3', '7', '8', '3', '2', '8', '2', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '0', '5', '1', '3', '0', '1', '9', '1', '0', '6', '4', '0', '9', '1', '7', '7', '9', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '1', '6', '0', '6', '7', '4', '3', '2', '9', '5', '3', '0', '5', '0', '6', '0', '6', '3', '4', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '1', '1', '3', '6', '7', '9', '5', '5', '4', '4', '1', '1', '2', '2', '4', '3', '0', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '1', '2', '1', '8', '1', '9', '4', '3', '3', '8', '5', '1', '0', '3', '8', '2', '2', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '9', '3', '9', '7', '2', '9', '2', '8', '3', '6', '4', '8', '4', '2', '0', '9', '7', '1', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '1', '6', '2', '3', '6', '7', '0', '1', '2', '8', '8', '7', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '2', '5', '3', '6', '3', '7', '2', '3', '0', '5', '6', '2', '7', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk024Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['2', '4'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '2', '7', '8', '2', '2', '5', '0', '7', '5', '8', '4', '5', '7', '0', '2', '8', '1', '9', '6', '9']), .str (String.ofList ['1', '4', '1', '3', '4', '9', '5', '6', '9', '0', '8', '3', '1', '2', '7', '5', '8', '0', '7', '7', '7', '9']), .str (String.ofList ['2', '6', '8', '1', '0', '3', '9', '2', '7', '8', '0', '7', '5', '0', '9', '2', '0', '8', '5', '4', '5']), .str (String.ofList ['3', '7', '2', '9', '5', '4', '7', '8', '1', '8', '3', '1', '7', '3', '9', '3', '9', '5', '9', '3', '0']), .str (String.ofList ['7', '6', '8', '4', '2', '4', '1', '8', '4', '5', '1', '0', '3', '7', '8', '3', '2', '8', '2', '2', '7']), .str (String.ofList ['1', '8', '3', '0', '5', '1', '3', '0', '1', '9', '1', '0', '6', '4', '0', '9', '1', '7', '7', '9', '6', '3']), .str (String.ofList ['2', '1', '1', '6', '0', '6', '7', '4', '3', '2', '9', '5', '3', '0', '5', '0', '6', '0', '6', '3', '4', '0']), .str (String.ofList ['1', '0', '3', '1', '1', '3', '6', '7', '9', '5', '5', '4', '4', '1', '1', '2', '2', '4', '3', '0', '1', '6']), .str (String.ofList ['1', '0', '3', '1', '2', '1', '8', '1', '9', '4', '3', '3', '8', '5', '1', '0', '3', '8', '2', '2', '2', '8']), .str (String.ofList ['6', '4', '9', '3', '9', '7', '2', '9', '2', '8', '3', '6', '4', '8', '4', '2', '0', '9', '7', '1', '0'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '1', '6', '2', '3', '6', '7', '0', '1', '2', '8', '8', '7', '4', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '2', '5', '3', '6', '3', '7', '2', '3', '0', '5', '6', '2', '7', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_024_before_generic"
  err.flush

theorem array_moment_records_chunk_024 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 157)
      (SourceJson.white (momentRecordsChunk024Chars ++ tail)) acc =
      SourceJson.array (fuel + 156) (SourceJson.white tail) (momentRecordsChunk024Push acc) := by rfl

noncomputable def momentRecordsAcc025 : List SourceJson := momentRecordsChunk024Push momentRecordsAcc024

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_024_generic_complete"
  err.flush

noncomputable def momentRecordsChunk025Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '5', '9', '5', '7', '7', '2', '1', '5', '6', '6', '6', '1', '7', '1', '1', '2', '3', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '5', '6', '4', '1', '3', '6', '0', '3', '0', '3', '4', '4', '3', '5', '6', '8', '9', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '5', '4', '6', '2', '9', '8', '0', '2', '6', '3', '5', '4', '9', '5', '5', '9', '2', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '0', '8', '2', '6', '3', '7', '3', '1', '2', '1', '8', '1', '3', '4', '6', '3', '7', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '5', '6', '8', '2', '9', '9', '3', '4', '1', '3', '7', '4', '2', '6', '7', '0', '9', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '4', '0', '4', '0', '3', '7', '1', '8', '6', '4', '8', '3', '9', '0', '1', '5', '2', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '0', '4', '5', '4', '2', '9', '5', '7', '6', '0', '7', '2', '1', '5', '4', '6', '1', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '6', '0', '8', '8', '9', '1', '1', '1', '0', '5', '5', '7', '2', '0', '5', '4', '2', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '6', '1', '3', '6', '4', '6', '6', '0', '3', '4', '5', '9', '8', '7', '1', '5', '8', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '3', '9', '9', '8', '6', '1', '8', '4', '5', '8', '0', '9', '2', '7', '4', '9', '7', '2', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '7', '2', '6', '6', '7', '8', '1', '0', '3', '9', '6', '1', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '8', '0', '0', '1', '4', '0', '3', '5', '2', '5', '3', '6', '1', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk025Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['2', '5'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '4', '5', '5', '9', '5', '7', '7', '2', '1', '5', '6', '6', '6', '1', '7', '1', '1', '2', '3', '8', '3']), .str (String.ofList ['1', '5', '9', '5', '6', '4', '1', '3', '6', '0', '3', '0', '3', '4', '4', '3', '5', '6', '8', '9', '4', '6']), .str (String.ofList ['2', '4', '5', '4', '6', '2', '9', '8', '0', '2', '6', '3', '5', '4', '9', '5', '5', '9', '2', '1', '0']), .str (String.ofList ['3', '4', '0', '8', '2', '6', '3', '7', '3', '1', '2', '1', '8', '1', '3', '4', '6', '3', '7', '3', '6']), .str (String.ofList ['5', '7', '5', '6', '8', '2', '9', '9', '3', '4', '1', '3', '7', '4', '2', '6', '7', '0', '9', '1', '8']), .str (String.ofList ['1', '7', '0', '4', '0', '4', '0', '3', '7', '1', '8', '6', '4', '8', '3', '9', '0', '1', '5', '2', '8', '0']), .str (String.ofList ['1', '3', '4', '0', '4', '5', '4', '2', '9', '5', '7', '6', '0', '7', '2', '1', '5', '4', '6', '1', '7', '2']), .str (String.ofList ['9', '1', '6', '0', '8', '8', '9', '1', '1', '1', '0', '5', '5', '7', '2', '0', '5', '4', '2', '1', '0']), .str (String.ofList ['9', '1', '6', '1', '3', '6', '4', '6', '6', '0', '3', '4', '5', '9', '8', '7', '1', '5', '8', '6', '0']), .str (String.ofList ['1', '0', '4', '3', '9', '9', '8', '6', '1', '8', '4', '5', '8', '0', '9', '2', '7', '4', '9', '7', '2', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '7', '2', '6', '6', '7', '8', '1', '0', '3', '9', '6', '1', '7', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '8', '0', '0', '1', '4', '0', '3', '5', '2', '5', '3', '6', '1', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_025_before_generic"
  err.flush

theorem array_moment_records_chunk_025 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 156)
      (SourceJson.white (momentRecordsChunk025Chars ++ tail)) acc =
      SourceJson.array (fuel + 155) (SourceJson.white tail) (momentRecordsChunk025Push acc) := by rfl

noncomputable def momentRecordsAcc026 : List SourceJson := momentRecordsChunk025Push momentRecordsAcc025

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_025_generic_complete"
  err.flush

noncomputable def momentRecordsChunk026Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '7', '4', '8', '4', '3', '0', '9', '9', '1', '5', '8', '6', '7', '9', '0', '0', '4', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '6', '3', '9', '9', '4', '5', '8', '9', '0', '9', '7', '5', '7', '9', '0', '6', '4', '6', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '4', '4', '7', '6', '6', '7', '6', '0', '3', '9', '8', '2', '7', '3', '7', '4', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '2', '4', '6', '9', '7', '4', '6', '7', '5', '1', '3', '0', '0', '6', '6', '8', '3', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '7', '7', '2', '7', '4', '2', '1', '6', '8', '3', '9', '1', '7', '2', '6', '9', '6', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '8', '2', '5', '3', '3', '3', '7', '5', '3', '7', '7', '0', '8', '4', '7', '9', '1', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '6', '0', '5', '1', '1', '7', '6', '8', '1', '6', '2', '5', '8', '4', '0', '3', '0', '5', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '6', '4', '2', '6', '6', '0', '8', '7', '5', '6', '9', '2', '9', '2', '5', '1', '0', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '6', '4', '7', '3', '7', '8', '4', '2', '1', '3', '6', '8', '9', '6', '4', '2', '8', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '0', '0', '0', '4', '8', '7', '3', '3', '1', '3', '4', '8', '2', '6', '7', '3', '2', '7', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '8', '1', '6', '1', '5', '5', '2', '6', '9', '4', '0', '7', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '8', '4', '3', '3', '7', '3', '1', '5', '6', '6', '2', '2', '7', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk026Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['2', '6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '1', '4', '7', '4', '8', '4', '3', '0', '9', '9', '1', '5', '8', '6', '7', '9', '0', '0', '4', '7', '1']), .str (String.ofList ['1', '3', '6', '3', '9', '9', '4', '5', '8', '9', '0', '9', '7', '5', '7', '9', '0', '6', '4', '6', '1', '3']), .str (String.ofList ['2', '0', '8', '4', '4', '7', '6', '6', '7', '6', '0', '3', '9', '8', '2', '7', '3', '7', '4', '2', '6']), .str (String.ofList ['1', '6', '2', '4', '6', '9', '7', '4', '6', '7', '5', '1', '3', '0', '0', '6', '6', '8', '3', '0', '0']), .str (String.ofList ['4', '8', '7', '7', '2', '7', '4', '2', '1', '6', '8', '3', '9', '1', '7', '2', '6', '9', '6', '1', '2']), .str (String.ofList ['1', '1', '0', '8', '2', '5', '3', '3', '3', '7', '5', '3', '7', '7', '0', '8', '4', '7', '9', '1', '9', '8']), .str (String.ofList ['1', '3', '6', '0', '5', '1', '1', '7', '6', '8', '1', '6', '2', '5', '8', '4', '0', '3', '0', '5', '0', '8']), .str (String.ofList ['9', '0', '6', '4', '2', '6', '6', '0', '8', '7', '5', '6', '9', '2', '9', '2', '5', '1', '0', '9', '3']), .str (String.ofList ['9', '0', '6', '4', '7', '3', '7', '8', '4', '2', '1', '3', '6', '8', '9', '6', '4', '2', '8', '4', '2']), .str (String.ofList ['9', '4', '0', '0', '0', '4', '8', '7', '3', '3', '1', '3', '4', '8', '2', '6', '7', '3', '2', '7', '6'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '8', '1', '6', '1', '5', '5', '2', '6', '9', '4', '0', '7', '2', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '8', '4', '3', '3', '7', '3', '1', '5', '6', '6', '2', '2', '7', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_026_before_generic"
  err.flush

theorem array_moment_records_chunk_026 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 155)
      (SourceJson.white (momentRecordsChunk026Chars ++ tail)) acc =
      SourceJson.array (fuel + 154) (SourceJson.white tail) (momentRecordsChunk026Push acc) := by rfl

noncomputable def momentRecordsAcc027 : List SourceJson := momentRecordsChunk026Push momentRecordsAcc026

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_026_generic_complete"
  err.flush

noncomputable def momentRecordsChunk027Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '0', '5', '7', '2', '6', '7', '1', '7', '3', '7', '5', '7', '5', '6', '2', '4', '0', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '8', '8', '5', '4', '6', '6', '7', '8', '4', '0', '4', '1', '5', '3', '6', '3', '9', '0', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '5', '3', '8', '0', '5', '7', '5', '5', '1', '2', '1', '8', '4', '8', '9', '6', '6', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '2', '1', '7', '1', '3', '9', '5', '0', '6', '2', '7', '8', '0', '8', '4', '6', '4', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '2', '5', '4', '4', '4', '1', '4', '9', '8', '0', '4', '5', '5', '2', '4', '8', '7', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '5', '8', '8', '9', '7', '4', '7', '0', '3', '0', '8', '9', '9', '9', '9', '6', '5', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '4', '7', '9', '3', '2', '0', '8', '9', '6', '1', '8', '3', '8', '0', '2', '8', '5', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '3', '4', '4', '8', '7', '6', '5', '8', '9', '6', '5', '6', '1', '9', '0', '9', '0', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '3', '5', '0', '0', '6', '6', '3', '2', '2', '0', '1', '7', '4', '5', '6', '3', '6', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '1', '3', '8', '4', '4', '1', '6', '5', '9', '3', '2', '7', '1', '5', '4', '1', '0', '0', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '8', '5', '7', '0', '1', '0', '0', '8', '0', '1', '1', '5', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '0', '5', '0', '1', '6', '9', '1', '0', '2', '2', '2', '0', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk027Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['2', '7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '4', '6', '0', '5', '7', '2', '6', '7', '1', '7', '3', '7', '5', '7', '5', '6', '2', '4', '0', '5', '6']), .str (String.ofList ['1', '5', '9', '8', '8', '5', '4', '6', '6', '7', '8', '4', '0', '4', '1', '5', '3', '6', '3', '9', '0', '3']), .str (String.ofList ['2', '5', '5', '3', '8', '0', '5', '7', '5', '5', '1', '2', '1', '8', '4', '8', '9', '6', '6', '4', '5']), .str (String.ofList ['3', '6', '2', '1', '7', '1', '3', '9', '5', '0', '6', '2', '7', '8', '0', '8', '4', '6', '4', '5', '5']), .str (String.ofList ['5', '1', '2', '5', '4', '4', '4', '1', '4', '9', '8', '0', '4', '5', '5', '2', '4', '8', '7', '5', '3']), .str (String.ofList ['1', '6', '4', '5', '8', '8', '9', '7', '4', '7', '0', '3', '0', '8', '9', '9', '9', '9', '6', '5', '0', '8']), .str (String.ofList ['1', '0', '4', '4', '7', '9', '3', '2', '0', '8', '9', '6', '1', '8', '3', '8', '0', '2', '8', '5', '7', '5']), .str (String.ofList ['9', '7', '3', '4', '4', '8', '7', '6', '5', '8', '9', '6', '5', '6', '1', '9', '0', '9', '0', '1', '9']), .str (String.ofList ['9', '7', '3', '5', '0', '0', '6', '6', '3', '2', '2', '0', '1', '7', '4', '5', '6', '3', '6', '0', '1']), .str (String.ofList ['1', '0', '4', '1', '3', '8', '4', '4', '1', '6', '5', '9', '3', '2', '7', '1', '5', '4', '1', '0', '0', '2'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '8', '5', '7', '0', '1', '0', '0', '8', '0', '1', '1', '5', '6', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '9', '0', '5', '0', '1', '6', '9', '1', '0', '2', '2', '2', '0', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_027_before_generic"
  err.flush

theorem array_moment_records_chunk_027 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 154)
      (SourceJson.white (momentRecordsChunk027Chars ++ tail)) acc =
      SourceJson.array (fuel + 153) (SourceJson.white tail) (momentRecordsChunk027Push acc) := by rfl

noncomputable def momentRecordsAcc028 : List SourceJson := momentRecordsChunk027Push momentRecordsAcc027

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_027_generic_complete"
  err.flush

noncomputable def momentRecordsBlock006Chars : List Char := momentRecordsChunk024Chars ++ momentRecordsChunk025Chars ++ momentRecordsChunk026Chars ++ momentRecordsChunk027Chars
noncomputable def momentRecordsBlock006Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk027Push (momentRecordsChunk026Push (momentRecordsChunk025Push (momentRecordsChunk024Push (acc))))

theorem array_moment_records_block_006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 157)
      (SourceJson.white (momentRecordsBlock006Chars ++ tail)) acc =
      SourceJson.array (fuel + 153) (SourceJson.white tail) (momentRecordsBlock006Push acc) := by
  have hinput : momentRecordsBlock006Chars ++ tail = momentRecordsChunk024Chars ++ (momentRecordsChunk025Chars ++ (momentRecordsChunk026Chars ++ (momentRecordsChunk027Chars ++ (tail)))) := by
    simp only [momentRecordsBlock006Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 157) (SourceJson.white (momentRecordsBlock006Chars ++ tail)) acc =
        SourceJson.array (fuel + 157) (SourceJson.white (momentRecordsChunk024Chars ++ (momentRecordsChunk025Chars ++ (momentRecordsChunk026Chars ++ (momentRecordsChunk027Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 157) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 156) (SourceJson.white (momentRecordsChunk025Chars ++ (momentRecordsChunk026Chars ++ (momentRecordsChunk027Chars ++ (tail))))) (momentRecordsChunk024Push (acc)) := array_moment_records_chunk_024 fuel (momentRecordsChunk025Chars ++ (momentRecordsChunk026Chars ++ (momentRecordsChunk027Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 155) (SourceJson.white (momentRecordsChunk026Chars ++ (momentRecordsChunk027Chars ++ (tail)))) (momentRecordsChunk025Push (momentRecordsChunk024Push (acc))) := array_moment_records_chunk_025 fuel (momentRecordsChunk026Chars ++ (momentRecordsChunk027Chars ++ (tail))) (momentRecordsChunk024Push (acc))
    _ = SourceJson.array (fuel + 154) (SourceJson.white (momentRecordsChunk027Chars ++ (tail))) (momentRecordsChunk026Push (momentRecordsChunk025Push (momentRecordsChunk024Push (acc)))) := array_moment_records_chunk_026 fuel (momentRecordsChunk027Chars ++ (tail)) (momentRecordsChunk025Push (momentRecordsChunk024Push (acc)))
    _ = SourceJson.array (fuel + 153) (SourceJson.white tail) (momentRecordsBlock006Push acc) := array_moment_records_chunk_027 fuel (tail) (momentRecordsChunk026Push (momentRecordsChunk025Push (momentRecordsChunk024Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_006_before_raw_binding"
  err.flush

theorem moment_records_block_006_prefix :
    (momentRest01 12889).take 2070 = momentRecordsBlock006Chars := by rfl

theorem moment_records_block_006_split :
    momentRest01 12889 = momentRecordsBlock006Chars ++ momentRest01 14959 := by
  calc
    momentRest01 12889 =
        (momentRest01 12889).take 2070 ++ (momentRest01 12889).drop 2070 :=
      (List.take_append_drop 2070 (momentRest01 12889)).symm
    _ = momentRecordsBlock006Chars ++ (momentRest01 12889).drop 2070 :=
      congrArg (fun p => p ++ (momentRest01 12889).drop 2070) moment_records_block_006_prefix
    _ = momentRecordsBlock006Chars ++ momentRest01 14959 :=
      congrArg (fun rest => momentRecordsBlock006Chars ++ rest) (momentRest01_drop 12889 2070)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_006_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_006 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 157)
      (SourceJson.white (momentRest01 12889)) acc =
      SourceJson.array (fuel + 153) (SourceJson.white (momentRest01 14959)) (momentRecordsBlock006Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 157) (SourceJson.white s) acc)
      moment_records_block_006_split).trans (array_moment_records_block_006 fuel (momentRest01 14959) acc)

theorem moment_records_through_block_006 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 153) (SourceJson.white (momentRest01 14959)) momentRecordsAcc028 := by
  exact (moment_records_through_block_005 fuel).trans (array_moment_records_original_block_006 fuel momentRecordsAcc024)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_006_complete"
  err.flush

#print axioms array_moment_records_chunk_024
#print axioms array_moment_records_chunk_025
#print axioms array_moment_records_chunk_026
#print axioms array_moment_records_chunk_027
#print axioms array_moment_records_block_006
#print axioms moment_records_block_006_prefix
#print axioms moment_records_block_006_split
#print axioms array_moment_records_original_block_006
#print axioms moment_records_through_block_006

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
