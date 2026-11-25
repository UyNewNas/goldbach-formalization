import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock029

/-! Original moment records block 30. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk120Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '9', '4', '6', '0', '7', '6', '4', '6', '4', '8', '0', '4', '2', '5', '5', '5', '3', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '6', '9', '8', '9', '5', '2', '2', '6', '9', '2', '8', '0', '8', '3', '0', '7', '1', '5', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '7', '3', '7', '5', '5', '7', '3', '2', '2', '9', '7', '7', '9', '3', '8', '7', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '1', '6', '4', '6', '3', '9', '7', '4', '7', '5', '2', '3', '8', '0', '6', '7', '6', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '1', '5', '4', '4', '4', '1', '9', '4', '3', '2', '5', '5', '1', '9', '5', '6', '1', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '2', '8', '2', '8', '4', '7', '1', '9', '8', '8', '3', '7', '6', '6', '5', '5', '7', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '6', '6', '7', '0', '0', '5', '4', '2', '7', '9', '8', '4', '4', '3', '9', '2', '8', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '3', '0', '9', '9', '1', '9', '6', '0', '2', '1', '4', '1', '0', '0', '3', '7', '6', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '0', '4', '3', '7', '2', '8', '4', '0', '3', '2', '2', '2', '4', '5', '6', '9', '5', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '0', '4', '4', '7', '7', '6', '2', '4', '8', '1', '8', '4', '9', '7', '1', '2', '0', '0', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '1', '3', '4', '3', '1', '5', '2', '1', '8', '7', '3', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '3', '7', '5', '0', '2', '9', '5', '3', '7', '1', '4', '5', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk120Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '2', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '1', '2', '9', '4', '6', '0', '7', '6', '4', '6', '4', '8', '0', '4', '2', '5', '5', '5', '3', '3', '7']), .str (String.ofList ['1', '3', '0', '6', '9', '8', '9', '5', '2', '2', '6', '9', '2', '8', '0', '8', '3', '0', '7', '1', '5', '8']), .str (String.ofList ['2', '7', '7', '7', '3', '7', '5', '5', '7', '3', '2', '2', '9', '7', '7', '9', '3', '8', '7', '8', '8']), .str (String.ofList ['2', '6', '1', '6', '4', '6', '3', '9', '7', '4', '7', '5', '2', '3', '8', '0', '6', '7', '6', '1', '8']), .str (String.ofList ['6', '6', '1', '5', '4', '4', '4', '1', '9', '4', '3', '2', '5', '5', '1', '9', '5', '6', '1', '5', '5']), .str (String.ofList ['1', '8', '1', '2', '8', '2', '8', '4', '7', '1', '9', '8', '8', '3', '7', '6', '6', '5', '5', '7', '8', '1']), .str (String.ofList ['1', '1', '3', '6', '6', '7', '0', '0', '5', '4', '2', '7', '9', '8', '4', '4', '3', '9', '2', '8', '3', '6']), .str (String.ofList ['7', '8', '3', '0', '9', '9', '1', '9', '6', '0', '2', '1', '4', '1', '0', '0', '3', '7', '6', '9', '5']), .str (String.ofList ['6', '9', '0', '4', '3', '7', '2', '8', '4', '0', '3', '2', '2', '2', '4', '5', '6', '9', '5', '1', '3']), .str (String.ofList ['6', '9', '0', '4', '4', '7', '7', '6', '2', '4', '8', '1', '8', '4', '9', '7', '1', '2', '0', '0', '4'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '3', '1', '3', '4', '3', '1', '5', '2', '1', '8', '7', '3', '2', '6'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '3', '3', '7', '5', '0', '2', '9', '5', '3', '7', '1', '4', '5', '6']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_120_before_generic"
  err.flush

theorem array_moment_records_chunk_120 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 61)
      (SourceJson.white (momentRecordsChunk120Chars ++ tail)) acc =
      SourceJson.array (fuel + 60) (SourceJson.white tail) (momentRecordsChunk120Push acc) := by rfl

noncomputable def momentRecordsAcc121 : List SourceJson := momentRecordsChunk120Push momentRecordsAcc120

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_120_generic_complete"
  err.flush

noncomputable def momentRecordsChunk121Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '4', '2', '7', '1', '3', '6', '3', '0', '5', '1', '8', '0', '3', '6', '6', '5', '3', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '4', '9', '8', '0', '3', '0', '8', '1', '0', '5', '4', '1', '0', '7', '2', '4', '9', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '7', '3', '5', '7', '9', '5', '4', '3', '0', '2', '0', '6', '6', '4', '9', '6', '8', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '9', '8', '3', '9', '5', '7', '6', '7', '7', '5', '2', '8', '7', '2', '0', '0', '5', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '4', '7', '3', '6', '0', '5', '0', '5', '6', '2', '4', '8', '8', '9', '3', '2', '2', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '0', '5', '4', '3', '1', '9', '1', '9', '1', '1', '3', '0', '6', '6', '0', '5', '5', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '9', '5', '5', '4', '5', '1', '5', '0', '3', '3', '9', '9', '9', '5', '6', '0', '0', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '5', '1', '8', '9', '4', '8', '5', '5', '8', '0', '7', '9', '1', '5', '7', '7', '8', '7', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '1', '3', '1', '8', '5', '5', '2', '2', '0', '9', '7', '8', '9', '0', '5', '7', '3', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '1', '3', '3', '3', '4', '4', '0', '4', '4', '5', '1', '3', '2', '7', '0', '4', '8', '9', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '8', '5', '6', '4', '4', '0', '3', '5', '6', '3', '9', '4', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '8', '9', '7', '4', '7', '9', '1', '7', '8', '6', '6', '9', '0', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk121Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '2', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '4', '0', '4', '2', '7', '1', '3', '6', '3', '0', '5', '1', '8', '0', '3', '6', '6', '5', '3', '8', '4']), .str (String.ofList ['1', '5', '1', '4', '9', '8', '0', '3', '0', '8', '1', '0', '5', '4', '1', '0', '7', '2', '4', '9', '6', '0']), .str (String.ofList ['3', '3', '7', '3', '5', '7', '9', '5', '4', '3', '0', '2', '0', '6', '6', '4', '9', '6', '8', '3', '0']), .str (String.ofList ['4', '9', '6', '9', '8', '3', '9', '5', '7', '6', '7', '7', '5', '2', '8', '7', '2', '0', '0', '5', '8']), .str (String.ofList ['6', '1', '4', '7', '3', '6', '0', '5', '0', '5', '6', '2', '4', '8', '8', '9', '3', '2', '2', '8', '2']), .str (String.ofList ['2', '4', '9', '0', '5', '4', '3', '1', '9', '1', '9', '1', '1', '3', '0', '6', '6', '0', '5', '5', '9', '8']), .str (String.ofList ['9', '7', '9', '5', '5', '4', '5', '1', '5', '0', '3', '3', '9', '9', '9', '5', '6', '0', '0', '3', '9']), .str (String.ofList ['8', '5', '1', '8', '9', '4', '8', '5', '5', '8', '0', '7', '9', '1', '5', '7', '7', '8', '7', '8', '8']), .str (String.ofList ['7', '4', '1', '3', '1', '8', '5', '5', '2', '2', '0', '9', '7', '8', '9', '0', '5', '7', '3', '5', '0']), .str (String.ofList ['7', '4', '1', '3', '3', '3', '4', '4', '0', '4', '4', '5', '1', '3', '2', '7', '0', '4', '8', '9', '0'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '8', '5', '6', '4', '4', '0', '3', '5', '6', '3', '9', '4', '2', '6'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '8', '9', '7', '4', '7', '9', '1', '7', '8', '6', '6', '9', '0', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_121_before_generic"
  err.flush

theorem array_moment_records_chunk_121 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 60)
      (SourceJson.white (momentRecordsChunk121Chars ++ tail)) acc =
      SourceJson.array (fuel + 59) (SourceJson.white tail) (momentRecordsChunk121Push acc) := by rfl

noncomputable def momentRecordsAcc122 : List SourceJson := momentRecordsChunk121Push momentRecordsAcc121

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_121_generic_complete"
  err.flush

noncomputable def momentRecordsChunk122Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '8', '1', '3', '6', '7', '3', '3', '7', '0', '7', '9', '4', '0', '7', '6', '1', '9', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '0', '9', '5', '8', '1', '5', '6', '7', '4', '0', '8', '6', '8', '5', '7', '4', '5', '3', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '9', '7', '6', '9', '8', '3', '3', '7', '0', '9', '7', '5', '9', '7', '5', '1', '9', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '5', '4', '5', '3', '5', '8', '6', '4', '6', '5', '7', '7', '0', '0', '4', '9', '8', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '7', '5', '4', '2', '6', '9', '2', '5', '2', '9', '9', '3', '1', '6', '0', '4', '3', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '2', '4', '9', '6', '1', '7', '4', '2', '9', '6', '9', '0', '3', '2', '4', '2', '0', '4', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '9', '5', '8', '8', '5', '3', '9', '2', '3', '5', '1', '3', '3', '2', '2', '9', '6', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '1', '7', '6', '5', '6', '0', '8', '0', '4', '4', '1', '5', '4', '3', '9', '3', '0', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '8', '1', '7', '2', '4', '7', '3', '3', '7', '9', '5', '7', '5', '9', '8', '5', '1', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '8', '1', '8', '8', '4', '2', '8', '3', '1', '1', '0', '0', '2', '4', '5', '7', '4', '2', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '9', '9', '2', '9', '2', '9', '8', '7', '7', '6', '4', '0', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '0', '5', '5', '1', '1', '6', '2', '8', '8', '8', '5', '8', '3', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk122Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '2', '2'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '4', '0', '8', '1', '3', '6', '7', '3', '3', '7', '0', '7', '9', '4', '0', '7', '6', '1', '9', '7', '5']), .str (String.ofList ['1', '5', '0', '9', '5', '8', '1', '5', '6', '7', '4', '0', '8', '6', '8', '5', '7', '4', '5', '3', '8', '4']), .str (String.ofList ['3', '4', '9', '7', '6', '9', '8', '3', '3', '7', '0', '9', '7', '5', '9', '7', '5', '1', '9', '5', '1']), .str (String.ofList ['5', '2', '5', '4', '5', '3', '5', '8', '6', '4', '6', '5', '7', '7', '0', '0', '4', '9', '8', '1', '4']), .str (String.ofList ['7', '2', '7', '5', '4', '2', '6', '9', '2', '5', '2', '9', '9', '3', '1', '6', '0', '4', '3', '6', '1']), .str (String.ofList ['2', '6', '2', '4', '9', '6', '1', '7', '4', '2', '9', '6', '9', '0', '3', '2', '4', '2', '0', '4', '0', '2']), .str (String.ofList ['1', '0', '7', '9', '5', '8', '8', '5', '3', '9', '2', '3', '5', '1', '3', '3', '2', '2', '9', '6', '3', '9']), .str (String.ofList ['1', '0', '8', '1', '7', '6', '5', '6', '0', '8', '0', '4', '4', '1', '5', '4', '3', '9', '3', '0', '7', '4']), .str (String.ofList ['6', '9', '8', '1', '7', '2', '4', '7', '3', '3', '7', '9', '5', '7', '5', '9', '8', '5', '1', '1', '3']), .str (String.ofList ['6', '9', '8', '1', '8', '8', '4', '2', '8', '3', '1', '1', '0', '0', '2', '4', '5', '7', '4', '2', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '9', '9', '2', '9', '2', '9', '8', '7', '7', '6', '4', '0', '4', '6'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['7', '0', '5', '5', '1', '1', '6', '2', '8', '8', '8', '5', '8', '3', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_122_before_generic"
  err.flush

theorem array_moment_records_chunk_122 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 59)
      (SourceJson.white (momentRecordsChunk122Chars ++ tail)) acc =
      SourceJson.array (fuel + 58) (SourceJson.white tail) (momentRecordsChunk122Push acc) := by rfl

noncomputable def momentRecordsAcc123 : List SourceJson := momentRecordsChunk122Push momentRecordsAcc122

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_122_generic_complete"
  err.flush

noncomputable def momentRecordsChunk123Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '2', '4', '5', '6', '2', '8', '0', '4', '3', '8', '4', '6', '2', '1', '6', '3', '2', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '6', '2', '1', '9', '1', '1', '3', '1', '3', '0', '6', '0', '7', '5', '5', '2', '8', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '1', '1', '7', '9', '9', '4', '2', '4', '3', '6', '1', '0', '5', '6', '3', '2', '8', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '4', '3', '3', '8', '9', '0', '6', '2', '2', '3', '9', '4', '1', '3', '6', '4', '4', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '0', '1', '1', '0', '8', '5', '1', '6', '7', '1', '1', '8', '9', '6', '5', '5', '3', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '7', '9', '2', '7', '1', '0', '2', '4', '1', '8', '6', '1', '1', '9', '8', '2', '9', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '5', '8', '6', '2', '8', '0', '2', '2', '8', '4', '7', '5', '0', '5', '2', '8', '9', '8', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '7', '9', '5', '6', '6', '1', '3', '9', '9', '7', '0', '0', '5', '5', '4', '2', '9', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '5', '3', '7', '3', '9', '5', '7', '6', '9', '2', '9', '9', '8', '0', '1', '2', '4', '9', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '5', '3', '9', '1', '8', '9', '2', '9', '6', '0', '1', '3', '0', '4', '5', '7', '5', '2', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '8', '7', '0', '4', '7', '2', '6', '3', '0', '7', '7', '2', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '9', '4', '5', '1', '6', '9', '8', '0', '5', '8', '8', '0', '0', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk123Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '2', '3'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '5', '2', '4', '5', '6', '2', '8', '0', '4', '3', '8', '4', '6', '2', '1', '6', '3', '2', '1', '7']), .str (String.ofList ['1', '4', '3', '6', '2', '1', '9', '1', '1', '3', '1', '3', '0', '6', '0', '7', '5', '5', '2', '8', '3', '4']), .str (String.ofList ['3', '6', '1', '1', '7', '9', '9', '4', '2', '4', '3', '6', '1', '0', '5', '6', '3', '2', '8', '9', '2']), .str (String.ofList ['5', '4', '4', '3', '3', '8', '9', '0', '6', '2', '2', '3', '9', '4', '1', '3', '6', '4', '4', '5', '2']), .str (String.ofList ['7', '3', '0', '1', '1', '0', '8', '5', '1', '6', '7', '1', '1', '8', '9', '6', '5', '5', '3', '4', '3']), .str (String.ofList ['2', '7', '3', '7', '9', '2', '7', '1', '0', '2', '4', '1', '8', '6', '1', '1', '9', '8', '2', '9', '4', '8']), .str (String.ofList ['1', '9', '5', '8', '6', '2', '8', '0', '2', '2', '8', '4', '7', '5', '0', '5', '2', '8', '9', '8', '7', '4']), .str (String.ofList ['1', '1', '8', '7', '9', '5', '6', '6', '1', '3', '9', '9', '7', '0', '0', '5', '5', '4', '2', '9', '0', '1']), .str (String.ofList ['5', '5', '5', '3', '7', '3', '9', '5', '7', '6', '9', '2', '9', '9', '8', '0', '1', '2', '4', '9', '7']), .str (String.ofList ['5', '5', '5', '3', '9', '1', '8', '9', '2', '9', '6', '0', '1', '3', '0', '4', '5', '7', '5', '2', '0'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['7', '8', '7', '0', '4', '7', '2', '6', '3', '0', '7', '7', '2', '7', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['7', '9', '4', '5', '1', '6', '9', '8', '0', '5', '8', '8', '0', '0', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_123_before_generic"
  err.flush

theorem array_moment_records_chunk_123 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 58)
      (SourceJson.white (momentRecordsChunk123Chars ++ tail)) acc =
      SourceJson.array (fuel + 57) (SourceJson.white tail) (momentRecordsChunk123Push acc) := by rfl

noncomputable def momentRecordsAcc124 : List SourceJson := momentRecordsChunk123Push momentRecordsAcc123

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_123_generic_complete"
  err.flush

noncomputable def momentRecordsBlock030Chars : List Char := momentRecordsChunk120Chars ++ momentRecordsChunk121Chars ++ momentRecordsChunk122Chars ++ momentRecordsChunk123Chars
noncomputable def momentRecordsBlock030Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk123Push (momentRecordsChunk122Push (momentRecordsChunk121Push (momentRecordsChunk120Push (acc))))

theorem array_moment_records_block_030 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 61)
      (SourceJson.white (momentRecordsBlock030Chars ++ tail)) acc =
      SourceJson.array (fuel + 57) (SourceJson.white tail) (momentRecordsBlock030Push acc) := by
  have hinput : momentRecordsBlock030Chars ++ tail = momentRecordsChunk120Chars ++ (momentRecordsChunk121Chars ++ (momentRecordsChunk122Chars ++ (momentRecordsChunk123Chars ++ (tail)))) := by
    simp only [momentRecordsBlock030Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 61) (SourceJson.white (momentRecordsBlock030Chars ++ tail)) acc =
        SourceJson.array (fuel + 61) (SourceJson.white (momentRecordsChunk120Chars ++ (momentRecordsChunk121Chars ++ (momentRecordsChunk122Chars ++ (momentRecordsChunk123Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 61) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 60) (SourceJson.white (momentRecordsChunk121Chars ++ (momentRecordsChunk122Chars ++ (momentRecordsChunk123Chars ++ (tail))))) (momentRecordsChunk120Push (acc)) := array_moment_records_chunk_120 fuel (momentRecordsChunk121Chars ++ (momentRecordsChunk122Chars ++ (momentRecordsChunk123Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 59) (SourceJson.white (momentRecordsChunk122Chars ++ (momentRecordsChunk123Chars ++ (tail)))) (momentRecordsChunk121Push (momentRecordsChunk120Push (acc))) := array_moment_records_chunk_121 fuel (momentRecordsChunk122Chars ++ (momentRecordsChunk123Chars ++ (tail))) (momentRecordsChunk120Push (acc))
    _ = SourceJson.array (fuel + 58) (SourceJson.white (momentRecordsChunk123Chars ++ (tail))) (momentRecordsChunk122Push (momentRecordsChunk121Push (momentRecordsChunk120Push (acc)))) := array_moment_records_chunk_122 fuel (momentRecordsChunk123Chars ++ (tail)) (momentRecordsChunk121Push (momentRecordsChunk120Push (acc)))
    _ = SourceJson.array (fuel + 57) (SourceJson.white tail) (momentRecordsBlock030Push acc) := array_moment_records_chunk_123 fuel (tail) (momentRecordsChunk122Push (momentRecordsChunk121Push (momentRecordsChunk120Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_030_before_raw_binding"
  err.flush

theorem moment_records_block_030_prefix :
    (momentRest01 62728).take 2069 = momentRecordsBlock030Chars := by rfl

theorem moment_records_block_030_split :
    momentRest01 62728 = momentRecordsBlock030Chars ++ momentRest01 64797 := by
  calc
    momentRest01 62728 =
        (momentRest01 62728).take 2069 ++ (momentRest01 62728).drop 2069 :=
      (List.take_append_drop 2069 (momentRest01 62728)).symm
    _ = momentRecordsBlock030Chars ++ (momentRest01 62728).drop 2069 :=
      congrArg (fun p => p ++ (momentRest01 62728).drop 2069) moment_records_block_030_prefix
    _ = momentRecordsBlock030Chars ++ momentRest01 64797 :=
      congrArg (fun rest => momentRecordsBlock030Chars ++ rest) (momentRest01_drop 62728 2069)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_030_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_030 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 61)
      (SourceJson.white (momentRest01 62728)) acc =
      SourceJson.array (fuel + 57) (SourceJson.white (momentRest01 64797)) (momentRecordsBlock030Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 61) (SourceJson.white s) acc)
      moment_records_block_030_split).trans (array_moment_records_block_030 fuel (momentRest01 64797) acc)

theorem moment_records_through_block_030 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 57) (SourceJson.white (momentRest01 64797)) momentRecordsAcc124 := by
  exact (moment_records_through_block_029 fuel).trans (array_moment_records_original_block_030 fuel momentRecordsAcc120)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_030_complete"
  err.flush

#print axioms array_moment_records_chunk_120
#print axioms array_moment_records_chunk_121
#print axioms array_moment_records_chunk_122
#print axioms array_moment_records_chunk_123
#print axioms array_moment_records_block_030
#print axioms moment_records_block_030_prefix
#print axioms moment_records_block_030_split
#print axioms array_moment_records_original_block_030
#print axioms moment_records_through_block_030

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
