import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock024

/-! Original moment records block 25. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk100Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '5', '8', '7', '5', '2', '8', '3', '9', '3', '8', '6', '5', '2', '0', '9', '3', '6', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '3', '6', '4', '5', '8', '8', '1', '4', '0', '8', '7', '1', '6', '1', '2', '0', '7', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '9', '2', '5', '8', '3', '7', '1', '7', '2', '8', '0', '0', '9', '5', '8', '3', '5', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '9', '2', '6', '7', '4', '8', '7', '4', '0', '0', '5', '9', '5', '9', '1', '8', '0', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '0', '2', '9', '0', '1', '5', '8', '8', '1', '2', '5', '7', '4', '7', '1', '5', '3', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '1', '4', '7', '7', '8', '3', '3', '2', '5', '9', '7', '3', '2', '6', '1', '0', '9', '6', '6', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '3', '6', '2', '9', '5', '1', '4', '0', '4', '8', '7', '7', '0', '8', '9', '5', '9', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '0', '1', '7', '2', '8', '8', '5', '6', '8', '0', '5', '8', '2', '2', '0', '0', '6', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '5', '6', '9', '1', '4', '0', '7', '5', '8', '3', '2', '2', '0', '6', '0', '4', '3', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '2', '9', '3', '6', '3', '2', '3', '1', '1', '6', '1', '2', '0', '1', '1', '5', '4', '9', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '0', '0', '8', '0', '3', '0', '0', '5', '2', '9', '9', '9', '4', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '1', '4', '8', '3', '9', '8', '7', '4', '0', '1', '2', '9', '6', '3', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk100Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '0', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '8', '1', '5', '8', '7', '5', '2', '8', '3', '9', '3', '8', '6', '5', '2', '0', '9', '3', '6', '9', '8']), .str (String.ofList ['1', '7', '6', '3', '6', '4', '5', '8', '8', '1', '4', '0', '8', '7', '1', '6', '1', '2', '0', '7', '8', '2']), .str (String.ofList ['2', '1', '9', '2', '5', '8', '3', '7', '1', '7', '2', '8', '0', '0', '9', '5', '8', '3', '5', '3', '8']), .str (String.ofList ['7', '5', '9', '2', '6', '7', '4', '8', '7', '4', '0', '0', '5', '9', '5', '9', '1', '8', '0', '6', '1']), .str (String.ofList ['1', '0', '4', '0', '2', '9', '0', '1', '5', '8', '8', '1', '2', '5', '7', '4', '7', '1', '5', '3', '0', '8']), .str (String.ofList ['2', '0', '1', '4', '7', '7', '8', '3', '3', '2', '5', '9', '7', '3', '2', '6', '1', '0', '9', '6', '6', '8']), .str (String.ofList ['1', '3', '4', '3', '6', '2', '9', '5', '1', '4', '0', '4', '8', '7', '7', '0', '8', '9', '5', '9', '1', '2']), .str (String.ofList ['1', '1', '9', '0', '1', '7', '2', '8', '8', '5', '6', '8', '0', '5', '8', '2', '2', '0', '0', '6', '8', '2']), .str (String.ofList ['1', '1', '2', '5', '6', '9', '1', '4', '0', '7', '5', '8', '3', '2', '2', '0', '6', '0', '4', '3', '1', '6']), .str (String.ofList ['1', '7', '0', '2', '9', '3', '6', '3', '2', '3', '1', '1', '6', '1', '2', '0', '1', '1', '5', '4', '9', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '3', '0', '0', '8', '0', '3', '0', '0', '5', '2', '9', '9', '9', '4', '1', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '3', '1', '4', '8', '3', '9', '8', '7', '4', '0', '1', '2', '9', '6', '3', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_100_before_generic"
  err.flush

theorem array_moment_records_chunk_100 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 81)
      (SourceJson.white (momentRecordsChunk100Chars ++ tail)) acc =
      SourceJson.array (fuel + 80) (SourceJson.white tail) (momentRecordsChunk100Push acc) := by rfl

noncomputable def momentRecordsAcc101 : List SourceJson := momentRecordsChunk100Push momentRecordsAcc100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_100_generic_complete"
  err.flush

noncomputable def momentRecordsChunk101Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '8', '2', '0', '9', '8', '0', '4', '2', '9', '2', '9', '8', '2', '2', '1', '3', '8', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '8', '5', '6', '6', '3', '1', '2', '9', '7', '9', '4', '0', '0', '5', '4', '0', '5', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '2', '8', '0', '5', '1', '3', '2', '5', '7', '3', '0', '6', '8', '8', '7', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '0', '6', '7', '4', '6', '8', '9', '3', '4', '2', '2', '3', '6', '3', '2', '2', '5', '9', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '1', '2', '5', '0', '8', '3', '3', '7', '0', '4', '6', '5', '1', '8', '1', '3', '0', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '4', '5', '3', '5', '6', '8', '3', '2', '6', '9', '4', '5', '4', '3', '7', '4', '0', '4', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '0', '8', '6', '6', '0', '3', '4', '9', '6', '1', '1', '0', '3', '9', '7', '7', '5', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '3', '4', '4', '5', '9', '9', '1', '8', '5', '3', '2', '0', '5', '1', '8', '9', '8', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '7', '1', '4', '7', '2', '7', '8', '2', '5', '1', '7', '8', '1', '0', '4', '8', '1', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '3', '3', '9', '0', '5', '2', '1', '4', '6', '6', '6', '1', '6', '9', '2', '9', '2', '5', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '1', '9', '1', '8', '4', '5', '8', '2', '9', '1', '6', '3', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '3', '3', '2', '4', '0', '1', '7', '3', '5', '4', '5', '7', '8', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk101Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '0', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '0', '8', '2', '0', '9', '8', '0', '4', '2', '9', '2', '9', '8', '2', '2', '1', '3', '8', '7', '8']), .str (String.ofList ['1', '2', '6', '8', '5', '6', '6', '3', '1', '2', '9', '7', '9', '4', '0', '0', '5', '4', '0', '5', '7', '2']), .str (String.ofList ['1', '6', '4', '8', '2', '8', '0', '5', '1', '3', '2', '5', '7', '3', '0', '6', '8', '8', '7', '2', '4']), .str (String.ofList ['7', '0', '6', '7', '4', '6', '8', '9', '3', '4', '2', '2', '3', '6', '3', '2', '2', '5', '9', '4', '6']), .str (String.ofList ['8', '0', '1', '2', '5', '0', '8', '3', '3', '7', '0', '4', '6', '5', '1', '8', '1', '3', '0', '2', '9']), .str (String.ofList ['1', '5', '8', '4', '5', '3', '5', '6', '8', '3', '2', '6', '9', '4', '5', '4', '3', '7', '4', '0', '4', '0']), .str (String.ofList ['1', '1', '0', '0', '8', '6', '6', '0', '3', '4', '9', '6', '1', '1', '0', '3', '9', '7', '7', '5', '4', '8']), .str (String.ofList ['9', '8', '3', '4', '4', '5', '9', '9', '1', '8', '5', '3', '2', '0', '5', '1', '8', '9', '8', '0', '6']), .str (String.ofList ['9', '3', '7', '1', '4', '7', '2', '7', '8', '2', '5', '1', '7', '8', '1', '0', '4', '8', '1', '5', '5']), .str (String.ofList ['1', '5', '9', '3', '3', '9', '0', '5', '2', '1', '4', '6', '6', '6', '1', '6', '9', '2', '9', '2', '5', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '6', '1', '9', '1', '8', '4', '5', '8', '2', '9', '1', '6', '3', '9', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '6', '3', '3', '2', '4', '0', '1', '7', '3', '5', '4', '5', '7', '8', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_101_before_generic"
  err.flush

theorem array_moment_records_chunk_101 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 80)
      (SourceJson.white (momentRecordsChunk101Chars ++ tail)) acc =
      SourceJson.array (fuel + 79) (SourceJson.white tail) (momentRecordsChunk101Push acc) := by rfl

noncomputable def momentRecordsAcc102 : List SourceJson := momentRecordsChunk101Push momentRecordsAcc101

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_101_generic_complete"
  err.flush

noncomputable def momentRecordsChunk102Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '2', '2', '6', '7', '6', '3', '1', '5', '3', '7', '4', '4', '8', '1', '7', '3', '7', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '7', '1', '6', '0', '7', '1', '9', '2', '1', '3', '4', '9', '6', '0', '6', '0', '7', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '5', '7', '8', '8', '7', '9', '9', '8', '7', '4', '2', '6', '3', '0', '1', '1', '3', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '9', '9', '8', '7', '8', '6', '6', '4', '1', '3', '8', '2', '8', '6', '5', '1', '3', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '7', '7', '6', '8', '2', '4', '1', '3', '5', '0', '0', '2', '0', '9', '2', '6', '9', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '0', '6', '3', '3', '8', '8', '9', '7', '9', '1', '6', '8', '2', '8', '9', '2', '6', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '7', '5', '7', '1', '0', '1', '3', '1', '8', '3', '6', '8', '5', '0', '5', '2', '4', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '6', '1', '2', '5', '0', '3', '5', '7', '2', '6', '3', '4', '7', '4', '7', '0', '7', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '6', '0', '8', '8', '8', '0', '2', '7', '8', '1', '3', '2', '6', '7', '2', '0', '1', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '4', '1', '0', '1', '2', '6', '6', '8', '7', '9', '7', '0', '4', '3', '4', '7', '4', '9', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '3', '2', '5', '7', '9', '7', '8', '8', '0', '1', '3', '1', '9', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '4', '4', '9', '8', '6', '1', '9', '9', '1', '6', '2', '4', '0', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk102Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '0', '2'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '0', '2', '2', '2', '6', '7', '6', '3', '1', '5', '3', '7', '4', '4', '8', '1', '7', '3', '7', '4', '9']), .str (String.ofList ['1', '0', '8', '7', '1', '6', '0', '7', '1', '9', '2', '1', '3', '4', '9', '6', '0', '6', '0', '7', '3', '5']), .str (String.ofList ['2', '9', '5', '7', '8', '8', '7', '9', '9', '8', '7', '4', '2', '6', '3', '0', '1', '1', '3', '9', '2']), .str (String.ofList ['5', '5', '9', '9', '8', '7', '8', '6', '6', '4', '1', '3', '8', '2', '8', '6', '5', '1', '3', '2', '2']), .str (String.ofList ['1', '3', '1', '7', '7', '6', '8', '2', '4', '1', '3', '5', '0', '0', '2', '0', '9', '2', '6', '9', '0', '7']), .str (String.ofList ['2', '0', '6', '0', '6', '3', '3', '8', '8', '9', '7', '9', '1', '6', '8', '2', '8', '9', '2', '6', '0', '0']), .str (String.ofList ['2', '0', '8', '7', '5', '7', '1', '0', '1', '3', '1', '8', '3', '6', '8', '5', '0', '5', '2', '4', '8', '8']), .str (String.ofList ['1', '0', '5', '6', '1', '2', '5', '0', '3', '5', '7', '2', '6', '3', '4', '7', '4', '7', '0', '7', '3', '0']), .str (String.ofList ['1', '0', '5', '6', '0', '8', '8', '8', '0', '2', '7', '8', '1', '3', '2', '6', '7', '2', '0', '1', '7', '1']), .str (String.ofList ['1', '5', '6', '4', '1', '0', '1', '2', '6', '6', '8', '7', '9', '7', '0', '4', '3', '4', '7', '4', '9', '0'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '2', '3', '2', '5', '7', '9', '7', '8', '8', '0', '1', '3', '1', '9', '9'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '2', '4', '4', '9', '8', '6', '1', '9', '9', '1', '6', '2', '4', '0', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_102_before_generic"
  err.flush

theorem array_moment_records_chunk_102 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 79)
      (SourceJson.white (momentRecordsChunk102Chars ++ tail)) acc =
      SourceJson.array (fuel + 78) (SourceJson.white tail) (momentRecordsChunk102Push acc) := by rfl

noncomputable def momentRecordsAcc103 : List SourceJson := momentRecordsChunk102Push momentRecordsAcc102

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_102_generic_complete"
  err.flush

noncomputable def momentRecordsChunk103Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '1', '0', '3', '8', '4', '0', '6', '4', '0', '9', '6', '2', '0', '6', '1', '3', '5', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '1', '1', '3', '8', '8', '0', '2', '0', '6', '9', '7', '7', '2', '9', '2', '8', '6', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '9', '8', '9', '7', '9', '2', '2', '7', '8', '1', '3', '8', '6', '9', '9', '0', '9', '7', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '4', '8', '2', '6', '1', '1', '8', '0', '4', '0', '8', '7', '7', '7', '7', '9', '8', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '5', '0', '4', '4', '0', '9', '0', '3', '6', '4', '6', '0', '9', '5', '9', '1', '5', '9', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '0', '3', '8', '0', '5', '4', '8', '0', '9', '1', '6', '4', '7', '2', '2', '0', '1', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '7', '9', '5', '7', '9', '0', '3', '0', '9', '3', '2', '6', '9', '2', '4', '4', '6', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '8', '8', '9', '2', '3', '2', '1', '4', '6', '5', '3', '9', '9', '7', '0', '4', '0', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '8', '8', '6', '7', '2', '0', '7', '8', '2', '6', '7', '5', '5', '8', '2', '9', '2', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '9', '6', '1', '8', '0', '2', '5', '9', '4', '3', '1', '3', '6', '0', '1', '3', '1', '3', '2', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '8', '0', '2', '5', '4', '0', '8', '0', '9', '9', '0', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '1', '4', '8', '9', '6', '6', '5', '8', '5', '1', '9', '8', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk103Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '0', '3'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '4', '6', '1', '0', '3', '8', '4', '0', '6', '4', '0', '9', '6', '2', '0', '6', '1', '3', '5', '5', '2']), .str (String.ofList ['1', '5', '4', '1', '1', '3', '8', '8', '0', '2', '0', '6', '9', '7', '7', '2', '9', '2', '8', '6', '2', '8']), .str (String.ofList ['2', '8', '9', '8', '9', '7', '9', '2', '2', '7', '8', '1', '3', '8', '6', '9', '9', '0', '9', '7', '7']), .str (String.ofList ['6', '3', '4', '8', '2', '6', '1', '1', '8', '0', '4', '0', '8', '7', '7', '7', '7', '9', '8', '1', '9']), .str (String.ofList ['1', '3', '7', '5', '0', '4', '4', '0', '9', '0', '3', '6', '4', '6', '0', '9', '5', '9', '1', '5', '9', '9']), .str (String.ofList ['2', '0', '0', '3', '8', '0', '5', '4', '8', '0', '9', '1', '6', '4', '7', '2', '2', '0', '1', '7', '5', '0']), .str (String.ofList ['1', '6', '1', '7', '9', '5', '7', '9', '0', '3', '0', '9', '3', '2', '6', '9', '2', '4', '4', '6', '0', '5']), .str (String.ofList ['1', '0', '8', '8', '8', '9', '2', '3', '2', '1', '4', '6', '5', '3', '9', '9', '7', '0', '4', '0', '3', '7']), .str (String.ofList ['1', '0', '8', '8', '8', '6', '7', '2', '0', '7', '8', '2', '6', '7', '5', '5', '8', '2', '9', '2', '0', '2']), .str (String.ofList ['1', '9', '9', '6', '1', '8', '0', '2', '5', '9', '4', '3', '1', '3', '6', '0', '1', '3', '1', '3', '2', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '1', '8', '0', '2', '5', '4', '0', '8', '0', '9', '9', '0', '7', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '2', '1', '4', '8', '9', '6', '6', '5', '8', '5', '1', '9', '8', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_103_before_generic"
  err.flush

theorem array_moment_records_chunk_103 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 78)
      (SourceJson.white (momentRecordsChunk103Chars ++ tail)) acc =
      SourceJson.array (fuel + 77) (SourceJson.white tail) (momentRecordsChunk103Push acc) := by rfl

noncomputable def momentRecordsAcc104 : List SourceJson := momentRecordsChunk103Push momentRecordsAcc103

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_103_generic_complete"
  err.flush

noncomputable def momentRecordsBlock025Chars : List Char := momentRecordsChunk100Chars ++ momentRecordsChunk101Chars ++ momentRecordsChunk102Chars ++ momentRecordsChunk103Chars
noncomputable def momentRecordsBlock025Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk103Push (momentRecordsChunk102Push (momentRecordsChunk101Push (momentRecordsChunk100Push (acc))))

theorem array_moment_records_block_025 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 81)
      (SourceJson.white (momentRecordsBlock025Chars ++ tail)) acc =
      SourceJson.array (fuel + 77) (SourceJson.white tail) (momentRecordsBlock025Push acc) := by
  have hinput : momentRecordsBlock025Chars ++ tail = momentRecordsChunk100Chars ++ (momentRecordsChunk101Chars ++ (momentRecordsChunk102Chars ++ (momentRecordsChunk103Chars ++ (tail)))) := by
    simp only [momentRecordsBlock025Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 81) (SourceJson.white (momentRecordsBlock025Chars ++ tail)) acc =
        SourceJson.array (fuel + 81) (SourceJson.white (momentRecordsChunk100Chars ++ (momentRecordsChunk101Chars ++ (momentRecordsChunk102Chars ++ (momentRecordsChunk103Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 81) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 80) (SourceJson.white (momentRecordsChunk101Chars ++ (momentRecordsChunk102Chars ++ (momentRecordsChunk103Chars ++ (tail))))) (momentRecordsChunk100Push (acc)) := array_moment_records_chunk_100 fuel (momentRecordsChunk101Chars ++ (momentRecordsChunk102Chars ++ (momentRecordsChunk103Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 79) (SourceJson.white (momentRecordsChunk102Chars ++ (momentRecordsChunk103Chars ++ (tail)))) (momentRecordsChunk101Push (momentRecordsChunk100Push (acc))) := array_moment_records_chunk_101 fuel (momentRecordsChunk102Chars ++ (momentRecordsChunk103Chars ++ (tail))) (momentRecordsChunk100Push (acc))
    _ = SourceJson.array (fuel + 78) (SourceJson.white (momentRecordsChunk103Chars ++ (tail))) (momentRecordsChunk102Push (momentRecordsChunk101Push (momentRecordsChunk100Push (acc)))) := array_moment_records_chunk_102 fuel (momentRecordsChunk103Chars ++ (tail)) (momentRecordsChunk101Push (momentRecordsChunk100Push (acc)))
    _ = SourceJson.array (fuel + 77) (SourceJson.white tail) (momentRecordsBlock025Push acc) := array_moment_records_chunk_103 fuel (tail) (momentRecordsChunk102Push (momentRecordsChunk101Push (momentRecordsChunk100Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_025_before_raw_binding"
  err.flush

theorem moment_records_block_025_prefix :
    (momentRest01 52388).take 2089 = momentRecordsBlock025Chars := by rfl

theorem moment_records_block_025_split :
    momentRest01 52388 = momentRecordsBlock025Chars ++ momentRest01 54477 := by
  calc
    momentRest01 52388 =
        (momentRest01 52388).take 2089 ++ (momentRest01 52388).drop 2089 :=
      (List.take_append_drop 2089 (momentRest01 52388)).symm
    _ = momentRecordsBlock025Chars ++ (momentRest01 52388).drop 2089 :=
      congrArg (fun p => p ++ (momentRest01 52388).drop 2089) moment_records_block_025_prefix
    _ = momentRecordsBlock025Chars ++ momentRest01 54477 :=
      congrArg (fun rest => momentRecordsBlock025Chars ++ rest) (momentRest01_drop 52388 2089)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_025_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_025 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 81)
      (SourceJson.white (momentRest01 52388)) acc =
      SourceJson.array (fuel + 77) (SourceJson.white (momentRest01 54477)) (momentRecordsBlock025Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 81) (SourceJson.white s) acc)
      moment_records_block_025_split).trans (array_moment_records_block_025 fuel (momentRest01 54477) acc)

theorem moment_records_through_block_025 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 77) (SourceJson.white (momentRest01 54477)) momentRecordsAcc104 := by
  exact (moment_records_through_block_024 fuel).trans (array_moment_records_original_block_025 fuel momentRecordsAcc100)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_025_complete"
  err.flush

#print axioms array_moment_records_chunk_100
#print axioms array_moment_records_chunk_101
#print axioms array_moment_records_chunk_102
#print axioms array_moment_records_chunk_103
#print axioms array_moment_records_block_025
#print axioms moment_records_block_025_prefix
#print axioms moment_records_block_025_split
#print axioms array_moment_records_original_block_025
#print axioms moment_records_through_block_025

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
