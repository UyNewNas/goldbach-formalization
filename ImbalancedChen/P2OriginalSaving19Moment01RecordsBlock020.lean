import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock019

/-! Original moment records block 20. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk080Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '6', '1', '9', '4', '2', '5', '7', '1', '3', '3', '8', '9', '2', '2', '3', '3', '9', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '0', '9', '8', '8', '8', '8', '5', '0', '8', '0', '6', '3', '7', '2', '1', '0', '8', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '3', '6', '0', '7', '5', '2', '9', '4', '9', '4', '0', '0', '4', '2', '4', '7', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '1', '7', '3', '5', '2', '5', '0', '6', '8', '2', '4', '5', '8', '1', '9', '5', '7', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '4', '7', '3', '6', '3', '5', '6', '7', '6', '0', '2', '4', '1', '4', '8', '4', '4', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '0', '5', '3', '4', '7', '3', '9', '4', '8', '6', '6', '5', '4', '2', '5', '8', '9', '4', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '4', '2', '9', '5', '5', '0', '3', '1', '5', '8', '1', '1', '0', '5', '0', '9', '5', '2', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '6', '4', '5', '9', '4', '0', '4', '2', '2', '5', '5', '2', '4', '7', '4', '8', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '7', '7', '2', '9', '1', '1', '1', '7', '9', '9', '9', '7', '8', '4', '4', '0', '3', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '1', '6', '1', '0', '2', '5', '1', '1', '9', '9', '9', '5', '0', '0', '7', '6', '1', '5', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '3', '8', '0', '8', '2', '4', '5', '6', '2', '3', '0', '7', '4', '7', '6', '2', '5', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '5', '8', '1', '5', '4', '8', '3', '8', '9', '5', '3', '6', '8', '1', '4', '8', '4', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk080Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['8', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['6', '5', '6', '1', '9', '4', '2', '5', '7', '1', '3', '3', '8', '9', '2', '2', '3', '3', '9', '6', '4']), .str (String.ofList ['6', '9', '0', '9', '8', '8', '8', '8', '5', '0', '8', '0', '6', '3', '7', '2', '1', '0', '8', '2', '1']), .str (String.ofList ['2', '9', '9', '3', '6', '0', '7', '5', '2', '9', '4', '9', '4', '0', '0', '4', '2', '4', '7', '4', '8']), .str (String.ofList ['4', '9', '1', '7', '3', '5', '2', '5', '0', '6', '8', '2', '4', '5', '8', '1', '9', '5', '7', '8', '2']), .str (String.ofList ['1', '2', '4', '4', '7', '3', '6', '3', '5', '6', '7', '6', '0', '2', '4', '1', '4', '8', '4', '4', '3', '7']), .str (String.ofList ['2', '1', '0', '5', '3', '4', '7', '3', '9', '4', '8', '6', '6', '5', '4', '2', '5', '8', '9', '4', '9', '1']), .str (String.ofList ['1', '8', '4', '2', '9', '5', '5', '0', '3', '1', '5', '8', '1', '1', '0', '5', '0', '9', '5', '2', '1', '0']), .str (String.ofList ['9', '5', '3', '6', '4', '5', '9', '4', '0', '4', '2', '2', '5', '5', '2', '4', '7', '4', '8', '9', '3']), .str (String.ofList ['9', '8', '7', '7', '2', '9', '1', '1', '1', '7', '9', '9', '9', '7', '8', '4', '4', '0', '3', '7', '8']), .str (String.ofList ['1', '0', '6', '1', '6', '1', '0', '2', '5', '1', '1', '9', '9', '9', '5', '0', '0', '7', '6', '1', '5', '2'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '3', '3', '8', '0', '8', '2', '4', '5', '6', '2', '3', '0', '7', '4', '7', '6', '2', '5', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '3', '5', '8', '1', '5', '4', '8', '3', '8', '9', '5', '3', '6', '8', '1', '4', '8', '4', '6']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_080_before_generic"
  err.flush

theorem array_moment_records_chunk_080 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 101)
      (SourceJson.white (momentRecordsChunk080Chars ++ tail)) acc =
      SourceJson.array (fuel + 100) (SourceJson.white tail) (momentRecordsChunk080Push acc) := by rfl

noncomputable def momentRecordsAcc081 : List SourceJson := momentRecordsChunk080Push momentRecordsAcc080

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_080_generic_complete"
  err.flush

noncomputable def momentRecordsChunk081Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '6', '1', '9', '4', '0', '2', '0', '6', '7', '0', '7', '0', '5', '8', '4', '3', '8', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '0', '9', '8', '9', '2', '8', '6', '3', '9', '1', '7', '8', '3', '0', '2', '0', '3', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '3', '6', '0', '8', '4', '3', '8', '8', '5', '7', '1', '4', '8', '4', '9', '4', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '1', '7', '3', '4', '9', '4', '6', '2', '1', '4', '1', '7', '0', '1', '8', '2', '5', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '4', '7', '3', '6', '0', '1', '1', '1', '9', '2', '4', '0', '5', '7', '0', '5', '1', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '0', '5', '3', '4', '8', '2', '8', '4', '4', '4', '5', '5', '0', '5', '9', '0', '2', '6', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '7', '9', '5', '8', '5', '0', '5', '4', '1', '8', '8', '2', '3', '9', '8', '5', '3', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '7', '7', '1', '5', '1', '1', '9', '3', '3', '0', '2', '5', '8', '0', '4', '0', '4', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '7', '7', '0', '2', '2', '7', '2', '3', '3', '1', '0', '5', '7', '1', '8', '2', '2', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '1', '6', '1', '4', '2', '0', '3', '1', '4', '0', '3', '0', '2', '4', '1', '4', '9', '3', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '7', '4', '3', '0', '4', '0', '9', '4', '6', '1', '4', '7', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '8', '5', '8', '7', '0', '3', '5', '4', '0', '7', '3', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk081Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['8', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['6', '5', '6', '1', '9', '4', '0', '2', '0', '6', '7', '0', '7', '0', '5', '8', '4', '3', '8', '3', '0']), .str (String.ofList ['6', '9', '0', '9', '8', '9', '2', '8', '6', '3', '9', '1', '7', '8', '3', '0', '2', '0', '3', '7', '3']), .str (String.ofList ['2', '9', '9', '3', '6', '0', '8', '4', '3', '8', '8', '5', '7', '1', '4', '8', '4', '9', '4', '7', '6']), .str (String.ofList ['4', '9', '1', '7', '3', '4', '9', '4', '6', '2', '1', '4', '1', '7', '0', '1', '8', '2', '5', '7', '5']), .str (String.ofList ['1', '2', '4', '4', '7', '3', '6', '0', '1', '1', '1', '9', '2', '4', '0', '5', '7', '0', '5', '1', '2', '0']), .str (String.ofList ['2', '1', '0', '5', '3', '4', '8', '2', '8', '4', '4', '4', '5', '5', '0', '5', '9', '0', '2', '6', '2', '1']), .str (String.ofList ['2', '3', '9', '7', '9', '5', '8', '5', '0', '5', '4', '1', '8', '8', '2', '3', '9', '8', '5', '3', '7', '1']), .str (String.ofList ['9', '8', '7', '7', '1', '5', '1', '1', '9', '3', '3', '0', '2', '5', '8', '0', '4', '0', '4', '5', '2']), .str (String.ofList ['9', '8', '7', '7', '0', '2', '2', '7', '2', '3', '3', '1', '0', '5', '7', '1', '8', '2', '2', '0', '5']), .str (String.ofList ['1', '0', '6', '1', '6', '1', '4', '2', '0', '3', '1', '4', '0', '3', '0', '2', '4', '1', '4', '9', '3', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '2', '7', '4', '3', '0', '4', '0', '9', '4', '6', '1', '4', '7', '6', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '2', '8', '5', '8', '7', '0', '3', '5', '4', '0', '7', '3', '0', '0', '0']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_081_before_generic"
  err.flush

theorem array_moment_records_chunk_081 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 100)
      (SourceJson.white (momentRecordsChunk081Chars ++ tail)) acc =
      SourceJson.array (fuel + 99) (SourceJson.white tail) (momentRecordsChunk081Push acc) := by rfl

noncomputable def momentRecordsAcc082 : List SourceJson := momentRecordsChunk081Push momentRecordsAcc081

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_081_generic_complete"
  err.flush

noncomputable def momentRecordsChunk082Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '0', '3', '1', '0', '9', '8', '2', '2', '8', '4', '9', '8', '1', '2', '2', '9', '3', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '2', '0', '6', '2', '5', '8', '7', '5', '4', '8', '8', '8', '1', '5', '6', '1', '0', '7', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '1', '6', '2', '0', '0', '9', '8', '2', '2', '1', '3', '3', '0', '2', '5', '4', '6', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '5', '5', '4', '9', '8', '1', '6', '8', '7', '0', '7', '0', '6', '7', '6', '9', '5', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '1', '7', '9', '7', '0', '1', '5', '1', '6', '8', '7', '2', '9', '9', '6', '4', '5', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '0', '5', '3', '1', '7', '4', '4', '7', '4', '5', '9', '4', '4', '4', '7', '3', '9', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '2', '4', '6', '4', '2', '4', '3', '9', '2', '4', '1', '1', '2', '2', '2', '0', '9', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '2', '4', '6', '2', '0', '3', '9', '4', '3', '5', '1', '6', '9', '7', '6', '7', '3', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '0', '0', '8', '6', '6', '1', '5', '1', '2', '2', '0', '4', '0', '7', '5', '4', '5', '4', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '0', '1', '3', '7', '4', '9', '7', '2', '6', '4', '0', '5', '5', '9', '7', '0', '4', '2', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '6', '1', '5', '7', '6', '1', '7', '2', '4', '1', '8', '5', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '7', '9', '6', '4', '4', '2', '6', '7', '9', '9', '7', '6', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk082Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['8', '2'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '1', '1', '0', '3', '1', '0', '9', '8', '2', '2', '8', '4', '9', '8', '1', '2', '2', '9', '3', '8', '4']), .str (String.ofList ['1', '1', '5', '2', '0', '6', '2', '5', '8', '7', '5', '4', '8', '8', '8', '1', '5', '6', '1', '0', '7', '9']), .str (String.ofList ['3', '2', '1', '6', '2', '0', '0', '9', '8', '2', '2', '1', '3', '3', '0', '2', '5', '4', '6', '6', '2']), .str (String.ofList ['6', '5', '5', '5', '4', '9', '8', '1', '6', '8', '7', '0', '7', '0', '6', '7', '6', '9', '5', '0', '9']), .str (String.ofList ['1', '3', '5', '1', '7', '9', '7', '0', '1', '5', '1', '6', '8', '7', '2', '9', '9', '6', '4', '5', '2', '0']), .str (String.ofList ['2', '3', '4', '0', '5', '3', '1', '7', '4', '4', '7', '4', '5', '9', '4', '4', '4', '7', '3', '9', '7', '6']), .str (String.ofList ['1', '3', '7', '2', '4', '6', '4', '2', '4', '3', '9', '2', '4', '1', '1', '2', '2', '2', '0', '9', '1', '5']), .str (String.ofList ['1', '0', '5', '2', '4', '6', '2', '0', '3', '9', '4', '3', '5', '1', '6', '9', '7', '6', '7', '3', '8', '6']), .str (String.ofList ['1', '1', '6', '0', '0', '8', '6', '6', '1', '5', '1', '2', '2', '0', '4', '0', '7', '5', '4', '5', '4', '4']), .str (String.ofList ['1', '1', '6', '0', '1', '3', '7', '4', '9', '7', '2', '6', '4', '0', '5', '5', '9', '7', '0', '4', '2', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '8', '6', '1', '5', '7', '6', '1', '7', '2', '4', '1', '8', '5', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '8', '7', '9', '6', '4', '4', '2', '6', '7', '9', '9', '7', '6', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_082_before_generic"
  err.flush

theorem array_moment_records_chunk_082 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 99)
      (SourceJson.white (momentRecordsChunk082Chars ++ tail)) acc =
      SourceJson.array (fuel + 98) (SourceJson.white tail) (momentRecordsChunk082Push acc) := by rfl

noncomputable def momentRecordsAcc083 : List SourceJson := momentRecordsChunk082Push momentRecordsAcc082

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_082_generic_complete"
  err.flush

noncomputable def momentRecordsChunk083Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '3', '4', '3', '1', '1', '9', '1', '0', '8', '9', '1', '6', '6', '3', '5', '7', '0', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '1', '6', '7', '5', '4', '0', '2', '8', '4', '6', '4', '5', '8', '2', '5', '0', '4', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '6', '2', '9', '0', '8', '1', '4', '4', '1', '1', '0', '7', '7', '4', '5', '0', '9', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '4', '2', '8', '5', '4', '9', '2', '4', '1', '9', '6', '5', '3', '0', '0', '2', '2', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '0', '7', '8', '9', '5', '4', '4', '7', '9', '0', '9', '8', '5', '9', '9', '0', '8', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '7', '4', '8', '6', '9', '2', '3', '9', '8', '1', '2', '7', '1', '9', '1', '1', '4', '5', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '1', '5', '8', '1', '7', '7', '9', '5', '9', '4', '2', '7', '9', '9', '5', '7', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '5', '7', '0', '4', '2', '0', '3', '9', '4', '3', '4', '8', '0', '5', '3', '0', '8', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '2', '0', '1', '5', '5', '6', '1', '4', '3', '4', '9', '2', '9', '7', '9', '6', '0', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '6', '4', '7', '9', '2', '6', '3', '4', '4', '4', '5', '5', '2', '2', '3', '2', '6', '9', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '5', '7', '1', '1', '2', '1', '4', '1', '5', '0', '2', '6', '2', '2', '2', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '7', '5', '9', '7', '8', '9', '3', '7', '7', '4', '8', '6', '3', '0', '7', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk083Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['8', '3'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '0', '1', '3', '4', '3', '1', '1', '9', '1', '0', '8', '9', '1', '6', '6', '3', '5', '7', '0', '9', '8']), .str (String.ofList ['1', '0', '8', '1', '6', '7', '5', '4', '0', '2', '8', '4', '6', '4', '5', '8', '2', '5', '0', '4', '6', '9']), .str (String.ofList ['3', '0', '6', '2', '9', '0', '8', '1', '4', '4', '1', '1', '0', '7', '7', '4', '5', '0', '9', '4', '1']), .str (String.ofList ['5', '6', '4', '2', '8', '5', '4', '9', '2', '4', '1', '9', '6', '5', '3', '0', '0', '2', '2', '3', '8']), .str (String.ofList ['1', '3', '7', '0', '7', '8', '9', '5', '4', '4', '7', '9', '0', '9', '8', '5', '9', '9', '0', '8', '5', '9']), .str (String.ofList ['1', '9', '7', '4', '8', '6', '9', '2', '3', '9', '8', '1', '2', '7', '1', '9', '1', '1', '4', '5', '9', '3']), .str (String.ofList ['1', '3', '4', '1', '5', '8', '1', '7', '7', '9', '5', '9', '4', '2', '7', '9', '9', '5', '7', '7', '5', '0']), .str (String.ofList ['1', '0', '2', '5', '7', '0', '4', '2', '0', '3', '9', '4', '3', '4', '8', '0', '5', '3', '0', '8', '2', '7']), .str (String.ofList ['1', '1', '4', '2', '0', '1', '5', '5', '6', '1', '4', '3', '4', '9', '2', '9', '7', '9', '6', '0', '6', '5']), .str (String.ofList ['1', '2', '1', '6', '4', '7', '9', '2', '6', '3', '4', '4', '4', '5', '5', '2', '2', '3', '2', '6', '9', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '0', '5', '7', '1', '1', '2', '1', '4', '1', '5', '0', '2', '6', '2', '2', '2', '7', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '0', '7', '5', '9', '7', '8', '9', '3', '7', '7', '4', '8', '6', '3', '0', '7', '6', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_083_before_generic"
  err.flush

theorem array_moment_records_chunk_083 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 98)
      (SourceJson.white (momentRecordsChunk083Chars ++ tail)) acc =
      SourceJson.array (fuel + 97) (SourceJson.white tail) (momentRecordsChunk083Push acc) := by rfl

noncomputable def momentRecordsAcc084 : List SourceJson := momentRecordsChunk083Push momentRecordsAcc083

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_083_generic_complete"
  err.flush

noncomputable def momentRecordsBlock020Chars : List Char := momentRecordsChunk080Chars ++ momentRecordsChunk081Chars ++ momentRecordsChunk082Chars ++ momentRecordsChunk083Chars
noncomputable def momentRecordsBlock020Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk083Push (momentRecordsChunk082Push (momentRecordsChunk081Push (momentRecordsChunk080Push (acc))))

theorem array_moment_records_block_020 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 101)
      (SourceJson.white (momentRecordsBlock020Chars ++ tail)) acc =
      SourceJson.array (fuel + 97) (SourceJson.white tail) (momentRecordsBlock020Push acc) := by
  have hinput : momentRecordsBlock020Chars ++ tail = momentRecordsChunk080Chars ++ (momentRecordsChunk081Chars ++ (momentRecordsChunk082Chars ++ (momentRecordsChunk083Chars ++ (tail)))) := by
    simp only [momentRecordsBlock020Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 101) (SourceJson.white (momentRecordsBlock020Chars ++ tail)) acc =
        SourceJson.array (fuel + 101) (SourceJson.white (momentRecordsChunk080Chars ++ (momentRecordsChunk081Chars ++ (momentRecordsChunk082Chars ++ (momentRecordsChunk083Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 101) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 100) (SourceJson.white (momentRecordsChunk081Chars ++ (momentRecordsChunk082Chars ++ (momentRecordsChunk083Chars ++ (tail))))) (momentRecordsChunk080Push (acc)) := array_moment_records_chunk_080 fuel (momentRecordsChunk081Chars ++ (momentRecordsChunk082Chars ++ (momentRecordsChunk083Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 99) (SourceJson.white (momentRecordsChunk082Chars ++ (momentRecordsChunk083Chars ++ (tail)))) (momentRecordsChunk081Push (momentRecordsChunk080Push (acc))) := array_moment_records_chunk_081 fuel (momentRecordsChunk082Chars ++ (momentRecordsChunk083Chars ++ (tail))) (momentRecordsChunk080Push (acc))
    _ = SourceJson.array (fuel + 98) (SourceJson.white (momentRecordsChunk083Chars ++ (tail))) (momentRecordsChunk082Push (momentRecordsChunk081Push (momentRecordsChunk080Push (acc)))) := array_moment_records_chunk_082 fuel (momentRecordsChunk083Chars ++ (tail)) (momentRecordsChunk081Push (momentRecordsChunk080Push (acc)))
    _ = SourceJson.array (fuel + 97) (SourceJson.white tail) (momentRecordsBlock020Push acc) := array_moment_records_chunk_083 fuel (tail) (momentRecordsChunk082Push (momentRecordsChunk081Push (momentRecordsChunk080Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_020_before_raw_binding"
  err.flush

theorem moment_records_block_020_prefix :
    (momentRest01 41936).take 2092 = momentRecordsBlock020Chars := by rfl

theorem moment_records_block_020_split :
    momentRest01 41936 = momentRecordsBlock020Chars ++ momentRest01 44028 := by
  calc
    momentRest01 41936 =
        (momentRest01 41936).take 2092 ++ (momentRest01 41936).drop 2092 :=
      (List.take_append_drop 2092 (momentRest01 41936)).symm
    _ = momentRecordsBlock020Chars ++ (momentRest01 41936).drop 2092 :=
      congrArg (fun p => p ++ (momentRest01 41936).drop 2092) moment_records_block_020_prefix
    _ = momentRecordsBlock020Chars ++ momentRest01 44028 :=
      congrArg (fun rest => momentRecordsBlock020Chars ++ rest) (momentRest01_drop 41936 2092)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_020_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_020 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 101)
      (SourceJson.white (momentRest01 41936)) acc =
      SourceJson.array (fuel + 97) (SourceJson.white (momentRest01 44028)) (momentRecordsBlock020Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 101) (SourceJson.white s) acc)
      moment_records_block_020_split).trans (array_moment_records_block_020 fuel (momentRest01 44028) acc)

theorem moment_records_through_block_020 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 97) (SourceJson.white (momentRest01 44028)) momentRecordsAcc084 := by
  exact (moment_records_through_block_019 fuel).trans (array_moment_records_original_block_020 fuel momentRecordsAcc080)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_020_complete"
  err.flush

#print axioms array_moment_records_chunk_080
#print axioms array_moment_records_chunk_081
#print axioms array_moment_records_chunk_082
#print axioms array_moment_records_chunk_083
#print axioms array_moment_records_block_020
#print axioms moment_records_block_020_prefix
#print axioms moment_records_block_020_split
#print axioms array_moment_records_original_block_020
#print axioms moment_records_through_block_020

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
