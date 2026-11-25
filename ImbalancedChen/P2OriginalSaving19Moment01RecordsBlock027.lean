import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock026

/-! Original moment records block 27. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk108Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '0', '3', '1', '5', '8', '9', '4', '6', '3', '7', '8', '8', '8', '6', '2', '5', '2', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '2', '0', '6', '6', '9', '3', '7', '6', '6', '5', '1', '4', '0', '4', '6', '4', '1', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '7', '6', '1', '9', '7', '5', '4', '5', '0', '7', '3', '4', '8', '7', '3', '3', '2', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '5', '6', '0', '1', '9', '7', '2', '6', '9', '6', '6', '4', '5', '9', '5', '0', '8', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '4', '7', '7', '2', '7', '9', '8', '1', '7', '7', '5', '2', '0', '8', '2', '5', '3', '8', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '3', '4', '2', '7', '3', '0', '9', '3', '6', '2', '5', '2', '5', '2', '0', '7', '9', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '2', '4', '6', '0', '1', '5', '9', '8', '9', '1', '0', '3', '8', '8', '5', '6', '9', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '2', '4', '5', '8', '4', '5', '5', '8', '9', '1', '5', '0', '3', '9', '3', '1', '9', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '0', '0', '9', '2', '3', '3', '9', '1', '4', '0', '1', '3', '5', '5', '9', '2', '1', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '0', '1', '3', '6', '3', '5', '2', '2', '6', '2', '0', '6', '6', '0', '5', '9', '4', '6', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '9', '0', '0', '1', '2', '7', '7', '4', '4', '5', '9', '5', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '1', '0', '8', '9', '8', '5', '3', '4', '8', '5', '0', '2', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk108Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '0', '8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '1', '1', '0', '3', '1', '5', '8', '9', '4', '6', '3', '7', '8', '8', '8', '6', '2', '5', '2', '4', '3']), .str (String.ofList ['1', '1', '5', '2', '0', '6', '6', '9', '3', '7', '6', '6', '5', '1', '4', '0', '4', '6', '4', '1', '3', '5']), .str (String.ofList ['3', '3', '7', '6', '1', '9', '7', '5', '4', '5', '0', '7', '3', '4', '8', '7', '3', '3', '2', '2', '0']), .str (String.ofList ['6', '3', '5', '6', '0', '1', '9', '7', '2', '6', '9', '6', '6', '4', '5', '9', '5', '0', '8', '6', '4']), .str (String.ofList ['2', '1', '4', '7', '7', '2', '7', '9', '8', '1', '7', '7', '5', '2', '0', '8', '2', '5', '3', '8', '8', '0']), .str (String.ofList ['2', '4', '9', '3', '4', '2', '7', '3', '0', '9', '3', '6', '2', '5', '2', '5', '2', '0', '7', '9', '4', '9']), .str (String.ofList ['1', '3', '7', '2', '4', '6', '0', '1', '5', '9', '8', '9', '1', '0', '3', '8', '8', '5', '6', '9', '6', '5']), .str (String.ofList ['1', '0', '5', '2', '4', '5', '8', '4', '5', '5', '8', '9', '1', '5', '0', '3', '9', '3', '1', '9', '2', '2']), .str (String.ofList ['1', '1', '6', '0', '0', '9', '2', '3', '3', '9', '1', '4', '0', '1', '3', '5', '5', '9', '2', '1', '5', '1']), .str (String.ofList ['1', '1', '6', '0', '1', '3', '6', '3', '5', '2', '2', '6', '2', '0', '6', '6', '0', '5', '9', '4', '6', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '9', '9', '0', '0', '1', '2', '7', '7', '4', '4', '5', '9', '5', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '0', '1', '0', '8', '9', '8', '5', '3', '4', '8', '5', '0', '2', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_108_before_generic"
  err.flush

theorem array_moment_records_chunk_108 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 73)
      (SourceJson.white (momentRecordsChunk108Chars ++ tail)) acc =
      SourceJson.array (fuel + 72) (SourceJson.white tail) (momentRecordsChunk108Push acc) := by rfl

noncomputable def momentRecordsAcc109 : List SourceJson := momentRecordsChunk108Push momentRecordsAcc108

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_108_generic_complete"
  err.flush

noncomputable def momentRecordsChunk109Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '4', '4', '2', '8', '6', '1', '3', '7', '2', '5', '8', '9', '3', '3', '8', '2', '9', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '4', '3', '1', '4', '3', '8', '6', '9', '4', '3', '2', '0', '8', '3', '7', '6', '8', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '7', '0', '8', '7', '3', '7', '1', '2', '0', '3', '7', '6', '0', '0', '1', '1', '8', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '6', '2', '7', '0', '2', '3', '1', '3', '9', '9', '1', '1', '5', '4', '8', '0', '7', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '8', '4', '9', '1', '3', '5', '0', '4', '9', '5', '0', '1', '8', '6', '4', '4', '0', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '7', '2', '0', '7', '4', '3', '3', '8', '2', '8', '8', '8', '3', '9', '7', '6', '4', '1', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '0', '1', '2', '4', '3', '8', '6', '8', '4', '6', '0', '4', '6', '4', '0', '9', '0', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '8', '0', '1', '8', '6', '1', '5', '0', '1', '4', '2', '8', '2', '8', '6', '9', '3', '6', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '7', '1', '4', '2', '1', '6', '5', '3', '9', '7', '7', '8', '8', '3', '9', '2', '1', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '7', '2', '0', '1', '2', '0', '2', '7', '5', '9', '9', '5', '8', '2', '3', '4', '4', '5', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '3', '2', '7', '5', '5', '1', '2', '5', '5', '4', '2', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '3', '7', '8', '5', '1', '9', '7', '8', '7', '4', '0', '5', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk109Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '0', '9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '5', '1', '4', '4', '2', '8', '6', '1', '3', '7', '2', '5', '8', '9', '3', '3', '8', '2', '9', '4', '6']), .str (String.ofList ['1', '5', '8', '4', '3', '1', '4', '3', '8', '6', '9', '4', '3', '2', '0', '8', '3', '7', '6', '8', '6', '4']), .str (String.ofList ['3', '2', '7', '0', '8', '7', '3', '7', '1', '2', '0', '3', '7', '6', '0', '0', '1', '1', '8', '6', '1']), .str (String.ofList ['7', '1', '6', '2', '7', '0', '2', '3', '1', '3', '9', '9', '1', '1', '5', '4', '8', '0', '7', '8', '0']), .str (String.ofList ['2', '1', '7', '8', '4', '9', '1', '3', '5', '0', '4', '9', '5', '0', '1', '8', '6', '4', '4', '0', '3', '8']), .str (String.ofList ['2', '3', '7', '2', '0', '7', '4', '3', '3', '8', '2', '8', '8', '8', '3', '9', '7', '6', '4', '1', '1', '3']), .str (String.ofList ['1', '5', '4', '0', '1', '2', '4', '3', '8', '6', '8', '4', '6', '0', '4', '6', '4', '0', '9', '0', '6', '9']), .str (String.ofList ['1', '2', '4', '8', '0', '1', '8', '6', '1', '5', '0', '1', '4', '2', '8', '2', '8', '6', '9', '3', '6', '8']), .str (String.ofList ['1', '3', '3', '7', '1', '4', '2', '1', '6', '5', '3', '9', '7', '7', '8', '8', '3', '9', '2', '1', '7', '0']), .str (String.ofList ['1', '3', '3', '7', '2', '0', '1', '2', '0', '2', '7', '5', '9', '9', '5', '8', '2', '3', '4', '4', '5', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '3', '2', '7', '5', '5', '1', '2', '5', '5', '4', '2', '0', '6'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '3', '7', '8', '5', '1', '9', '7', '8', '7', '4', '0', '5', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_109_before_generic"
  err.flush

theorem array_moment_records_chunk_109 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 72)
      (SourceJson.white (momentRecordsChunk109Chars ++ tail)) acc =
      SourceJson.array (fuel + 71) (SourceJson.white tail) (momentRecordsChunk109Push acc) := by rfl

noncomputable def momentRecordsAcc110 : List SourceJson := momentRecordsChunk109Push momentRecordsAcc109

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_109_generic_complete"
  err.flush

noncomputable def momentRecordsChunk110Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '8', '8', '5', '5', '0', '6', '5', '8', '4', '0', '4', '7', '7', '4', '4', '0', '3', '3', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '3', '0', '3', '8', '6', '3', '0', '7', '3', '8', '0', '6', '6', '5', '7', '1', '5', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '9', '4', '5', '2', '2', '3', '3', '4', '0', '7', '1', '8', '7', '0', '3', '1', '1', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '1', '7', '3', '8', '3', '5', '8', '6', '2', '4', '7', '4', '2', '9', '5', '2', '3', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '6', '7', '1', '7', '6', '7', '5', '8', '1', '7', '9', '8', '6', '3', '6', '7', '0', '3', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '6', '7', '9', '2', '7', '6', '8', '5', '2', '8', '3', '8', '5', '3', '5', '7', '7', '5', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '5', '2', '5', '0', '7', '5', '7', '7', '1', '9', '5', '5', '9', '0', '0', '0', '6', '0', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '7', '5', '2', '8', '3', '5', '0', '5', '0', '3', '6', '4', '5', '2', '8', '9', '8', '2', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '0', '4', '0', '8', '1', '9', '0', '3', '4', '2', '8', '4', '5', '4', '2', '6', '7', '7', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '0', '4', '1', '5', '4', '5', '3', '3', '7', '1', '1', '6', '9', '7', '2', '7', '0', '7', '7', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '8', '9', '7', '0', '9', '8', '3', '2', '7', '8', '3', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '0', '2', '8', '2', '6', '4', '5', '7', '1', '1', '9', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk110Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '1', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '9', '8', '8', '5', '5', '0', '6', '5', '8', '4', '0', '4', '7', '7', '4', '4', '0', '3', '3', '7', '6']), .str (String.ofList ['2', '0', '8', '3', '0', '3', '8', '6', '3', '0', '7', '3', '8', '0', '6', '6', '5', '7', '1', '5', '9', '5']), .str (String.ofList ['3', '0', '9', '4', '5', '2', '2', '3', '3', '4', '0', '7', '1', '8', '7', '0', '3', '1', '1', '9', '6']), .str (String.ofList ['7', '9', '1', '7', '3', '8', '3', '5', '8', '6', '2', '4', '7', '4', '2', '9', '5', '2', '3', '5', '6']), .str (String.ofList ['2', '1', '6', '7', '1', '7', '6', '7', '5', '8', '1', '7', '9', '8', '6', '3', '6', '7', '0', '3', '5', '9']), .str (String.ofList ['2', '3', '6', '7', '9', '2', '7', '6', '8', '5', '2', '8', '3', '8', '5', '3', '5', '7', '7', '5', '1', '8']), .str (String.ofList ['1', '7', '2', '5', '2', '5', '0', '7', '5', '7', '7', '1', '9', '5', '5', '9', '0', '0', '0', '6', '0', '3']), .str (String.ofList ['1', '4', '7', '5', '2', '8', '3', '5', '0', '5', '0', '3', '6', '4', '5', '2', '8', '9', '8', '2', '1', '5']), .str (String.ofList ['1', '5', '0', '4', '0', '8', '1', '9', '0', '3', '4', '2', '8', '4', '5', '4', '2', '6', '7', '7', '4', '3']), .str (String.ofList ['1', '5', '0', '4', '1', '5', '4', '5', '3', '3', '7', '1', '1', '6', '9', '7', '2', '7', '0', '7', '7', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '8', '9', '7', '0', '9', '8', '3', '2', '7', '8', '3', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '0', '2', '8', '2', '6', '4', '5', '7', '1', '1', '9', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_110_before_generic"
  err.flush

theorem array_moment_records_chunk_110 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 71)
      (SourceJson.white (momentRecordsChunk110Chars ++ tail)) acc =
      SourceJson.array (fuel + 70) (SourceJson.white tail) (momentRecordsChunk110Push acc) := by rfl

noncomputable def momentRecordsAcc111 : List SourceJson := momentRecordsChunk110Push momentRecordsAcc110

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_110_generic_complete"
  err.flush

noncomputable def momentRecordsChunk111Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '7', '3', '4', '4', '9', '1', '5', '2', '8', '4', '7', '9', '1', '2', '1', '9', '4', '2', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '2', '1', '2', '8', '7', '5', '8', '3', '8', '5', '9', '0', '2', '0', '5', '7', '8', '9', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '6', '9', '7', '0', '2', '2', '2', '6', '6', '8', '1', '4', '7', '4', '9', '3', '7', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '3', '8', '9', '1', '3', '1', '7', '5', '4', '8', '4', '5', '2', '5', '1', '1', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '4', '9', '6', '2', '8', '6', '4', '9', '4', '6', '1', '3', '5', '3', '5', '4', '9', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '3', '4', '2', '7', '2', '5', '1', '6', '8', '2', '7', '9', '0', '6', '6', '7', '6', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '5', '3', '2', '7', '9', '9', '9', '0', '0', '8', '0', '7', '9', '1', '4', '6', '3', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '6', '1', '1', '6', '5', '9', '6', '4', '4', '4', '7', '6', '0', '5', '0', '5', '2', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '2', '8', '6', '1', '5', '7', '4', '2', '4', '5', '8', '4', '2', '0', '6', '0', '8', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '2', '9', '4', '8', '0', '2', '4', '6', '1', '0', '2', '8', '9', '5', '6', '3', '7', '0', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '0', '0', '8', '2', '8', '3', '8', '1', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '3', '5', '2', '1', '9', '5', '3', '1', '4', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk111Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '1', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '2', '7', '3', '4', '4', '9', '1', '5', '2', '8', '4', '7', '9', '1', '2', '1', '9', '4', '2', '8', '7']), .str (String.ofList ['2', '2', '2', '1', '2', '8', '7', '5', '8', '3', '8', '5', '9', '0', '2', '0', '5', '7', '8', '9', '1', '5']), .str (String.ofList ['2', '3', '6', '9', '7', '0', '2', '2', '2', '6', '6', '8', '1', '4', '7', '4', '9', '3', '7', '6', '7']), .str (String.ofList ['9', '0', '9', '3', '8', '9', '1', '3', '1', '7', '5', '4', '8', '4', '5', '2', '5', '1', '1', '6', '0']), .str (String.ofList ['1', '6', '7', '4', '9', '6', '2', '8', '6', '4', '9', '4', '6', '1', '3', '5', '3', '5', '4', '9', '7', '6']), .str (String.ofList ['2', '3', '9', '3', '4', '2', '7', '2', '5', '1', '6', '8', '2', '7', '9', '0', '6', '6', '7', '6', '1', '7']), .str (String.ofList ['1', '6', '0', '5', '3', '2', '7', '9', '9', '9', '0', '0', '8', '0', '7', '9', '1', '4', '6', '3', '8', '7']), .str (String.ofList ['1', '4', '3', '6', '1', '1', '6', '5', '9', '6', '4', '4', '4', '7', '6', '0', '5', '0', '5', '2', '7', '5']), .str (String.ofList ['1', '2', '7', '2', '8', '6', '1', '5', '7', '4', '2', '4', '5', '8', '4', '2', '0', '6', '0', '8', '3', '6']), .str (String.ofList ['1', '2', '7', '2', '9', '4', '8', '0', '2', '4', '6', '1', '0', '2', '8', '9', '5', '6', '3', '7', '0', '4'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '7', '0', '0', '8', '2', '8', '3', '8', '1', '8', '6'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '7', '3', '5', '2', '1', '9', '5', '3', '1', '4', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_111_before_generic"
  err.flush

theorem array_moment_records_chunk_111 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 70)
      (SourceJson.white (momentRecordsChunk111Chars ++ tail)) acc =
      SourceJson.array (fuel + 69) (SourceJson.white tail) (momentRecordsChunk111Push acc) := by rfl

noncomputable def momentRecordsAcc112 : List SourceJson := momentRecordsChunk111Push momentRecordsAcc111

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_111_generic_complete"
  err.flush

noncomputable def momentRecordsBlock027Chars : List Char := momentRecordsChunk108Chars ++ momentRecordsChunk109Chars ++ momentRecordsChunk110Chars ++ momentRecordsChunk111Chars
noncomputable def momentRecordsBlock027Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk111Push (momentRecordsChunk110Push (momentRecordsChunk109Push (momentRecordsChunk108Push (acc))))

theorem array_moment_records_block_027 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 73)
      (SourceJson.white (momentRecordsBlock027Chars ++ tail)) acc =
      SourceJson.array (fuel + 69) (SourceJson.white tail) (momentRecordsBlock027Push acc) := by
  have hinput : momentRecordsBlock027Chars ++ tail = momentRecordsChunk108Chars ++ (momentRecordsChunk109Chars ++ (momentRecordsChunk110Chars ++ (momentRecordsChunk111Chars ++ (tail)))) := by
    simp only [momentRecordsBlock027Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 73) (SourceJson.white (momentRecordsBlock027Chars ++ tail)) acc =
        SourceJson.array (fuel + 73) (SourceJson.white (momentRecordsChunk108Chars ++ (momentRecordsChunk109Chars ++ (momentRecordsChunk110Chars ++ (momentRecordsChunk111Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 73) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 72) (SourceJson.white (momentRecordsChunk109Chars ++ (momentRecordsChunk110Chars ++ (momentRecordsChunk111Chars ++ (tail))))) (momentRecordsChunk108Push (acc)) := array_moment_records_chunk_108 fuel (momentRecordsChunk109Chars ++ (momentRecordsChunk110Chars ++ (momentRecordsChunk111Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 71) (SourceJson.white (momentRecordsChunk110Chars ++ (momentRecordsChunk111Chars ++ (tail)))) (momentRecordsChunk109Push (momentRecordsChunk108Push (acc))) := array_moment_records_chunk_109 fuel (momentRecordsChunk110Chars ++ (momentRecordsChunk111Chars ++ (tail))) (momentRecordsChunk108Push (acc))
    _ = SourceJson.array (fuel + 70) (SourceJson.white (momentRecordsChunk111Chars ++ (tail))) (momentRecordsChunk110Push (momentRecordsChunk109Push (momentRecordsChunk108Push (acc)))) := array_moment_records_chunk_110 fuel (momentRecordsChunk111Chars ++ (tail)) (momentRecordsChunk109Push (momentRecordsChunk108Push (acc)))
    _ = SourceJson.array (fuel + 69) (SourceJson.white tail) (momentRecordsBlock027Push acc) := array_moment_records_chunk_111 fuel (tail) (momentRecordsChunk110Push (momentRecordsChunk109Push (momentRecordsChunk108Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_027_before_raw_binding"
  err.flush

theorem moment_records_block_027_prefix :
    (momentRest01 56539).take 2073 = momentRecordsBlock027Chars := by rfl

theorem moment_records_block_027_split :
    momentRest01 56539 = momentRecordsBlock027Chars ++ momentRest01 58612 := by
  calc
    momentRest01 56539 =
        (momentRest01 56539).take 2073 ++ (momentRest01 56539).drop 2073 :=
      (List.take_append_drop 2073 (momentRest01 56539)).symm
    _ = momentRecordsBlock027Chars ++ (momentRest01 56539).drop 2073 :=
      congrArg (fun p => p ++ (momentRest01 56539).drop 2073) moment_records_block_027_prefix
    _ = momentRecordsBlock027Chars ++ momentRest01 58612 :=
      congrArg (fun rest => momentRecordsBlock027Chars ++ rest) (momentRest01_drop 56539 2073)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_027_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_027 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 73)
      (SourceJson.white (momentRest01 56539)) acc =
      SourceJson.array (fuel + 69) (SourceJson.white (momentRest01 58612)) (momentRecordsBlock027Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 73) (SourceJson.white s) acc)
      moment_records_block_027_split).trans (array_moment_records_block_027 fuel (momentRest01 58612) acc)

theorem moment_records_through_block_027 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 69) (SourceJson.white (momentRest01 58612)) momentRecordsAcc112 := by
  exact (moment_records_through_block_026 fuel).trans (array_moment_records_original_block_027 fuel momentRecordsAcc108)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_027_complete"
  err.flush

#print axioms array_moment_records_chunk_108
#print axioms array_moment_records_chunk_109
#print axioms array_moment_records_chunk_110
#print axioms array_moment_records_chunk_111
#print axioms array_moment_records_block_027
#print axioms moment_records_block_027_prefix
#print axioms moment_records_block_027_split
#print axioms array_moment_records_original_block_027
#print axioms moment_records_through_block_027

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
