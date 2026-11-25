import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock034

/-! Original moment records block 35. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk140Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '4', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '4', '3', '0', '7', '3', '0', '6', '4', '4', '1', '9', '9', '5', '9', '5', '4', '6', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '4', '0', '9', '3', '3', '7', '1', '0', '9', '8', '9', '0', '0', '7', '2', '1', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '9', '6', '9', '8', '6', '0', '5', '0', '1', '1', '2', '5', '6', '5', '5', '5', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '2', '8', '3', '4', '4', '0', '7', '1', '2', '6', '1', '2', '0', '2', '0', '0', '5', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '8', '5', '2', '1', '6', '9', '5', '8', '9', '6', '3', '7', '0', '6', '9', '3', '6', '7', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '8', '0', '3', '9', '5', '9', '5', '3', '6', '3', '7', '7', '8', '1', '6', '7', '5', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '7', '1', '8', '5', '3', '3', '2', '0', '1', '5', '2', '9', '8', '6', '9', '0', '6', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '7', '7', '3', '3', '5', '6', '6', '3', '3', '6', '1', '6', '1', '6', '5', '1', '7', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '6', '8', '9', '6', '1', '3', '9', '0', '8', '0', '1', '2', '7', '0', '5', '8', '0', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '4', '7', '0', '7', '7', '0', '5', '1', '9', '4', '2', '2', '9', '2', '4', '6', '0', '9', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '8', '0', '1', '8', '0', '7', '4', '5', '2', '1', '3', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '9', '3', '1', '5', '6', '3', '8', '6', '8', '6', '8', '7', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk140Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '4', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['6', '7', '4', '3', '0', '7', '3', '0', '6', '4', '4', '1', '9', '9', '5', '9', '5', '4', '6', '6', '7']), .str (String.ofList ['6', '6', '4', '0', '9', '3', '3', '7', '1', '0', '9', '8', '9', '0', '0', '7', '2', '1', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '9', '6', '9', '8', '6', '0', '5', '0', '1', '1', '2', '5', '6', '5', '5', '5', '6', '9']), .str (String.ofList ['5', '6', '2', '8', '3', '4', '4', '0', '7', '1', '2', '6', '1', '2', '0', '2', '0', '0', '5', '9', '3']), .str (String.ofList ['4', '5', '8', '5', '2', '1', '6', '9', '5', '8', '9', '6', '3', '7', '0', '6', '9', '3', '6', '7', '7']), .str (String.ofList ['9', '6', '8', '0', '3', '9', '5', '9', '5', '3', '6', '3', '7', '7', '8', '1', '6', '7', '5', '1', '4']), .str (String.ofList ['7', '9', '7', '1', '8', '5', '3', '3', '2', '0', '1', '5', '2', '9', '8', '6', '9', '0', '6', '6', '2']), .str (String.ofList ['7', '2', '7', '7', '3', '3', '5', '6', '6', '3', '3', '6', '1', '6', '1', '6', '5', '1', '7', '6', '4']), .str (String.ofList ['6', '8', '6', '8', '9', '6', '1', '3', '9', '0', '8', '0', '1', '2', '7', '0', '5', '8', '0', '6', '9']), .str (String.ofList ['6', '6', '4', '7', '0', '7', '7', '0', '5', '1', '9', '4', '2', '2', '9', '2', '4', '6', '0', '9', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '4', '8', '0', '1', '8', '0', '7', '4', '5', '2', '1', '3', '0', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '4', '9', '3', '1', '5', '6', '3', '8', '6', '8', '6', '8', '7', '8']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_140_before_generic"
  err.flush

theorem array_moment_records_chunk_140 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 41)
      (SourceJson.white (momentRecordsChunk140Chars ++ tail)) acc =
      SourceJson.array (fuel + 40) (SourceJson.white tail) (momentRecordsChunk140Push acc) := by rfl

noncomputable def momentRecordsAcc141 : List SourceJson := momentRecordsChunk140Push momentRecordsAcc140

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_140_generic_complete"
  err.flush

noncomputable def momentRecordsChunk141Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '4', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '2', '3', '3', '7', '8', '3', '7', '9', '5', '2', '5', '0', '7', '2', '3', '1', '1', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '0', '1', '7', '0', '5', '0', '3', '8', '5', '5', '4', '3', '1', '5', '9', '6', '4', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '4', '1', '2', '1', '9', '0', '5', '9', '5', '8', '4', '8', '7', '1', '2', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '3', '4', '0', '4', '6', '5', '4', '9', '3', '0', '2', '7', '7', '5', '2', '1', '1', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '6', '8', '3', '0', '3', '6', '9', '6', '8', '7', '4', '0', '3', '2', '6', '5', '3', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '1', '2', '3', '4', '1', '3', '1', '7', '4', '8', '5', '6', '5', '3', '1', '5', '9', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '7', '4', '9', '0', '2', '6', '8', '8', '4', '0', '8', '6', '7', '0', '8', '4', '7', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '5', '2', '9', '0', '1', '9', '2', '0', '2', '2', '0', '8', '3', '1', '6', '7', '7', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '5', '2', '8', '8', '2', '3', '8', '4', '6', '6', '1', '5', '5', '7', '5', '5', '0', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '6', '6', '4', '1', '2', '0', '9', '7', '6', '3', '1', '6', '8', '9', '2', '0', '3', '8', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '6', '0', '1', '3', '2', '9', '8', '2', '8', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '6', '1', '5', '1', '5', '3', '0', '2', '8', '2', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk141Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '4', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['6', '7', '2', '3', '3', '7', '8', '3', '7', '9', '5', '2', '5', '0', '7', '2', '3', '1', '1', '7', '3']), .str (String.ofList ['6', '6', '0', '1', '7', '0', '5', '0', '3', '8', '5', '5', '4', '3', '1', '5', '9', '6', '4', '5', '3']), .str (String.ofList ['1', '0', '8', '4', '1', '2', '1', '9', '0', '5', '9', '5', '8', '4', '8', '7', '1', '2', '0', '0', '0']), .str (String.ofList ['5', '4', '3', '4', '0', '4', '6', '5', '4', '9', '3', '0', '2', '7', '7', '5', '2', '1', '1', '0', '2']), .str (String.ofList ['4', '4', '6', '8', '3', '0', '3', '6', '9', '6', '8', '7', '4', '0', '3', '2', '6', '5', '3', '1', '3']), .str (String.ofList ['1', '0', '2', '1', '2', '3', '4', '1', '3', '1', '7', '4', '8', '5', '6', '5', '3', '1', '5', '9', '8', '4']), .str (String.ofList ['8', '3', '7', '4', '9', '0', '2', '6', '8', '8', '4', '0', '8', '6', '7', '0', '8', '4', '7', '3', '5']), .str (String.ofList ['6', '8', '5', '2', '9', '0', '1', '9', '2', '0', '2', '2', '0', '8', '3', '1', '6', '7', '7', '0', '5']), .str (String.ofList ['6', '8', '5', '2', '8', '8', '2', '3', '8', '4', '6', '6', '1', '5', '5', '7', '5', '5', '0', '9', '0']), .str (String.ofList ['7', '4', '6', '6', '4', '1', '2', '0', '9', '7', '6', '3', '1', '6', '8', '9', '2', '0', '3', '8', '0'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '6', '0', '1', '3', '2', '9', '8', '2', '8', '2', '6'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '6', '1', '5', '1', '5', '3', '0', '2', '8', '2', '6']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_141_before_generic"
  err.flush

theorem array_moment_records_chunk_141 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 40)
      (SourceJson.white (momentRecordsChunk141Chars ++ tail)) acc =
      SourceJson.array (fuel + 39) (SourceJson.white tail) (momentRecordsChunk141Push acc) := by rfl

noncomputable def momentRecordsAcc142 : List SourceJson := momentRecordsChunk141Push momentRecordsAcc141

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_141_generic_complete"
  err.flush

noncomputable def momentRecordsChunk142Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '4', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '8', '2', '1', '2', '6', '0', '0', '3', '2', '9', '6', '5', '7', '3', '6', '8', '0', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '8', '1', '2', '7', '2', '1', '0', '7', '5', '0', '4', '8', '9', '2', '5', '8', '4', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '3', '4', '6', '3', '5', '6', '9', '1', '9', '4', '3', '7', '7', '1', '0', '6', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '9', '2', '1', '0', '4', '9', '6', '9', '8', '4', '8', '0', '1', '5', '3', '5', '0', '6', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '4', '9', '1', '0', '5', '4', '7', '9', '3', '6', '3', '1', '4', '5', '8', '2', '5', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '3', '8', '8', '4', '7', '1', '3', '9', '3', '2', '5', '2', '1', '0', '7', '4', '7', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '0', '6', '7', '5', '5', '8', '7', '2', '5', '8', '7', '9', '7', '0', '9', '7', '2', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '3', '6', '6', '3', '3', '8', '0', '1', '2', '9', '7', '1', '6', '8', '9', '7', '2', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '1', '9', '2', '7', '4', '9', '4', '9', '8', '4', '4', '9', '8', '7', '6', '5', '0', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '1', '9', '8', '2', '4', '0', '6', '4', '0', '8', '4', '5', '1', '9', '2', '8', '0', '7', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '1', '3', '9', '2', '5', '3', '9', '7', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '1', '6', '1', '2', '9', '7', '1', '9', '3', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk142Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '4', '2'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['6', '7', '8', '2', '1', '2', '6', '0', '0', '3', '2', '9', '6', '5', '7', '3', '6', '8', '0', '5', '9']), .str (String.ofList ['6', '6', '8', '1', '2', '7', '2', '1', '0', '7', '5', '0', '4', '8', '9', '2', '5', '8', '4', '9', '5']), .str (String.ofList ['9', '8', '3', '4', '6', '3', '5', '6', '9', '1', '9', '4', '3', '7', '7', '1', '0', '6', '3', '1']), .str (String.ofList ['5', '5', '9', '2', '1', '0', '4', '9', '6', '9', '8', '4', '8', '0', '1', '5', '3', '5', '0', '6', '6']), .str (String.ofList ['5', '5', '4', '9', '1', '0', '5', '4', '7', '9', '3', '6', '3', '1', '4', '5', '8', '2', '5', '6', '3']), .str (String.ofList ['9', '6', '3', '8', '8', '4', '7', '1', '3', '9', '3', '2', '5', '2', '1', '0', '7', '4', '7', '6', '7']), .str (String.ofList ['8', '0', '0', '6', '7', '5', '5', '8', '7', '2', '5', '8', '7', '9', '7', '0', '9', '7', '2', '7', '3']), .str (String.ofList ['7', '3', '3', '6', '6', '3', '3', '8', '0', '1', '2', '9', '7', '1', '6', '8', '9', '7', '2', '4', '9']), .str (String.ofList ['6', '8', '1', '9', '2', '7', '4', '9', '4', '9', '8', '4', '4', '9', '8', '7', '6', '5', '0', '6', '0']), .str (String.ofList ['6', '8', '1', '9', '8', '2', '4', '0', '6', '4', '0', '8', '4', '5', '1', '9', '2', '8', '0', '7', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '1', '3', '9', '2', '5', '3', '9', '7', '9', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '1', '6', '1', '2', '9', '7', '1', '9', '3', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_142_before_generic"
  err.flush

theorem array_moment_records_chunk_142 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 39)
      (SourceJson.white (momentRecordsChunk142Chars ++ tail)) acc =
      SourceJson.array (fuel + 38) (SourceJson.white tail) (momentRecordsChunk142Push acc) := by rfl

noncomputable def momentRecordsAcc143 : List SourceJson := momentRecordsChunk142Push momentRecordsAcc142

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_142_generic_complete"
  err.flush

noncomputable def momentRecordsChunk143Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '4', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '0', '7', '9', '4', '3', '1', '2', '3', '2', '5', '4', '9', '1', '7', '5', '0', '8', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '5', '5', '5', '5', '6', '6', '3', '3', '9', '6', '3', '0', '4', '6', '6', '1', '6', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '2', '6', '0', '6', '3', '2', '3', '5', '4', '1', '0', '1', '1', '4', '4', '0', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '7', '0', '5', '6', '6', '6', '3', '0', '4', '0', '7', '1', '1', '3', '4', '4', '9', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '8', '8', '2', '1', '7', '0', '6', '7', '5', '4', '6', '8', '9', '6', '4', '8', '6', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '8', '5', '3', '7', '7', '5', '0', '9', '6', '2', '8', '5', '5', '3', '5', '8', '9', '3', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '6', '5', '9', '2', '8', '5', '0', '4', '4', '2', '2', '1', '1', '7', '8', '4', '1', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '2', '3', '0', '2', '7', '2', '2', '8', '3', '0', '6', '9', '9', '6', '0', '6', '1', '4', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '2', '6', '7', '9', '9', '3', '7', '7', '3', '5', '9', '9', '2', '4', '1', '1', '2', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '2', '7', '4', '0', '1', '2', '3', '3', '0', '4', '5', '5', '1', '0', '5', '9', '8', '1', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '2', '4', '4', '2', '9', '8', '6', '8', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '2', '6', '8', '8', '2', '3', '2', '0', '1', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', '\r', '\n', ' ', ' ', ']']
noncomputable def momentRecordsChunk143Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '4', '3'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['8', '9', '0', '7', '9', '4', '3', '1', '2', '3', '2', '5', '4', '9', '1', '7', '5', '0', '8', '9', '3']), .str (String.ofList ['8', '8', '5', '5', '5', '5', '6', '6', '3', '3', '9', '6', '3', '0', '4', '6', '6', '1', '6', '3', '8']), .str (String.ofList ['1', '0', '0', '2', '6', '0', '6', '3', '2', '3', '5', '4', '1', '0', '1', '1', '4', '4', '0', '5', '3']), .str (String.ofList ['5', '5', '7', '0', '5', '6', '6', '6', '3', '0', '4', '0', '7', '1', '1', '3', '4', '4', '9', '9', '5']), .str (String.ofList ['6', '5', '8', '8', '2', '1', '7', '0', '6', '7', '5', '4', '6', '8', '9', '6', '4', '8', '6', '3', '7']), .str (String.ofList ['9', '8', '8', '5', '3', '7', '7', '5', '0', '9', '6', '2', '8', '5', '5', '3', '5', '8', '9', '3', '3']), .str (String.ofList ['8', '0', '6', '5', '9', '2', '8', '5', '0', '4', '4', '2', '2', '1', '1', '7', '8', '4', '1', '5', '9']), .str (String.ofList ['7', '3', '2', '3', '0', '2', '7', '2', '2', '8', '3', '0', '6', '9', '9', '6', '0', '6', '1', '4', '0']), .str (String.ofList ['6', '7', '2', '6', '7', '9', '9', '3', '7', '7', '3', '5', '9', '9', '2', '4', '1', '1', '2', '6', '1']), .str (String.ofList ['6', '7', '2', '7', '4', '0', '1', '2', '3', '3', '0', '4', '5', '5', '1', '0', '5', '9', '8', '1', '2'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '2', '4', '4', '2', '9', '8', '6', '8', '4', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '2', '6', '8', '8', '2', '3', '2', '0', '1', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_143_before_generic"
  err.flush

theorem array_moment_records_chunk_143 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 38)
      (SourceJson.white (momentRecordsChunk143Chars ++ tail)) acc =
      .ok (.arr ((momentRecordsChunk143Push acc).reverse), tail) := by rfl

noncomputable def momentRecordsAcc144 : List SourceJson := momentRecordsChunk143Push momentRecordsAcc143

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_143_generic_complete"
  err.flush

noncomputable def momentRecordsBlock035Chars : List Char := momentRecordsChunk140Chars ++ momentRecordsChunk141Chars ++ momentRecordsChunk142Chars ++ momentRecordsChunk143Chars
noncomputable def momentRecordsBlock035Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk143Push (momentRecordsChunk142Push (momentRecordsChunk141Push (momentRecordsChunk140Push (acc))))

theorem array_moment_records_block_035 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 41)
      (SourceJson.white (momentRecordsBlock035Chars ++ tail)) acc =
      .ok (.arr ((momentRecordsBlock035Push acc).reverse), tail) := by
  have hinput : momentRecordsBlock035Chars ++ tail = momentRecordsChunk140Chars ++ (momentRecordsChunk141Chars ++ (momentRecordsChunk142Chars ++ (momentRecordsChunk143Chars ++ (tail)))) := by
    simp only [momentRecordsBlock035Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 41) (SourceJson.white (momentRecordsBlock035Chars ++ tail)) acc =
        SourceJson.array (fuel + 41) (SourceJson.white (momentRecordsChunk140Chars ++ (momentRecordsChunk141Chars ++ (momentRecordsChunk142Chars ++ (momentRecordsChunk143Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 41) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 40) (SourceJson.white (momentRecordsChunk141Chars ++ (momentRecordsChunk142Chars ++ (momentRecordsChunk143Chars ++ (tail))))) (momentRecordsChunk140Push (acc)) := array_moment_records_chunk_140 fuel (momentRecordsChunk141Chars ++ (momentRecordsChunk142Chars ++ (momentRecordsChunk143Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 39) (SourceJson.white (momentRecordsChunk142Chars ++ (momentRecordsChunk143Chars ++ (tail)))) (momentRecordsChunk141Push (momentRecordsChunk140Push (acc))) := array_moment_records_chunk_141 fuel (momentRecordsChunk142Chars ++ (momentRecordsChunk143Chars ++ (tail))) (momentRecordsChunk140Push (acc))
    _ = SourceJson.array (fuel + 38) (SourceJson.white (momentRecordsChunk143Chars ++ (tail))) (momentRecordsChunk142Push (momentRecordsChunk141Push (momentRecordsChunk140Push (acc)))) := array_moment_records_chunk_142 fuel (momentRecordsChunk143Chars ++ (tail)) (momentRecordsChunk141Push (momentRecordsChunk140Push (acc)))
    _ = .ok (.arr ((momentRecordsBlock035Push acc).reverse), tail) := array_moment_records_chunk_143 fuel (tail) (momentRecordsChunk142Push (momentRecordsChunk141Push (momentRecordsChunk140Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_035_before_raw_binding"
  err.flush

theorem moment_records_block_035_prefix :
    (momentRest01 73055).take 2034 = momentRecordsBlock035Chars := by rfl

theorem moment_records_block_035_split :
    momentRest01 73055 = momentRecordsBlock035Chars ++ momentRest01 75089 := by
  calc
    momentRest01 73055 =
        (momentRest01 73055).take 2034 ++ (momentRest01 73055).drop 2034 :=
      (List.take_append_drop 2034 (momentRest01 73055)).symm
    _ = momentRecordsBlock035Chars ++ (momentRest01 73055).drop 2034 :=
      congrArg (fun p => p ++ (momentRest01 73055).drop 2034) moment_records_block_035_prefix
    _ = momentRecordsBlock035Chars ++ momentRest01 75089 :=
      congrArg (fun rest => momentRecordsBlock035Chars ++ rest) (momentRest01_drop 73055 2034)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_035_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_035 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 41)
      (SourceJson.white (momentRest01 73055)) acc =
      .ok (.arr ((momentRecordsBlock035Push acc).reverse), momentRest01 75089) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 41) (SourceJson.white s) acc)
      moment_records_block_035_split).trans (array_moment_records_block_035 fuel (momentRest01 75089) acc)

noncomputable def momentRecordsArrayValue : SourceJson := .arr (momentRecordsAcc144.reverse)

theorem moment_records_through_block_035 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      .ok (momentRecordsArrayValue, momentRest01 75089) := by
  exact (moment_records_through_block_034 fuel).trans (array_moment_records_original_block_035 fuel momentRecordsAcc140)

theorem value_moment_records_original (fuel : Nat) :
    SourceJson.value (fuel + 182) (momentRest01 363) =
      .ok (momentRecordsArrayValue, momentRest01 75089) := by
  exact (value_moment_records_open fuel).trans (moment_records_through_block_035 fuel)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_035_complete"
  err.flush

#print axioms array_moment_records_chunk_140
#print axioms array_moment_records_chunk_141
#print axioms array_moment_records_chunk_142
#print axioms array_moment_records_chunk_143
#print axioms array_moment_records_block_035
#print axioms moment_records_block_035_prefix
#print axioms moment_records_block_035_split
#print axioms array_moment_records_original_block_035
#print axioms moment_records_through_block_035
#print axioms value_moment_records_original

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
