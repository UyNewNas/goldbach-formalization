import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock014

/-! Original moment records block 15. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk060Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '5', '9', '0', '4', '0', '7', '4', '6', '4', '8', '2', '0', '0', '9', '3', '8', '3', '2', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '3', '4', '7', '2', '3', '8', '0', '7', '8', '3', '9', '4', '9', '0', '7', '3', '9', '4', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '3', '6', '6', '4', '0', '8', '8', '6', '6', '6', '9', '4', '3', '2', '6', '8', '7', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '6', '6', '1', '7', '5', '3', '3', '6', '2', '0', '7', '5', '8', '2', '5', '5', '6', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '4', '9', '8', '2', '2', '0', '7', '5', '1', '6', '2', '7', '3', '0', '7', '2', '6', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '1', '6', '5', '6', '2', '9', '6', '9', '0', '3', '3', '5', '8', '0', '1', '1', '4', '7', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '6', '4', '0', '0', '5', '2', '7', '7', '2', '0', '1', '7', '1', '8', '8', '3', '9', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '5', '8', '4', '7', '4', '1', '8', '9', '3', '1', '3', '3', '6', '0', '0', '7', '3', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '0', '9', '3', '0', '8', '4', '7', '1', '1', '4', '3', '6', '6', '4', '0', '3', '7', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '0', '9', '0', '5', '7', '2', '2', '3', '8', '9', '4', '5', '8', '6', '9', '9', '4', '4', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '9', '6', '8', '6', '6', '9', '7', '4', '4', '9', '8', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '0', '5', '5', '7', '3', '5', '8', '4', '5', '1', '0', '3', '2', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk060Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['6', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '3', '5', '9', '0', '4', '0', '7', '4', '6', '4', '8', '2', '0', '0', '9', '3', '8', '3', '2', '5', '0']), .str (String.ofList ['2', '5', '3', '4', '7', '2', '3', '8', '0', '7', '8', '3', '9', '4', '9', '0', '7', '3', '9', '4', '8', '1']), .str (String.ofList ['2', '6', '3', '6', '6', '4', '0', '8', '8', '6', '6', '6', '9', '4', '3', '2', '6', '8', '7', '4', '5']), .str (String.ofList ['3', '3', '6', '6', '1', '7', '5', '3', '3', '6', '2', '0', '7', '5', '8', '2', '5', '5', '6', '5', '7']), .str (String.ofList ['6', '4', '4', '9', '8', '2', '2', '0', '7', '5', '1', '6', '2', '7', '3', '0', '7', '2', '6', '0', '8']), .str (String.ofList ['1', '9', '1', '6', '5', '6', '2', '9', '6', '9', '0', '3', '3', '5', '8', '0', '1', '1', '4', '7', '4', '9']), .str (String.ofList ['9', '4', '6', '4', '0', '0', '5', '2', '7', '7', '2', '0', '1', '7', '1', '8', '8', '3', '9', '3', '4']), .str (String.ofList ['7', '8', '5', '8', '4', '7', '4', '1', '8', '9', '3', '1', '3', '3', '6', '0', '0', '7', '3', '0', '7']), .str (String.ofList ['1', '0', '1', '0', '9', '3', '0', '8', '4', '7', '1', '1', '4', '3', '6', '6', '4', '0', '3', '7', '6', '5']), .str (String.ofList ['1', '0', '1', '0', '9', '0', '5', '7', '2', '2', '3', '8', '9', '4', '5', '8', '6', '9', '9', '4', '4', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '9', '9', '6', '8', '6', '6', '9', '7', '4', '4', '9', '8', '9', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '0', '5', '5', '7', '3', '5', '8', '4', '5', '1', '0', '3', '2', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_060_before_generic"
  err.flush

theorem array_moment_records_chunk_060 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 121)
      (SourceJson.white (momentRecordsChunk060Chars ++ tail)) acc =
      SourceJson.array (fuel + 120) (SourceJson.white tail) (momentRecordsChunk060Push acc) := by rfl

noncomputable def momentRecordsAcc061 : List SourceJson := momentRecordsChunk060Push momentRecordsAcc060

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_060_generic_complete"
  err.flush

noncomputable def momentRecordsChunk061Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '2', '1', '2', '7', '4', '0', '3', '4', '9', '4', '0', '3', '1', '8', '3', '7', '9', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '9', '2', '9', '4', '0', '8', '5', '7', '5', '4', '0', '6', '3', '1', '5', '7', '2', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '8', '6', '2', '5', '9', '6', '3', '3', '4', '7', '2', '4', '5', '2', '9', '8', '5', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '6', '1', '7', '4', '9', '7', '6', '4', '4', '3', '4', '9', '7', '1', '0', '7', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '1', '8', '8', '3', '9', '0', '1', '9', '4', '0', '1', '6', '8', '6', '9', '2', '5', '8', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '1', '6', '0', '9', '3', '2', '2', '9', '1', '0', '1', '5', '9', '2', '1', '2', '7', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '4', '4', '6', '4', '8', '9', '8', '1', '6', '7', '9', '5', '8', '8', '2', '1', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '4', '2', '5', '1', '8', '0', '3', '3', '7', '3', '1', '3', '9', '5', '7', '0', '5', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '9', '5', '9', '3', '8', '9', '9', '3', '1', '2', '1', '9', '9', '9', '4', '7', '8', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '9', '5', '6', '2', '5', '2', '2', '2', '5', '3', '9', '7', '0', '8', '8', '0', '9', '1', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '5', '3', '3', '8', '8', '6', '9', '9', '8', '7', '7', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '8', '0', '1', '0', '5', '1', '8', '5', '9', '8', '9', '9', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk061Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['6', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '0', '4', '2', '1', '2', '7', '4', '0', '3', '4', '9', '4', '0', '3', '1', '8', '3', '7', '9', '2', '8']), .str (String.ofList ['2', '2', '9', '9', '2', '9', '4', '0', '8', '5', '7', '5', '4', '0', '6', '3', '1', '5', '7', '2', '8', '7']), .str (String.ofList ['2', '1', '7', '8', '6', '2', '5', '9', '6', '3', '3', '4', '7', '2', '4', '5', '2', '9', '8', '5', '8']), .str (String.ofList ['1', '6', '5', '6', '1', '7', '4', '9', '7', '6', '4', '4', '3', '4', '9', '7', '1', '0', '7', '1', '4']), .str (String.ofList ['5', '4', '1', '8', '8', '3', '9', '0', '1', '9', '4', '0', '1', '6', '8', '6', '9', '2', '5', '8', '9']), .str (String.ofList ['1', '2', '1', '1', '6', '0', '9', '3', '2', '2', '9', '1', '0', '1', '5', '9', '2', '1', '2', '7', '8', '8']), .str (String.ofList ['9', '5', '7', '4', '4', '6', '4', '8', '9', '8', '1', '6', '7', '9', '5', '8', '8', '2', '1', '1', '5']), .str (String.ofList ['7', '8', '4', '2', '5', '1', '8', '0', '3', '3', '7', '3', '1', '3', '9', '5', '7', '0', '5', '2', '9']), .str (String.ofList ['9', '8', '9', '5', '9', '3', '8', '9', '9', '3', '1', '2', '1', '9', '9', '9', '4', '7', '8', '7', '4']), .str (String.ofList ['9', '8', '9', '5', '6', '2', '5', '2', '2', '2', '5', '3', '9', '7', '0', '8', '8', '0', '9', '1', '2'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '1', '5', '3', '3', '8', '8', '6', '9', '9', '8', '7', '7', '2', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '1', '8', '0', '1', '0', '5', '1', '8', '5', '9', '8', '9', '9', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_061_before_generic"
  err.flush

theorem array_moment_records_chunk_061 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 120)
      (SourceJson.white (momentRecordsChunk061Chars ++ tail)) acc =
      SourceJson.array (fuel + 119) (SourceJson.white tail) (momentRecordsChunk061Push acc) := by rfl

noncomputable def momentRecordsAcc062 : List SourceJson := momentRecordsChunk061Push momentRecordsAcc061

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_061_generic_complete"
  err.flush

noncomputable def momentRecordsChunk062Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '3', '4', '9', '2', '9', '9', '8', '7', '3', '3', '0', '4', '9', '2', '8', '6', '5', '9', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '9', '5', '9', '9', '1', '0', '7', '4', '9', '2', '3', '8', '9', '7', '4', '6', '6', '5', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '3', '9', '2', '8', '9', '3', '3', '6', '9', '2', '2', '2', '4', '8', '6', '2', '7', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '4', '3', '2', '6', '9', '0', '0', '9', '7', '9', '2', '0', '0', '5', '4', '1', '3', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '7', '9', '1', '4', '7', '0', '7', '5', '5', '1', '4', '5', '6', '3', '7', '4', '5', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '6', '6', '5', '6', '6', '3', '8', '2', '6', '2', '4', '3', '4', '6', '6', '8', '0', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '7', '4', '3', '5', '3', '6', '0', '3', '2', '0', '2', '0', '7', '6', '4', '0', '1', '7', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '1', '4', '6', '6', '9', '0', '6', '3', '0', '9', '9', '5', '9', '4', '4', '6', '4', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '7', '6', '0', '1', '7', '2', '1', '2', '1', '9', '4', '1', '7', '6', '3', '0', '2', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '7', '5', '7', '9', '6', '6', '7', '0', '8', '2', '2', '0', '6', '7', '9', '1', '4', '8', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '6', '2', '3', '6', '2', '1', '7', '5', '8', '5', '0', '4', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '6', '6', '8', '0', '3', '1', '5', '4', '4', '1', '6', '0', '7', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk062Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['6', '2'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '4', '3', '4', '9', '2', '9', '9', '8', '7', '3', '3', '0', '4', '9', '2', '8', '6', '5', '9', '5', '2']), .str (String.ofList ['2', '5', '9', '5', '9', '9', '1', '0', '7', '4', '9', '2', '3', '8', '9', '7', '4', '6', '6', '5', '9', '8']), .str (String.ofList ['2', '7', '2', '3', '9', '2', '8', '9', '3', '3', '6', '9', '2', '2', '2', '4', '8', '6', '2', '7', '9']), .str (String.ofList ['3', '6', '4', '3', '2', '6', '9', '0', '0', '9', '7', '9', '2', '0', '0', '5', '4', '1', '3', '1', '8']), .str (String.ofList ['6', '3', '7', '9', '1', '4', '7', '0', '7', '5', '5', '1', '4', '5', '6', '3', '7', '4', '5', '8', '6']), .str (String.ofList ['1', '8', '3', '6', '6', '5', '6', '6', '3', '8', '2', '6', '2', '4', '3', '4', '6', '6', '8', '0', '1', '2']), .str (String.ofList ['7', '2', '7', '4', '3', '5', '3', '6', '0', '3', '2', '0', '2', '0', '7', '6', '4', '0', '1', '7', '9']), .str (String.ofList ['7', '5', '1', '4', '6', '6', '9', '0', '6', '3', '0', '9', '9', '5', '9', '4', '4', '6', '4', '2', '1']), .str (String.ofList ['9', '6', '7', '6', '0', '1', '7', '2', '1', '2', '1', '9', '4', '1', '7', '6', '3', '0', '2', '5', '5']), .str (String.ofList ['9', '6', '7', '5', '7', '9', '6', '6', '7', '0', '8', '2', '2', '0', '6', '7', '9', '1', '4', '8', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '6', '2', '3', '6', '2', '1', '7', '5', '8', '5', '0', '4', '3', '9'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '6', '6', '8', '0', '3', '1', '5', '4', '4', '1', '6', '0', '7', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_062_before_generic"
  err.flush

theorem array_moment_records_chunk_062 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 119)
      (SourceJson.white (momentRecordsChunk062Chars ++ tail)) acc =
      SourceJson.array (fuel + 118) (SourceJson.white tail) (momentRecordsChunk062Push acc) := by rfl

noncomputable def momentRecordsAcc063 : List SourceJson := momentRecordsChunk062Push momentRecordsAcc062

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_062_generic_complete"
  err.flush

noncomputable def momentRecordsChunk063Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '1', '6', '5', '3', '1', '8', '8', '9', '6', '9', '2', '7', '8', '4', '4', '2', '3', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '1', '1', '5', '4', '2', '9', '0', '8', '6', '2', '2', '6', '1', '8', '7', '4', '3', '8', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '2', '0', '6', '9', '8', '2', '8', '8', '7', '3', '3', '8', '9', '8', '0', '4', '5', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '1', '4', '7', '6', '0', '1', '7', '3', '0', '5', '4', '6', '8', '5', '4', '4', '8', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '0', '6', '6', '0', '4', '7', '0', '4', '2', '0', '2', '7', '4', '5', '5', '2', '6', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '3', '6', '8', '5', '1', '2', '4', '6', '8', '8', '0', '7', '4', '3', '5', '4', '3', '6', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '4', '0', '0', '5', '1', '8', '7', '6', '1', '5', '0', '3', '6', '3', '6', '7', '7', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '3', '0', '2', '9', '0', '8', '9', '7', '2', '4', '5', '5', '4', '7', '9', '6', '3', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '6', '0', '9', '2', '1', '1', '4', '8', '5', '5', '7', '7', '1', '2', '7', '7', '2', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '6', '0', '7', '2', '3', '6', '9', '2', '2', '8', '2', '3', '5', '0', '5', '1', '3', '4', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '6', '1', '1', '8', '4', '9', '9', '7', '6', '6', '8', '7', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '7', '2', '7', '7', '6', '4', '7', '9', '3', '0', '1', '4', '2', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk063Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['6', '3'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '4', '6', '1', '6', '5', '3', '1', '8', '8', '9', '6', '9', '2', '7', '8', '4', '4', '2', '3', '1', '8']), .str (String.ofList ['2', '6', '1', '1', '5', '4', '2', '9', '0', '8', '6', '2', '2', '6', '1', '8', '7', '4', '3', '8', '2', '5']), .str (String.ofList ['2', '8', '2', '0', '6', '9', '8', '2', '8', '8', '7', '3', '3', '8', '9', '8', '0', '4', '5', '8', '0']), .str (String.ofList ['3', '8', '1', '4', '7', '6', '0', '1', '7', '3', '0', '5', '4', '6', '8', '5', '4', '4', '8', '8', '1']), .str (String.ofList ['8', '3', '0', '6', '6', '0', '4', '7', '0', '4', '2', '0', '2', '7', '4', '5', '5', '2', '6', '5', '1']), .str (String.ofList ['1', '9', '3', '6', '8', '5', '1', '2', '4', '6', '8', '8', '0', '7', '4', '3', '5', '4', '3', '6', '5', '6']), .str (String.ofList ['7', '8', '4', '0', '0', '5', '1', '8', '7', '6', '1', '5', '0', '3', '6', '3', '6', '7', '7', '6', '9']), .str (String.ofList ['9', '2', '3', '0', '2', '9', '0', '8', '9', '7', '2', '4', '5', '5', '4', '7', '9', '6', '3', '7', '4']), .str (String.ofList ['9', '0', '6', '0', '9', '2', '1', '1', '4', '8', '5', '5', '7', '7', '1', '2', '7', '7', '2', '9', '6']), .str (String.ofList ['9', '0', '6', '0', '7', '2', '3', '6', '9', '2', '2', '8', '2', '3', '5', '0', '5', '1', '3', '4', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '6', '6', '1', '1', '8', '4', '9', '9', '7', '6', '6', '8', '7', '7'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '7', '2', '7', '7', '6', '4', '7', '9', '3', '0', '1', '4', '2', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_063_before_generic"
  err.flush

theorem array_moment_records_chunk_063 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 118)
      (SourceJson.white (momentRecordsChunk063Chars ++ tail)) acc =
      SourceJson.array (fuel + 117) (SourceJson.white tail) (momentRecordsChunk063Push acc) := by rfl

noncomputable def momentRecordsAcc064 : List SourceJson := momentRecordsChunk063Push momentRecordsAcc063

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_063_generic_complete"
  err.flush

noncomputable def momentRecordsBlock015Chars : List Char := momentRecordsChunk060Chars ++ momentRecordsChunk061Chars ++ momentRecordsChunk062Chars ++ momentRecordsChunk063Chars
noncomputable def momentRecordsBlock015Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk063Push (momentRecordsChunk062Push (momentRecordsChunk061Push (momentRecordsChunk060Push (acc))))

theorem array_moment_records_block_015 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 121)
      (SourceJson.white (momentRecordsBlock015Chars ++ tail)) acc =
      SourceJson.array (fuel + 117) (SourceJson.white tail) (momentRecordsBlock015Push acc) := by
  have hinput : momentRecordsBlock015Chars ++ tail = momentRecordsChunk060Chars ++ (momentRecordsChunk061Chars ++ (momentRecordsChunk062Chars ++ (momentRecordsChunk063Chars ++ (tail)))) := by
    simp only [momentRecordsBlock015Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 121) (SourceJson.white (momentRecordsBlock015Chars ++ tail)) acc =
        SourceJson.array (fuel + 121) (SourceJson.white (momentRecordsChunk060Chars ++ (momentRecordsChunk061Chars ++ (momentRecordsChunk062Chars ++ (momentRecordsChunk063Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 121) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 120) (SourceJson.white (momentRecordsChunk061Chars ++ (momentRecordsChunk062Chars ++ (momentRecordsChunk063Chars ++ (tail))))) (momentRecordsChunk060Push (acc)) := array_moment_records_chunk_060 fuel (momentRecordsChunk061Chars ++ (momentRecordsChunk062Chars ++ (momentRecordsChunk063Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 119) (SourceJson.white (momentRecordsChunk062Chars ++ (momentRecordsChunk063Chars ++ (tail)))) (momentRecordsChunk061Push (momentRecordsChunk060Push (acc))) := array_moment_records_chunk_061 fuel (momentRecordsChunk062Chars ++ (momentRecordsChunk063Chars ++ (tail))) (momentRecordsChunk060Push (acc))
    _ = SourceJson.array (fuel + 118) (SourceJson.white (momentRecordsChunk063Chars ++ (tail))) (momentRecordsChunk062Push (momentRecordsChunk061Push (momentRecordsChunk060Push (acc)))) := array_moment_records_chunk_062 fuel (momentRecordsChunk063Chars ++ (tail)) (momentRecordsChunk061Push (momentRecordsChunk060Push (acc)))
    _ = SourceJson.array (fuel + 117) (SourceJson.white tail) (momentRecordsBlock015Push acc) := array_moment_records_chunk_063 fuel (tail) (momentRecordsChunk062Push (momentRecordsChunk061Push (momentRecordsChunk060Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_015_before_raw_binding"
  err.flush

theorem moment_records_block_015_prefix :
    (momentRest01 31628).take 2062 = momentRecordsBlock015Chars := by rfl

theorem moment_records_block_015_split :
    momentRest01 31628 = momentRecordsBlock015Chars ++ momentRest01 33690 := by
  calc
    momentRest01 31628 =
        (momentRest01 31628).take 2062 ++ (momentRest01 31628).drop 2062 :=
      (List.take_append_drop 2062 (momentRest01 31628)).symm
    _ = momentRecordsBlock015Chars ++ (momentRest01 31628).drop 2062 :=
      congrArg (fun p => p ++ (momentRest01 31628).drop 2062) moment_records_block_015_prefix
    _ = momentRecordsBlock015Chars ++ momentRest01 33690 :=
      congrArg (fun rest => momentRecordsBlock015Chars ++ rest) (momentRest01_drop 31628 2062)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_015_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_015 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 121)
      (SourceJson.white (momentRest01 31628)) acc =
      SourceJson.array (fuel + 117) (SourceJson.white (momentRest01 33690)) (momentRecordsBlock015Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 121) (SourceJson.white s) acc)
      moment_records_block_015_split).trans (array_moment_records_block_015 fuel (momentRest01 33690) acc)

theorem moment_records_through_block_015 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 117) (SourceJson.white (momentRest01 33690)) momentRecordsAcc064 := by
  exact (moment_records_through_block_014 fuel).trans (array_moment_records_original_block_015 fuel momentRecordsAcc060)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_015_complete"
  err.flush

#print axioms array_moment_records_chunk_060
#print axioms array_moment_records_chunk_061
#print axioms array_moment_records_chunk_062
#print axioms array_moment_records_chunk_063
#print axioms array_moment_records_block_015
#print axioms moment_records_block_015_prefix
#print axioms moment_records_block_015_split
#print axioms array_moment_records_original_block_015
#print axioms moment_records_through_block_015

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
