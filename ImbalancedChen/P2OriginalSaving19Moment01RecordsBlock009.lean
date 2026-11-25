import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock008

/-! Original moment records block 9. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk036Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '5', '4', '6', '0', '5', '9', '4', '9', '2', '7', '2', '6', '3', '0', '6', '6', '0', '0', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '2', '5', '6', '3', '6', '2', '5', '6', '8', '6', '1', '7', '4', '5', '3', '6', '3', '6', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '1', '1', '0', '3', '5', '0', '3', '6', '9', '4', '6', '8', '5', '2', '1', '9', '8', '8', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '8', '3', '5', '6', '1', '6', '4', '6', '1', '0', '5', '6', '6', '3', '7', '4', '9', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '6', '2', '9', '3', '8', '2', '8', '8', '9', '8', '6', '9', '4', '7', '4', '5', '6', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '8', '5', '7', '2', '6', '4', '4', '0', '6', '0', '6', '5', '5', '0', '9', '0', '0', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '4', '3', '0', '5', '6', '2', '9', '6', '4', '0', '2', '6', '2', '2', '0', '9', '5', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '0', '1', '0', '1', '6', '4', '2', '1', '6', '3', '3', '3', '6', '4', '7', '4', '2', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '6', '4', '8', '2', '9', '9', '8', '3', '9', '0', '6', '9', '3', '5', '3', '0', '9', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '1', '7', '0', '5', '7', '6', '0', '3', '2', '6', '4', '5', '3', '2', '9', '1', '7', '4', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '4', '5', '3', '3', '4', '6', '9', '4', '7', '8', '6', '1', '4', '4', '6', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '6', '7', '8', '0', '2', '9', '5', '8', '7', '1', '2', '4', '2', '8', '9', '6', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk036Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['3', '6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '9', '5', '4', '6', '0', '5', '9', '4', '9', '2', '7', '2', '6', '3', '0', '6', '6', '0', '0', '6', '2']), .str (String.ofList ['2', '1', '2', '5', '6', '3', '6', '2', '5', '6', '8', '6', '1', '7', '4', '5', '3', '6', '3', '6', '8', '7']), .str (String.ofList ['2', '7', '1', '1', '0', '3', '5', '0', '3', '6', '9', '4', '6', '8', '5', '2', '1', '9', '8', '8', '5']), .str (String.ofList ['4', '8', '8', '3', '5', '6', '1', '6', '4', '6', '1', '0', '5', '6', '6', '3', '7', '4', '9', '7', '5']), .str (String.ofList ['8', '8', '6', '2', '9', '3', '8', '2', '8', '8', '9', '8', '6', '9', '4', '7', '4', '5', '6', '5', '9']), .str (String.ofList ['1', '6', '8', '8', '5', '7', '2', '6', '4', '4', '0', '6', '0', '6', '5', '5', '0', '9', '0', '0', '3', '9']), .str (String.ofList ['1', '2', '4', '4', '3', '0', '5', '6', '2', '9', '6', '4', '0', '2', '6', '2', '2', '0', '9', '5', '9', '6']), .str (String.ofList ['9', '5', '0', '1', '0', '1', '6', '4', '2', '1', '6', '3', '3', '3', '6', '4', '7', '4', '2', '3', '6']), .str (String.ofList ['1', '1', '6', '6', '4', '8', '2', '9', '9', '8', '3', '9', '0', '6', '9', '3', '5', '3', '0', '9', '5', '7']), .str (String.ofList ['1', '2', '6', '1', '7', '0', '5', '7', '6', '0', '3', '2', '6', '4', '5', '3', '2', '9', '1', '7', '4', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '2', '4', '5', '3', '3', '4', '6', '9', '4', '7', '8', '6', '1', '4', '4', '6', '1', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '2', '6', '7', '8', '0', '2', '9', '5', '8', '7', '1', '2', '4', '2', '8', '9', '6', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_036_before_generic"
  err.flush

theorem array_moment_records_chunk_036 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 145)
      (SourceJson.white (momentRecordsChunk036Chars ++ tail)) acc =
      SourceJson.array (fuel + 144) (SourceJson.white tail) (momentRecordsChunk036Push acc) := by rfl

noncomputable def momentRecordsAcc037 : List SourceJson := momentRecordsChunk036Push momentRecordsAcc036

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_036_generic_complete"
  err.flush

noncomputable def momentRecordsChunk037Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '1', '2', '2', '4', '0', '5', '8', '4', '9', '7', '0', '9', '3', '7', '7', '8', '4', '9', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '2', '8', '6', '3', '7', '4', '0', '3', '0', '6', '6', '1', '8', '0', '3', '0', '2', '4', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '1', '3', '3', '2', '9', '1', '8', '3', '9', '0', '6', '0', '4', '3', '7', '6', '4', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '1', '3', '9', '8', '5', '8', '0', '4', '6', '2', '4', '9', '5', '5', '4', '4', '1', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '6', '2', '5', '6', '9', '3', '5', '6', '4', '3', '4', '5', '6', '3', '2', '7', '1', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '8', '7', '8', '3', '5', '1', '4', '7', '4', '7', '8', '6', '6', '3', '0', '3', '1', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '8', '8', '0', '9', '5', '9', '0', '6', '2', '9', '0', '3', '9', '0', '0', '0', '3', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '9', '7', '5', '7', '6', '4', '5', '1', '1', '3', '8', '6', '4', '3', '4', '0', '3', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '3', '9', '2', '7', '0', '4', '2', '4', '5', '9', '8', '0', '0', '6', '1', '6', '4', '4', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '2', '9', '6', '6', '6', '2', '4', '0', '4', '1', '6', '8', '3', '1', '1', '6', '5', '4', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '2', '4', '7', '0', '4', '9', '3', '0', '0', '9', '0', '5', '5', '7', '2', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '5', '7', '5', '2', '1', '1', '9', '1', '9', '9', '5', '0', '9', '1', '3', '5', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk037Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['3', '7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '9', '1', '2', '2', '4', '0', '5', '8', '4', '9', '7', '0', '9', '3', '7', '7', '8', '4', '9', '7', '5']), .str (String.ofList ['2', '0', '2', '8', '6', '3', '7', '4', '0', '3', '0', '6', '6', '1', '8', '0', '3', '0', '2', '4', '3', '5']), .str (String.ofList ['2', '6', '1', '3', '3', '2', '9', '1', '8', '3', '9', '0', '6', '0', '4', '3', '7', '6', '4', '1', '4']), .str (String.ofList ['4', '9', '1', '3', '9', '8', '5', '8', '0', '4', '6', '2', '4', '9', '5', '5', '4', '4', '1', '6', '1']), .str (String.ofList ['8', '8', '6', '2', '5', '6', '9', '3', '5', '6', '4', '3', '4', '5', '6', '3', '2', '7', '1', '4', '5']), .str (String.ofList ['1', '6', '8', '8', '7', '8', '3', '5', '1', '4', '7', '4', '7', '8', '6', '6', '3', '0', '3', '1', '4', '8']), .str (String.ofList ['1', '1', '9', '8', '8', '0', '9', '5', '9', '0', '6', '2', '9', '0', '3', '9', '0', '0', '0', '3', '4', '3']), .str (String.ofList ['9', '1', '9', '7', '5', '7', '6', '4', '5', '1', '1', '3', '8', '6', '4', '3', '4', '0', '3', '2', '0']), .str (String.ofList ['1', '0', '9', '3', '9', '2', '7', '0', '4', '2', '4', '5', '9', '8', '0', '0', '6', '1', '6', '4', '4', '4']), .str (String.ofList ['1', '3', '9', '2', '9', '6', '6', '6', '2', '4', '0', '4', '1', '6', '8', '3', '1', '1', '6', '5', '4', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '3', '2', '4', '7', '0', '4', '9', '3', '0', '0', '9', '0', '5', '5', '7', '2', '7', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '3', '5', '7', '5', '2', '1', '1', '9', '1', '9', '9', '5', '0', '9', '1', '3', '5', '8']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_037_before_generic"
  err.flush

theorem array_moment_records_chunk_037 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 144)
      (SourceJson.white (momentRecordsChunk037Chars ++ tail)) acc =
      SourceJson.array (fuel + 143) (SourceJson.white tail) (momentRecordsChunk037Push acc) := by rfl

noncomputable def momentRecordsAcc038 : List SourceJson := momentRecordsChunk037Push momentRecordsAcc037

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_037_generic_complete"
  err.flush

noncomputable def momentRecordsChunk038Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '4', '2', '2', '4', '6', '1', '4', '1', '0', '8', '1', '6', '7', '2', '7', '3', '4', '5', '2', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '8', '5', '7', '7', '6', '4', '7', '3', '5', '7', '4', '0', '5', '5', '9', '0', '2', '7', '1', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '1', '3', '3', '3', '0', '5', '3', '4', '2', '9', '2', '0', '7', '4', '5', '2', '6', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '4', '5', '5', '9', '8', '1', '8', '8', '6', '8', '0', '3', '1', '5', '1', '2', '3', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '1', '0', '3', '3', '6', '6', '3', '9', '7', '3', '1', '6', '9', '5', '9', '6', '0', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '5', '3', '3', '4', '3', '9', '6', '4', '1', '0', '3', '9', '9', '0', '8', '0', '6', '5', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '5', '3', '3', '1', '1', '4', '2', '1', '5', '1', '4', '0', '5', '3', '4', '8', '6', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '1', '9', '5', '8', '3', '8', '0', '3', '5', '8', '9', '3', '0', '3', '4', '9', '9', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '4', '3', '2', '6', '8', '9', '5', '4', '7', '1', '6', '8', '4', '2', '3', '6', '5', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '6', '8', '9', '2', '0', '6', '3', '1', '7', '9', '4', '8', '6', '1', '6', '5', '7', '3', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '3', '9', '2', '9', '1', '9', '0', '0', '5', '7', '2', '2', '0', '6', '5', '6', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '4', '4', '6', '8', '9', '1', '3', '5', '7', '3', '4', '6', '5', '6', '3', '0', '4', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk038Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['3', '8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '8', '4', '2', '2', '4', '6', '1', '4', '1', '0', '8', '1', '6', '7', '2', '7', '3', '4', '5', '2', '3']), .str (String.ofList ['1', '9', '8', '5', '7', '7', '6', '4', '7', '3', '5', '7', '4', '0', '5', '5', '9', '0', '2', '7', '1', '1']), .str (String.ofList ['2', '6', '1', '3', '3', '3', '0', '5', '3', '4', '2', '9', '2', '0', '7', '4', '5', '2', '6', '3', '5']), .str (String.ofList ['4', '8', '4', '5', '5', '9', '8', '1', '8', '8', '6', '8', '0', '3', '1', '5', '1', '2', '3', '4', '5']), .str (String.ofList ['9', '1', '1', '0', '3', '3', '6', '6', '3', '9', '7', '3', '1', '6', '9', '5', '9', '6', '0', '3', '9']), .str (String.ofList ['1', '7', '6', '5', '3', '3', '4', '3', '9', '6', '4', '1', '0', '3', '9', '9', '0', '8', '0', '6', '5', '4']), .str (String.ofList ['1', '2', '0', '5', '3', '3', '1', '1', '4', '2', '1', '5', '1', '4', '0', '5', '3', '4', '8', '6', '6', '4']), .str (String.ofList ['9', '3', '1', '9', '5', '8', '3', '8', '0', '3', '5', '8', '9', '3', '0', '3', '4', '9', '9', '2', '4']), .str (String.ofList ['1', '0', '1', '4', '3', '2', '6', '8', '9', '5', '4', '7', '1', '6', '8', '4', '2', '3', '6', '5', '8', '1']), .str (String.ofList ['1', '6', '3', '6', '8', '9', '2', '0', '6', '3', '1', '7', '9', '4', '8', '6', '1', '6', '5', '7', '3', '2'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '3', '9', '2', '9', '1', '9', '0', '0', '5', '7', '2', '2', '0', '6', '5', '6', '8', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '4', '4', '6', '8', '9', '1', '3', '5', '7', '3', '4', '6', '5', '6', '3', '0', '4', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_038_before_generic"
  err.flush

theorem array_moment_records_chunk_038 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 143)
      (SourceJson.white (momentRecordsChunk038Chars ++ tail)) acc =
      SourceJson.array (fuel + 142) (SourceJson.white tail) (momentRecordsChunk038Push acc) := by rfl

noncomputable def momentRecordsAcc039 : List SourceJson := momentRecordsChunk038Push momentRecordsAcc038

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_038_generic_complete"
  err.flush

noncomputable def momentRecordsChunk039Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '4', '1', '7', '2', '6', '5', '2', '3', '8', '3', '2', '7', '4', '3', '3', '7', '1', '0', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '8', '5', '1', '8', '0', '2', '1', '1', '7', '4', '4', '8', '0', '2', '7', '0', '6', '1', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '3', '5', '1', '6', '3', '8', '0', '5', '7', '5', '8', '9', '3', '6', '8', '3', '9', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '3', '0', '3', '2', '9', '3', '1', '5', '8', '1', '3', '3', '1', '7', '0', '5', '1', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '8', '5', '5', '0', '1', '1', '2', '6', '4', '9', '9', '5', '0', '1', '0', '4', '9', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '1', '0', '3', '0', '4', '3', '0', '8', '5', '9', '3', '7', '1', '2', '3', '9', '3', '8', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '8', '6', '8', '9', '4', '2', '9', '4', '0', '9', '2', '2', '0', '3', '6', '0', '8', '9', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '1', '6', '1', '5', '3', '0', '7', '2', '1', '7', '6', '2', '5', '7', '3', '8', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '9', '7', '6', '7', '2', '5', '2', '7', '6', '3', '0', '5', '5', '8', '6', '3', '8', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '9', '8', '2', '2', '9', '2', '3', '2', '6', '1', '8', '7', '0', '4', '1', '9', '2', '8', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '4', '2', '6', '5', '3', '3', '4', '7', '0', '1', '1', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '4', '7', '8', '5', '6', '6', '2', '7', '2', '7', '4', '7', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk039Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['3', '9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '4', '4', '1', '7', '2', '6', '5', '2', '3', '8', '3', '2', '7', '4', '3', '3', '7', '1', '0', '2', '8']), .str (String.ofList ['2', '5', '8', '5', '1', '8', '0', '2', '1', '1', '7', '4', '4', '8', '0', '2', '7', '0', '6', '1', '9', '1']), .str (String.ofList ['2', '8', '3', '5', '1', '6', '3', '8', '0', '5', '7', '5', '8', '9', '3', '6', '8', '3', '9', '5', '9']), .str (String.ofList ['6', '1', '3', '0', '3', '2', '9', '3', '1', '5', '8', '1', '3', '3', '1', '7', '0', '5', '1', '1', '6']), .str (String.ofList ['9', '8', '8', '5', '5', '0', '1', '1', '2', '6', '4', '9', '9', '5', '0', '1', '0', '4', '9', '5', '2']), .str (String.ofList ['2', '0', '1', '0', '3', '0', '4', '3', '0', '8', '5', '9', '3', '7', '1', '2', '3', '9', '3', '8', '6', '9']), .str (String.ofList ['1', '4', '2', '8', '6', '8', '9', '4', '2', '9', '4', '0', '9', '2', '2', '0', '3', '6', '0', '8', '9', '7']), .str (String.ofList ['1', '1', '5', '7', '1', '6', '1', '5', '3', '0', '7', '2', '1', '7', '6', '2', '5', '7', '3', '8', '4', '2']), .str (String.ofList ['1', '3', '0', '9', '7', '6', '7', '2', '5', '2', '7', '6', '3', '0', '5', '5', '8', '6', '3', '8', '4', '2']), .str (String.ofList ['1', '3', '0', '9', '8', '2', '2', '9', '2', '3', '2', '6', '1', '8', '7', '0', '4', '1', '9', '2', '8', '4'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '4', '2', '6', '5', '3', '3', '4', '7', '0', '1', '1', '7', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '4', '7', '8', '5', '6', '6', '2', '7', '2', '7', '4', '7', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_039_before_generic"
  err.flush

theorem array_moment_records_chunk_039 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 142)
      (SourceJson.white (momentRecordsChunk039Chars ++ tail)) acc =
      SourceJson.array (fuel + 141) (SourceJson.white tail) (momentRecordsChunk039Push acc) := by rfl

noncomputable def momentRecordsAcc040 : List SourceJson := momentRecordsChunk039Push momentRecordsAcc039

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_039_generic_complete"
  err.flush

noncomputable def momentRecordsBlock009Chars : List Char := momentRecordsChunk036Chars ++ momentRecordsChunk037Chars ++ momentRecordsChunk038Chars ++ momentRecordsChunk039Chars
noncomputable def momentRecordsBlock009Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk039Push (momentRecordsChunk038Push (momentRecordsChunk037Push (momentRecordsChunk036Push (acc))))

theorem array_moment_records_block_009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 145)
      (SourceJson.white (momentRecordsBlock009Chars ++ tail)) acc =
      SourceJson.array (fuel + 141) (SourceJson.white tail) (momentRecordsBlock009Push acc) := by
  have hinput : momentRecordsBlock009Chars ++ tail = momentRecordsChunk036Chars ++ (momentRecordsChunk037Chars ++ (momentRecordsChunk038Chars ++ (momentRecordsChunk039Chars ++ (tail)))) := by
    simp only [momentRecordsBlock009Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 145) (SourceJson.white (momentRecordsBlock009Chars ++ tail)) acc =
        SourceJson.array (fuel + 145) (SourceJson.white (momentRecordsChunk036Chars ++ (momentRecordsChunk037Chars ++ (momentRecordsChunk038Chars ++ (momentRecordsChunk039Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 145) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 144) (SourceJson.white (momentRecordsChunk037Chars ++ (momentRecordsChunk038Chars ++ (momentRecordsChunk039Chars ++ (tail))))) (momentRecordsChunk036Push (acc)) := array_moment_records_chunk_036 fuel (momentRecordsChunk037Chars ++ (momentRecordsChunk038Chars ++ (momentRecordsChunk039Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 143) (SourceJson.white (momentRecordsChunk038Chars ++ (momentRecordsChunk039Chars ++ (tail)))) (momentRecordsChunk037Push (momentRecordsChunk036Push (acc))) := array_moment_records_chunk_037 fuel (momentRecordsChunk038Chars ++ (momentRecordsChunk039Chars ++ (tail))) (momentRecordsChunk036Push (acc))
    _ = SourceJson.array (fuel + 142) (SourceJson.white (momentRecordsChunk039Chars ++ (tail))) (momentRecordsChunk038Push (momentRecordsChunk037Push (momentRecordsChunk036Push (acc)))) := array_moment_records_chunk_038 fuel (momentRecordsChunk039Chars ++ (tail)) (momentRecordsChunk037Push (momentRecordsChunk036Push (acc)))
    _ = SourceJson.array (fuel + 141) (SourceJson.white tail) (momentRecordsBlock009Push acc) := array_moment_records_chunk_039 fuel (tail) (momentRecordsChunk038Push (momentRecordsChunk037Push (momentRecordsChunk036Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_009_before_raw_binding"
  err.flush

theorem moment_records_block_009_prefix :
    (momentRest01 19134).take 2095 = momentRecordsBlock009Chars := by rfl

theorem moment_records_block_009_split :
    momentRest01 19134 = momentRecordsBlock009Chars ++ momentRest01 21229 := by
  calc
    momentRest01 19134 =
        (momentRest01 19134).take 2095 ++ (momentRest01 19134).drop 2095 :=
      (List.take_append_drop 2095 (momentRest01 19134)).symm
    _ = momentRecordsBlock009Chars ++ (momentRest01 19134).drop 2095 :=
      congrArg (fun p => p ++ (momentRest01 19134).drop 2095) moment_records_block_009_prefix
    _ = momentRecordsBlock009Chars ++ momentRest01 21229 :=
      congrArg (fun rest => momentRecordsBlock009Chars ++ rest) (momentRest01_drop 19134 2095)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_009_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_009 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 145)
      (SourceJson.white (momentRest01 19134)) acc =
      SourceJson.array (fuel + 141) (SourceJson.white (momentRest01 21229)) (momentRecordsBlock009Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 145) (SourceJson.white s) acc)
      moment_records_block_009_split).trans (array_moment_records_block_009 fuel (momentRest01 21229) acc)

theorem moment_records_through_block_009 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 141) (SourceJson.white (momentRest01 21229)) momentRecordsAcc040 := by
  exact (moment_records_through_block_008 fuel).trans (array_moment_records_original_block_009 fuel momentRecordsAcc036)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_009_complete"
  err.flush

#print axioms array_moment_records_chunk_036
#print axioms array_moment_records_chunk_037
#print axioms array_moment_records_chunk_038
#print axioms array_moment_records_chunk_039
#print axioms array_moment_records_block_009
#print axioms moment_records_block_009_prefix
#print axioms moment_records_block_009_split
#print axioms array_moment_records_original_block_009
#print axioms moment_records_through_block_009

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
