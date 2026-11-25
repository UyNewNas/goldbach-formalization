import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock018

/-! Original moment records block 19. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk076Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '3', '9', '0', '5', '6', '4', '2', '7', '1', '8', '9', '3', '8', '0', '8', '5', '8', '2', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '0', '7', '2', '7', '7', '6', '9', '1', '1', '0', '0', '3', '3', '7', '0', '9', '5', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '4', '9', '9', '5', '9', '6', '0', '2', '4', '7', '5', '3', '4', '5', '4', '6', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '0', '4', '3', '0', '2', '1', '5', '6', '5', '7', '1', '5', '5', '5', '1', '1', '5', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '2', '1', '7', '0', '9', '2', '9', '9', '1', '8', '2', '4', '8', '6', '3', '1', '9', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '8', '3', '8', '2', '3', '4', '9', '0', '1', '7', '2', '2', '9', '6', '0', '0', '1', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '0', '6', '7', '1', '4', '4', '8', '1', '0', '4', '9', '6', '2', '8', '9', '3', '3', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '4', '6', '5', '9', '7', '7', '9', '8', '4', '5', '1', '6', '5', '2', '5', '3', '5', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '1', '4', '7', '0', '9', '4', '2', '5', '1', '1', '6', '2', '0', '0', '6', '9', '7', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '1', '5', '4', '4', '9', '2', '7', '6', '7', '2', '4', '3', '3', '9', '1', '4', '5', '8', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '7', '5', '1', '1', '7', '1', '9', '4', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '7', '7', '8', '4', '2', '5', '8', '2', '5', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk076Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['7', '6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '2', '3', '9', '0', '5', '6', '4', '2', '7', '1', '8', '9', '3', '8', '0', '8', '5', '8', '2', '8', '7']), .str (String.ofList ['1', '2', '4', '0', '7', '2', '7', '7', '6', '9', '1', '1', '0', '0', '3', '3', '7', '0', '9', '5', '1', '0']), .str (String.ofList ['1', '1', '2', '4', '9', '9', '5', '9', '6', '0', '2', '4', '7', '5', '3', '4', '5', '4', '6', '5', '1']), .str (String.ofList ['6', '0', '0', '4', '3', '0', '2', '1', '5', '6', '5', '7', '1', '5', '5', '5', '1', '1', '5', '5', '3']), .str (String.ofList ['1', '2', '7', '2', '1', '7', '0', '9', '2', '9', '9', '1', '8', '2', '4', '8', '6', '3', '1', '9', '0', '6']), .str (String.ofList ['1', '1', '3', '8', '3', '8', '2', '3', '4', '9', '0', '1', '7', '2', '2', '9', '6', '0', '0', '1', '3', '7']), .str (String.ofList ['9', '0', '0', '6', '7', '1', '4', '4', '8', '1', '0', '4', '9', '6', '2', '8', '9', '3', '3', '5', '5']), .str (String.ofList ['8', '0', '4', '6', '5', '9', '7', '7', '9', '8', '4', '5', '1', '6', '5', '2', '5', '3', '5', '6', '7']), .str (String.ofList ['7', '2', '1', '4', '7', '0', '9', '4', '2', '5', '1', '1', '6', '2', '0', '0', '6', '9', '7', '5', '9']), .str (String.ofList ['7', '2', '1', '5', '4', '4', '9', '2', '7', '6', '7', '2', '4', '3', '3', '9', '1', '4', '5', '8', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '7', '5', '1', '1', '7', '1', '9', '4', '1', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '7', '7', '8', '4', '2', '5', '8', '2', '5', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_076_before_generic"
  err.flush

theorem array_moment_records_chunk_076 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 105)
      (SourceJson.white (momentRecordsChunk076Chars ++ tail)) acc =
      SourceJson.array (fuel + 104) (SourceJson.white tail) (momentRecordsChunk076Push acc) := by rfl

noncomputable def momentRecordsAcc077 : List SourceJson := momentRecordsChunk076Push momentRecordsAcc076

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_076_generic_complete"
  err.flush

noncomputable def momentRecordsChunk077Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '2', '1', '6', '9', '4', '8', '7', '4', '3', '8', '3', '6', '5', '4', '0', '2', '7', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '9', '3', '7', '4', '0', '8', '5', '8', '1', '3', '4', '3', '5', '6', '5', '4', '4', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '3', '9', '4', '3', '1', '3', '5', '6', '3', '8', '3', '0', '5', '5', '9', '7', '0', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '8', '5', '8', '6', '6', '8', '6', '6', '3', '0', '3', '6', '0', '8', '8', '5', '9', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '0', '9', '6', '7', '9', '7', '7', '1', '0', '4', '1', '9', '5', '8', '9', '5', '3', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '6', '4', '4', '6', '7', '7', '3', '5', '2', '4', '8', '3', '7', '6', '4', '9', '5', '5', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '3', '7', '1', '0', '0', '6', '4', '7', '0', '2', '8', '2', '6', '9', '9', '0', '1', '5', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '3', '1', '5', '7', '2', '6', '8', '6', '4', '2', '3', '6', '2', '0', '5', '2', '6', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '2', '8', '2', '0', '7', '8', '1', '2', '2', '7', '0', '8', '2', '5', '5', '1', '5', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '2', '8', '4', '3', '5', '7', '6', '6', '9', '7', '9', '0', '0', '3', '7', '5', '9', '7', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '8', '6', '4', '5', '5', '4', '1', '4', '6', '6', '8', '7', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '9', '4', '0', '8', '1', '2', '3', '9', '0', '2', '5', '5', '2', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk077Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['7', '7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['6', '6', '2', '1', '6', '9', '4', '8', '7', '4', '3', '8', '3', '6', '5', '4', '0', '2', '7', '9', '3']), .str (String.ofList ['6', '7', '9', '3', '7', '4', '0', '8', '5', '8', '1', '3', '4', '3', '5', '6', '5', '4', '4', '3', '8']), .str (String.ofList ['3', '2', '3', '9', '4', '3', '1', '3', '5', '6', '3', '8', '3', '0', '5', '5', '9', '7', '0', '8', '1']), .str (String.ofList ['5', '9', '8', '5', '8', '6', '6', '8', '6', '6', '3', '0', '3', '6', '0', '8', '8', '5', '9', '6', '4']), .str (String.ofList ['1', '2', '7', '0', '9', '6', '7', '9', '7', '7', '1', '0', '4', '1', '9', '5', '8', '9', '5', '3', '4', '2']), .str (String.ofList ['2', '3', '6', '4', '4', '6', '7', '7', '3', '5', '2', '4', '8', '3', '7', '6', '4', '9', '5', '5', '5', '2']), .str (String.ofList ['1', '9', '3', '7', '1', '0', '0', '6', '4', '7', '0', '2', '8', '2', '6', '9', '9', '0', '1', '5', '2', '0']), .str (String.ofList ['9', '1', '3', '1', '5', '7', '2', '6', '8', '6', '4', '2', '3', '6', '2', '0', '5', '2', '6', '3', '9']), .str (String.ofList ['8', '0', '2', '8', '2', '0', '7', '8', '1', '2', '2', '7', '0', '8', '2', '5', '5', '1', '5', '4', '6']), .str (String.ofList ['8', '0', '2', '8', '4', '3', '5', '7', '6', '6', '9', '7', '9', '0', '0', '3', '7', '5', '9', '7', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '8', '6', '4', '5', '5', '4', '1', '4', '6', '6', '8', '7', '0', '7'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '9', '4', '0', '8', '1', '2', '3', '9', '0', '2', '5', '5', '2', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_077_before_generic"
  err.flush

theorem array_moment_records_chunk_077 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 104)
      (SourceJson.white (momentRecordsChunk077Chars ++ tail)) acc =
      SourceJson.array (fuel + 103) (SourceJson.white tail) (momentRecordsChunk077Push acc) := by rfl

noncomputable def momentRecordsAcc078 : List SourceJson := momentRecordsChunk077Push momentRecordsAcc077

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_077_generic_complete"
  err.flush

noncomputable def momentRecordsChunk078Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '1', '2', '4', '9', '1', '6', '6', '7', '5', '8', '6', '0', '1', '3', '4', '8', '6', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '9', '9', '8', '6', '2', '7', '5', '1', '3', '1', '9', '7', '1', '5', '4', '8', '2', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '9', '2', '1', '9', '5', '6', '8', '6', '3', '4', '2', '6', '7', '1', '6', '3', '6', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '4', '0', '5', '6', '2', '0', '0', '3', '0', '1', '6', '4', '4', '0', '4', '0', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '8', '4', '2', '7', '9', '0', '3', '2', '4', '8', '0', '7', '6', '6', '6', '1', '4', '3', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '6', '6', '6', '1', '2', '8', '0', '7', '6', '4', '6', '1', '1', '6', '2', '7', '6', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '0', '5', '6', '5', '2', '0', '8', '5', '3', '6', '1', '2', '5', '9', '3', '5', '4', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '7', '6', '6', '2', '4', '9', '0', '9', '2', '4', '8', '1', '9', '0', '6', '9', '3', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '4', '4', '6', '1', '2', '3', '2', '5', '9', '3', '4', '2', '6', '0', '1', '2', '2', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '0', '2', '9', '4', '9', '4', '9', '9', '4', '7', '6', '0', '8', '5', '0', '8', '6', '1', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '7', '8', '7', '7', '9', '4', '1', '6', '2', '0', '1', '1', '9', '9', '7', '7', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '8', '6', '7', '5', '0', '0', '3', '7', '5', '5', '5', '3', '0', '2', '5', '6', '7', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk078Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['7', '8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['6', '0', '1', '2', '4', '9', '1', '6', '6', '7', '5', '8', '6', '0', '1', '3', '4', '8', '6', '2', '8']), .str (String.ofList ['6', '2', '9', '9', '8', '6', '2', '7', '5', '1', '3', '1', '9', '7', '1', '5', '4', '8', '2', '0', '6']), .str (String.ofList ['3', '0', '9', '2', '1', '9', '5', '6', '8', '6', '3', '4', '2', '6', '7', '1', '6', '3', '6', '7', '4']), .str (String.ofList ['4', '9', '6', '4', '0', '5', '6', '2', '0', '0', '3', '0', '1', '6', '4', '4', '0', '4', '0', '4', '2']), .str (String.ofList ['1', '2', '8', '8', '4', '2', '7', '9', '0', '3', '2', '4', '8', '0', '7', '6', '6', '6', '1', '4', '3', '2']), .str (String.ofList ['2', '0', '3', '6', '6', '6', '1', '2', '8', '0', '7', '6', '4', '6', '1', '1', '6', '2', '7', '6', '2', '7']), .str (String.ofList ['1', '9', '0', '0', '5', '6', '5', '2', '0', '8', '5', '3', '6', '1', '2', '5', '9', '3', '5', '4', '6', '5']), .str (String.ofList ['8', '9', '7', '6', '6', '2', '4', '9', '0', '9', '2', '4', '8', '1', '9', '0', '6', '9', '3', '6', '9']), .str (String.ofList ['8', '2', '4', '4', '6', '1', '2', '3', '2', '5', '9', '3', '4', '2', '6', '0', '1', '2', '2', '9', '6']), .str (String.ofList ['8', '2', '0', '2', '9', '4', '9', '4', '9', '9', '4', '7', '6', '0', '8', '5', '0', '8', '6', '1', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '7', '8', '7', '7', '9', '4', '1', '6', '2', '0', '1', '1', '9', '9', '7', '7', '3', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '8', '6', '7', '5', '0', '0', '3', '7', '5', '5', '5', '3', '0', '2', '5', '6', '7', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_078_before_generic"
  err.flush

theorem array_moment_records_chunk_078 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 103)
      (SourceJson.white (momentRecordsChunk078Chars ++ tail)) acc =
      SourceJson.array (fuel + 102) (SourceJson.white tail) (momentRecordsChunk078Push acc) := by rfl

noncomputable def momentRecordsAcc079 : List SourceJson := momentRecordsChunk078Push momentRecordsAcc078

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_078_generic_complete"
  err.flush

noncomputable def momentRecordsChunk079Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '5', '5', '4', '1', '7', '7', '3', '9', '5', '6', '0', '9', '1', '0', '7', '2', '0', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '2', '2', '6', '4', '4', '2', '6', '9', '0', '8', '4', '7', '6', '8', '2', '6', '8', '2', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '3', '6', '0', '6', '1', '6', '1', '5', '6', '6', '8', '2', '1', '9', '6', '6', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '5', '6', '8', '0', '6', '1', '1', '1', '3', '3', '8', '0', '9', '1', '9', '8', '1', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '4', '3', '5', '8', '7', '2', '2', '8', '4', '4', '2', '0', '9', '7', '2', '2', '7', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '7', '1', '4', '4', '4', '3', '8', '5', '2', '8', '6', '0', '6', '9', '4', '3', '0', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '4', '1', '4', '5', '0', '9', '9', '2', '8', '8', '4', '5', '3', '7', '7', '6', '7', '8', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '0', '9', '8', '0', '6', '8', '1', '5', '8', '0', '6', '9', '5', '1', '0', '0', '3', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '1', '7', '1', '6', '5', '4', '4', '8', '8', '0', '0', '7', '9', '7', '3', '0', '8', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '2', '5', '1', '3', '1', '2', '0', '5', '1', '9', '0', '5', '5', '2', '7', '8', '3', '1', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '4', '6', '0', '2', '4', '1', '0', '9', '2', '9', '1', '2', '8', '0', '9', '7', '9', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '5', '7', '8', '7', '9', '3', '8', '8', '4', '5', '9', '5', '8', '4', '6', '9', '0', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk079Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['7', '9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['6', '0', '5', '5', '4', '1', '7', '7', '3', '9', '5', '6', '0', '9', '1', '0', '7', '2', '0', '0', '9']), .str (String.ofList ['6', '2', '2', '2', '6', '4', '4', '2', '6', '9', '0', '8', '4', '7', '6', '8', '2', '6', '8', '2', '3']), .str (String.ofList ['2', '9', '9', '3', '6', '0', '6', '1', '6', '1', '5', '6', '6', '8', '2', '1', '9', '6', '6', '5', '9']), .str (String.ofList ['5', '0', '5', '6', '8', '0', '6', '1', '1', '1', '3', '3', '8', '0', '9', '1', '9', '8', '1', '2', '4']), .str (String.ofList ['1', '2', '4', '4', '3', '5', '8', '7', '2', '2', '8', '4', '4', '2', '0', '9', '7', '2', '2', '7', '0', '6']), .str (String.ofList ['2', '0', '3', '7', '1', '4', '4', '4', '3', '8', '5', '2', '8', '6', '0', '6', '9', '4', '3', '0', '6', '9']), .str (String.ofList ['1', '8', '4', '1', '4', '5', '0', '9', '9', '2', '8', '8', '4', '5', '3', '7', '7', '6', '7', '8', '5', '5']), .str (String.ofList ['9', '2', '0', '9', '8', '0', '6', '8', '1', '5', '8', '0', '6', '9', '5', '1', '0', '0', '3', '6', '3']), .str (String.ofList ['9', '0', '1', '7', '1', '6', '5', '4', '4', '8', '8', '0', '0', '7', '9', '7', '3', '0', '8', '5', '7']), .str (String.ofList ['8', '9', '2', '5', '1', '3', '1', '2', '0', '5', '1', '9', '0', '5', '5', '2', '7', '8', '3', '1', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '4', '4', '6', '0', '2', '4', '1', '0', '9', '2', '9', '1', '2', '8', '0', '9', '7', '9', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '4', '5', '7', '8', '7', '9', '3', '8', '8', '4', '5', '9', '5', '8', '4', '6', '9', '0', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_079_before_generic"
  err.flush

theorem array_moment_records_chunk_079 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 102)
      (SourceJson.white (momentRecordsChunk079Chars ++ tail)) acc =
      SourceJson.array (fuel + 101) (SourceJson.white tail) (momentRecordsChunk079Push acc) := by rfl

noncomputable def momentRecordsAcc080 : List SourceJson := momentRecordsChunk079Push momentRecordsAcc079

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_079_generic_complete"
  err.flush

noncomputable def momentRecordsBlock019Chars : List Char := momentRecordsChunk076Chars ++ momentRecordsChunk077Chars ++ momentRecordsChunk078Chars ++ momentRecordsChunk079Chars
noncomputable def momentRecordsBlock019Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk079Push (momentRecordsChunk078Push (momentRecordsChunk077Push (momentRecordsChunk076Push (acc))))

theorem array_moment_records_block_019 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 105)
      (SourceJson.white (momentRecordsBlock019Chars ++ tail)) acc =
      SourceJson.array (fuel + 101) (SourceJson.white tail) (momentRecordsBlock019Push acc) := by
  have hinput : momentRecordsBlock019Chars ++ tail = momentRecordsChunk076Chars ++ (momentRecordsChunk077Chars ++ (momentRecordsChunk078Chars ++ (momentRecordsChunk079Chars ++ (tail)))) := by
    simp only [momentRecordsBlock019Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 105) (SourceJson.white (momentRecordsBlock019Chars ++ tail)) acc =
        SourceJson.array (fuel + 105) (SourceJson.white (momentRecordsChunk076Chars ++ (momentRecordsChunk077Chars ++ (momentRecordsChunk078Chars ++ (momentRecordsChunk079Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 105) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 104) (SourceJson.white (momentRecordsChunk077Chars ++ (momentRecordsChunk078Chars ++ (momentRecordsChunk079Chars ++ (tail))))) (momentRecordsChunk076Push (acc)) := array_moment_records_chunk_076 fuel (momentRecordsChunk077Chars ++ (momentRecordsChunk078Chars ++ (momentRecordsChunk079Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 103) (SourceJson.white (momentRecordsChunk078Chars ++ (momentRecordsChunk079Chars ++ (tail)))) (momentRecordsChunk077Push (momentRecordsChunk076Push (acc))) := array_moment_records_chunk_077 fuel (momentRecordsChunk078Chars ++ (momentRecordsChunk079Chars ++ (tail))) (momentRecordsChunk076Push (acc))
    _ = SourceJson.array (fuel + 102) (SourceJson.white (momentRecordsChunk079Chars ++ (tail))) (momentRecordsChunk078Push (momentRecordsChunk077Push (momentRecordsChunk076Push (acc)))) := array_moment_records_chunk_078 fuel (momentRecordsChunk079Chars ++ (tail)) (momentRecordsChunk077Push (momentRecordsChunk076Push (acc)))
    _ = SourceJson.array (fuel + 101) (SourceJson.white tail) (momentRecordsBlock019Push acc) := array_moment_records_chunk_079 fuel (tail) (momentRecordsChunk078Push (momentRecordsChunk077Push (momentRecordsChunk076Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_019_before_raw_binding"
  err.flush

theorem moment_records_block_019_prefix :
    (momentRest01 39865).take 2071 = momentRecordsBlock019Chars := by rfl

theorem moment_records_block_019_split :
    momentRest01 39865 = momentRecordsBlock019Chars ++ momentRest01 41936 := by
  calc
    momentRest01 39865 =
        (momentRest01 39865).take 2071 ++ (momentRest01 39865).drop 2071 :=
      (List.take_append_drop 2071 (momentRest01 39865)).symm
    _ = momentRecordsBlock019Chars ++ (momentRest01 39865).drop 2071 :=
      congrArg (fun p => p ++ (momentRest01 39865).drop 2071) moment_records_block_019_prefix
    _ = momentRecordsBlock019Chars ++ momentRest01 41936 :=
      congrArg (fun rest => momentRecordsBlock019Chars ++ rest) (momentRest01_drop 39865 2071)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_019_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_019 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 105)
      (SourceJson.white (momentRest01 39865)) acc =
      SourceJson.array (fuel + 101) (SourceJson.white (momentRest01 41936)) (momentRecordsBlock019Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 105) (SourceJson.white s) acc)
      moment_records_block_019_split).trans (array_moment_records_block_019 fuel (momentRest01 41936) acc)

theorem moment_records_through_block_019 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 101) (SourceJson.white (momentRest01 41936)) momentRecordsAcc080 := by
  exact (moment_records_through_block_018 fuel).trans (array_moment_records_original_block_019 fuel momentRecordsAcc076)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_019_complete"
  err.flush

#print axioms array_moment_records_chunk_076
#print axioms array_moment_records_chunk_077
#print axioms array_moment_records_chunk_078
#print axioms array_moment_records_chunk_079
#print axioms array_moment_records_block_019
#print axioms moment_records_block_019_prefix
#print axioms moment_records_block_019_split
#print axioms array_moment_records_original_block_019
#print axioms moment_records_through_block_019

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
