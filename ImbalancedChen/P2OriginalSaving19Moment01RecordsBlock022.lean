import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock021

/-! Original moment records block 22. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk088Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '2', '9', '5', '5', '4', '5', '5', '2', '9', '2', '4', '3', '4', '4', '5', '0', '8', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '9', '0', '3', '4', '9', '6', '2', '3', '7', '0', '1', '0', '6', '7', '2', '1', '6', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '1', '0', '2', '0', '6', '7', '1', '3', '4', '3', '6', '1', '5', '5', '3', '2', '6', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '7', '1', '2', '0', '5', '9', '2', '5', '6', '6', '8', '8', '7', '3', '7', '0', '2', '7', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '9', '9', '1', '1', '4', '8', '2', '6', '1', '0', '4', '9', '7', '2', '7', '0', '5', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '4', '9', '5', '0', '3', '2', '7', '4', '9', '2', '0', '2', '3', '0', '2', '7', '4', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '7', '3', '1', '8', '9', '0', '4', '1', '2', '4', '8', '2', '0', '4', '3', '7', '2', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '4', '0', '9', '4', '4', '0', '5', '4', '6', '8', '0', '3', '4', '8', '6', '1', '1', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '3', '3', '7', '9', '9', '7', '7', '4', '6', '8', '8', '6', '1', '2', '7', '2', '1', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '4', '2', '3', '6', '1', '0', '8', '5', '3', '1', '1', '8', '1', '7', '8', '0', '4', '9', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '2', '5', '2', '8', '1', '0', '5', '2', '6', '5', '2', '0', '5', '4', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '9', '3', '3', '3', '1', '9', '6', '5', '4', '0', '0', '5', '6', '7', '0', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk088Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['8', '8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '5', '2', '9', '5', '5', '4', '5', '5', '2', '9', '2', '4', '3', '4', '4', '5', '0', '8', '4', '1']), .str (String.ofList ['1', '4', '2', '9', '0', '3', '4', '9', '6', '2', '3', '7', '0', '1', '0', '6', '7', '2', '1', '6', '2', '1']), .str (String.ofList ['2', '9', '1', '0', '2', '0', '6', '7', '1', '3', '4', '3', '6', '1', '5', '5', '3', '2', '6', '6', '3']), .str (String.ofList ['6', '3', '7', '1', '2', '0', '5', '9', '2', '5', '6', '6', '8', '8', '7', '3', '7', '0', '2', '7', '9']), .str (String.ofList ['1', '3', '7', '9', '9', '1', '1', '4', '8', '2', '6', '1', '0', '4', '9', '7', '2', '7', '0', '5', '3', '8']), .str (String.ofList ['1', '8', '9', '4', '9', '5', '0', '3', '2', '7', '4', '9', '2', '0', '2', '3', '0', '2', '7', '4', '5', '6']), .str (String.ofList ['1', '4', '5', '7', '3', '1', '8', '9', '0', '4', '1', '2', '4', '8', '2', '0', '4', '3', '7', '2', '5', '6']), .str (String.ofList ['1', '1', '8', '4', '0', '9', '4', '4', '0', '5', '4', '6', '8', '0', '3', '4', '8', '6', '1', '1', '1', '7']), .str (String.ofList ['1', '1', '4', '3', '3', '7', '9', '9', '7', '7', '4', '6', '8', '8', '6', '1', '2', '7', '2', '1', '3', '1']), .str (String.ofList ['1', '5', '8', '4', '2', '3', '6', '1', '0', '8', '5', '3', '1', '1', '8', '1', '7', '8', '0', '4', '9', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '6', '2', '5', '2', '8', '1', '0', '5', '2', '6', '5', '2', '0', '5', '4', '2', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '6', '9', '3', '3', '3', '1', '9', '6', '5', '4', '0', '0', '5', '6', '7', '0', '6']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_088_before_generic"
  err.flush

theorem array_moment_records_chunk_088 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRecordsChunk088Chars ++ tail)) acc =
      SourceJson.array (fuel + 92) (SourceJson.white tail) (momentRecordsChunk088Push acc) := by rfl

noncomputable def momentRecordsAcc089 : List SourceJson := momentRecordsChunk088Push momentRecordsAcc088

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_088_generic_complete"
  err.flush

noncomputable def momentRecordsChunk089Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '8', '8', '5', '4', '2', '8', '5', '5', '4', '5', '6', '7', '5', '7', '2', '9', '0', '2', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '3', '0', '3', '1', '5', '7', '0', '0', '8', '3', '9', '0', '9', '4', '9', '9', '1', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '9', '7', '9', '6', '5', '0', '5', '4', '7', '9', '7', '3', '1', '5', '1', '0', '4', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '6', '9', '7', '3', '5', '6', '0', '4', '8', '3', '1', '9', '7', '1', '3', '6', '1', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '7', '8', '1', '5', '4', '4', '3', '8', '2', '5', '2', '8', '5', '4', '5', '7', '3', '0', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '1', '3', '7', '6', '5', '9', '8', '4', '1', '7', '6', '9', '9', '2', '1', '7', '0', '6', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '5', '2', '5', '5', '7', '5', '9', '4', '1', '7', '8', '9', '1', '8', '1', '7', '9', '9', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '7', '5', '2', '8', '8', '0', '8', '4', '4', '2', '9', '8', '5', '0', '0', '1', '0', '8', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '0', '4', '0', '6', '2', '5', '9', '2', '8', '1', '0', '2', '5', '8', '3', '3', '9', '6', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '0', '4', '1', '5', '8', '3', '9', '6', '0', '5', '1', '6', '1', '9', '1', '0', '6', '9', '1', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '2', '4', '1', '7', '7', '7', '2', '0', '7', '5', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '3', '5', '8', '3', '1', '4', '3', '9', '5', '5', '0', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk089Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['8', '9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '9', '8', '8', '5', '4', '2', '8', '5', '5', '4', '5', '6', '7', '5', '7', '2', '9', '0', '2', '1', '3']), .str (String.ofList ['2', '0', '8', '3', '0', '3', '1', '5', '7', '0', '0', '8', '3', '9', '0', '9', '4', '9', '9', '1', '5', '1']), .str (String.ofList ['3', '0', '9', '7', '9', '6', '5', '0', '5', '4', '7', '9', '7', '3', '1', '5', '1', '0', '4', '8', '1']), .str (String.ofList ['7', '6', '6', '9', '7', '3', '5', '6', '0', '4', '8', '3', '1', '9', '7', '1', '3', '6', '1', '7', '1']), .str (String.ofList ['1', '4', '7', '8', '1', '5', '4', '4', '3', '8', '2', '5', '2', '8', '5', '4', '5', '7', '3', '0', '8', '6']), .str (String.ofList ['2', '3', '1', '3', '7', '6', '5', '9', '8', '4', '1', '7', '6', '9', '9', '2', '1', '7', '0', '6', '8', '6']), .str (String.ofList ['1', '7', '2', '5', '2', '5', '5', '7', '5', '9', '4', '1', '7', '8', '9', '1', '8', '1', '7', '9', '9', '7']), .str (String.ofList ['1', '4', '7', '5', '2', '8', '8', '0', '8', '4', '4', '2', '9', '8', '5', '0', '0', '1', '0', '8', '0', '2']), .str (String.ofList ['1', '5', '0', '4', '0', '6', '2', '5', '9', '2', '8', '1', '0', '2', '5', '8', '3', '3', '9', '6', '4', '6']), .str (String.ofList ['1', '5', '0', '4', '1', '5', '8', '3', '9', '6', '0', '5', '1', '6', '1', '9', '1', '0', '6', '9', '1', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '2', '4', '1', '7', '7', '7', '2', '0', '7', '5', '0', '6'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '3', '5', '8', '3', '1', '4', '3', '9', '5', '5', '0', '6']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_089_before_generic"
  err.flush

theorem array_moment_records_chunk_089 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 92)
      (SourceJson.white (momentRecordsChunk089Chars ++ tail)) acc =
      SourceJson.array (fuel + 91) (SourceJson.white tail) (momentRecordsChunk089Push acc) := by rfl

noncomputable def momentRecordsAcc090 : List SourceJson := momentRecordsChunk089Push momentRecordsAcc089

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_089_generic_complete"
  err.flush

noncomputable def momentRecordsChunk090Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '3', '0', '4', '5', '2', '3', '1', '0', '5', '0', '3', '6', '2', '8', '4', '5', '9', '8', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '8', '9', '8', '0', '8', '6', '2', '0', '1', '9', '7', '7', '3', '8', '8', '1', '0', '3', '4', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '3', '6', '9', '7', '0', '0', '8', '9', '2', '2', '4', '8', '0', '5', '9', '1', '7', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '1', '7', '0', '7', '6', '4', '9', '8', '9', '7', '9', '9', '6', '3', '7', '0', '3', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '2', '0', '0', '4', '3', '4', '5', '6', '5', '1', '8', '1', '0', '2', '6', '3', '3', '3', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '4', '9', '1', '2', '3', '8', '2', '4', '6', '0', '0', '5', '6', '4', '1', '0', '5', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '6', '5', '3', '2', '2', '1', '3', '9', '8', '2', '7', '1', '5', '0', '5', '8', '5', '1', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '4', '8', '1', '8', '3', '7', '9', '7', '1', '2', '6', '4', '5', '3', '8', '8', '3', '4', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '9', '7', '9', '3', '1', '3', '0', '0', '5', '1', '2', '4', '9', '3', '9', '8', '6', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '4', '7', '6', '3', '3', '4', '5', '4', '3', '5', '3', '5', '0', '1', '8', '9', '8', '4', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '4', '3', '3', '9', '6', '7', '5', '1', '6', '7', '1', '8', '5', '6', '6', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '5', '4', '4', '1', '4', '7', '1', '8', '2', '9', '4', '3', '0', '7', '2', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk090Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['9', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '7', '3', '0', '4', '5', '2', '3', '1', '0', '5', '0', '3', '6', '2', '8', '4', '5', '9', '8', '8', '4']), .str (String.ofList ['1', '8', '8', '9', '8', '0', '8', '6', '2', '0', '1', '9', '7', '7', '3', '8', '8', '1', '0', '3', '4', '7']), .str (String.ofList ['2', '9', '3', '6', '9', '7', '0', '0', '8', '9', '2', '2', '4', '8', '0', '5', '9', '1', '7', '5', '6']), .str (String.ofList ['6', '9', '1', '7', '0', '7', '6', '4', '9', '8', '9', '7', '9', '9', '6', '3', '7', '0', '3', '7', '1']), .str (String.ofList ['1', '4', '9', '2', '0', '0', '4', '3', '4', '5', '6', '5', '1', '8', '1', '0', '2', '6', '3', '3', '3', '3']), .str (String.ofList ['1', '8', '9', '4', '9', '1', '2', '3', '8', '2', '4', '6', '0', '0', '5', '6', '4', '1', '0', '5', '2', '5']), .str (String.ofList ['1', '6', '6', '5', '3', '2', '2', '1', '3', '9', '8', '2', '7', '1', '5', '0', '5', '8', '5', '1', '6', '3']), .str (String.ofList ['1', '4', '1', '4', '8', '1', '8', '3', '7', '9', '7', '1', '2', '6', '4', '5', '3', '8', '8', '3', '4', '7']), .str (String.ofList ['1', '3', '7', '9', '7', '9', '3', '1', '3', '0', '0', '5', '1', '2', '4', '9', '3', '9', '8', '6', '6', '5']), .str (String.ofList ['1', '5', '8', '4', '7', '6', '3', '3', '4', '5', '4', '3', '5', '3', '5', '0', '1', '8', '9', '8', '4', '4'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '4', '3', '3', '9', '6', '7', '5', '1', '6', '7', '1', '8', '5', '6', '6', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '5', '4', '4', '1', '4', '7', '1', '8', '2', '9', '4', '3', '0', '7', '2', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_090_before_generic"
  err.flush

theorem array_moment_records_chunk_090 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 91)
      (SourceJson.white (momentRecordsChunk090Chars ++ tail)) acc =
      SourceJson.array (fuel + 90) (SourceJson.white tail) (momentRecordsChunk090Push acc) := by rfl

noncomputable def momentRecordsAcc091 : List SourceJson := momentRecordsChunk090Push momentRecordsAcc090

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_090_generic_complete"
  err.flush

noncomputable def momentRecordsChunk091Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '7', '3', '4', '3', '8', '0', '5', '8', '8', '2', '5', '1', '5', '9', '3', '9', '8', '8', '3', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '2', '1', '2', '7', '6', '6', '0', '6', '9', '4', '2', '4', '1', '9', '8', '4', '7', '5', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '8', '1', '6', '0', '8', '3', '9', '0', '1', '8', '3', '9', '1', '6', '7', '4', '0', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '6', '5', '5', '0', '4', '1', '3', '6', '5', '5', '6', '8', '9', '9', '8', '8', '4', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '3', '4', '2', '0', '7', '8', '5', '3', '3', '5', '7', '2', '8', '8', '2', '9', '3', '6', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '1', '7', '9', '1', '2', '3', '2', '7', '8', '6', '1', '8', '9', '1', '7', '2', '4', '8', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '5', '3', '3', '3', '9', '3', '2', '0', '2', '0', '5', '9', '0', '9', '5', '9', '1', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '6', '1', '2', '2', '1', '9', '6', '8', '0', '2', '6', '7', '3', '7', '1', '3', '9', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '2', '8', '3', '5', '4', '1', '6', '8', '6', '5', '3', '4', '0', '8', '7', '3', '5', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '2', '9', '5', '3', '2', '5', '6', '3', '0', '6', '1', '9', '2', '5', '6', '8', '4', '8', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '5', '1', '7', '8', '2', '7', '5', '6', '3', '2', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '5', '4', '8', '6', '4', '8', '6', '4', '9', '6', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk091Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['9', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '2', '7', '3', '4', '3', '8', '0', '5', '8', '8', '2', '5', '1', '5', '9', '3', '9', '8', '8', '3', '3']), .str (String.ofList ['2', '2', '2', '1', '2', '7', '6', '6', '0', '6', '9', '4', '2', '4', '1', '9', '8', '4', '7', '5', '1', '0']), .str (String.ofList ['2', '5', '8', '1', '6', '0', '8', '3', '9', '0', '1', '8', '3', '9', '1', '6', '7', '4', '0', '0', '7']), .str (String.ofList ['8', '1', '6', '5', '5', '0', '4', '1', '3', '6', '5', '5', '6', '8', '9', '9', '8', '8', '4', '8', '4']), .str (String.ofList ['1', '2', '3', '4', '2', '0', '7', '8', '5', '3', '3', '5', '7', '2', '8', '8', '2', '9', '3', '6', '1', '6']), .str (String.ofList ['2', '3', '1', '7', '9', '1', '2', '3', '2', '7', '8', '6', '1', '8', '9', '1', '7', '2', '4', '8', '8', '0']), .str (String.ofList ['1', '6', '0', '5', '3', '3', '3', '9', '3', '2', '0', '2', '0', '5', '9', '0', '9', '5', '9', '1', '6', '4']), .str (String.ofList ['1', '4', '3', '6', '1', '2', '2', '1', '9', '6', '8', '0', '2', '6', '7', '3', '7', '1', '3', '9', '3', '4']), .str (String.ofList ['1', '2', '7', '2', '8', '3', '5', '4', '1', '6', '8', '6', '5', '3', '4', '0', '8', '7', '3', '5', '7', '4']), .str (String.ofList ['1', '2', '7', '2', '9', '5', '3', '2', '5', '6', '3', '0', '6', '1', '9', '2', '5', '6', '8', '4', '8', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '5', '1', '7', '8', '2', '7', '5', '6', '3', '2', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '5', '4', '8', '6', '4', '8', '6', '4', '9', '6', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_091_before_generic"
  err.flush

theorem array_moment_records_chunk_091 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 90)
      (SourceJson.white (momentRecordsChunk091Chars ++ tail)) acc =
      SourceJson.array (fuel + 89) (SourceJson.white tail) (momentRecordsChunk091Push acc) := by rfl

noncomputable def momentRecordsAcc092 : List SourceJson := momentRecordsChunk091Push momentRecordsAcc091

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_091_generic_complete"
  err.flush

noncomputable def momentRecordsBlock022Chars : List Char := momentRecordsChunk088Chars ++ momentRecordsChunk089Chars ++ momentRecordsChunk090Chars ++ momentRecordsChunk091Chars
noncomputable def momentRecordsBlock022Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk091Push (momentRecordsChunk090Push (momentRecordsChunk089Push (momentRecordsChunk088Push (acc))))

theorem array_moment_records_block_022 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRecordsBlock022Chars ++ tail)) acc =
      SourceJson.array (fuel + 89) (SourceJson.white tail) (momentRecordsBlock022Push acc) := by
  have hinput : momentRecordsBlock022Chars ++ tail = momentRecordsChunk088Chars ++ (momentRecordsChunk089Chars ++ (momentRecordsChunk090Chars ++ (momentRecordsChunk091Chars ++ (tail)))) := by
    simp only [momentRecordsBlock022Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 93) (SourceJson.white (momentRecordsBlock022Chars ++ tail)) acc =
        SourceJson.array (fuel + 93) (SourceJson.white (momentRecordsChunk088Chars ++ (momentRecordsChunk089Chars ++ (momentRecordsChunk090Chars ++ (momentRecordsChunk091Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 93) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 92) (SourceJson.white (momentRecordsChunk089Chars ++ (momentRecordsChunk090Chars ++ (momentRecordsChunk091Chars ++ (tail))))) (momentRecordsChunk088Push (acc)) := array_moment_records_chunk_088 fuel (momentRecordsChunk089Chars ++ (momentRecordsChunk090Chars ++ (momentRecordsChunk091Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 91) (SourceJson.white (momentRecordsChunk090Chars ++ (momentRecordsChunk091Chars ++ (tail)))) (momentRecordsChunk089Push (momentRecordsChunk088Push (acc))) := array_moment_records_chunk_089 fuel (momentRecordsChunk090Chars ++ (momentRecordsChunk091Chars ++ (tail))) (momentRecordsChunk088Push (acc))
    _ = SourceJson.array (fuel + 90) (SourceJson.white (momentRecordsChunk091Chars ++ (tail))) (momentRecordsChunk090Push (momentRecordsChunk089Push (momentRecordsChunk088Push (acc)))) := array_moment_records_chunk_090 fuel (momentRecordsChunk091Chars ++ (tail)) (momentRecordsChunk089Push (momentRecordsChunk088Push (acc)))
    _ = SourceJson.array (fuel + 89) (SourceJson.white tail) (momentRecordsBlock022Push acc) := array_moment_records_chunk_091 fuel (tail) (momentRecordsChunk090Push (momentRecordsChunk089Push (momentRecordsChunk088Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_022_before_raw_binding"
  err.flush

theorem moment_records_block_022_prefix :
    (momentRest01 46128).take 2080 = momentRecordsBlock022Chars := by rfl

theorem moment_records_block_022_split :
    momentRest01 46128 = momentRecordsBlock022Chars ++ momentRest01 48208 := by
  calc
    momentRest01 46128 =
        (momentRest01 46128).take 2080 ++ (momentRest01 46128).drop 2080 :=
      (List.take_append_drop 2080 (momentRest01 46128)).symm
    _ = momentRecordsBlock022Chars ++ (momentRest01 46128).drop 2080 :=
      congrArg (fun p => p ++ (momentRest01 46128).drop 2080) moment_records_block_022_prefix
    _ = momentRecordsBlock022Chars ++ momentRest01 48208 :=
      congrArg (fun rest => momentRecordsBlock022Chars ++ rest) (momentRest01_drop 46128 2080)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_022_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_022 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRest01 46128)) acc =
      SourceJson.array (fuel + 89) (SourceJson.white (momentRest01 48208)) (momentRecordsBlock022Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 93) (SourceJson.white s) acc)
      moment_records_block_022_split).trans (array_moment_records_block_022 fuel (momentRest01 48208) acc)

theorem moment_records_through_block_022 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 89) (SourceJson.white (momentRest01 48208)) momentRecordsAcc092 := by
  exact (moment_records_through_block_021 fuel).trans (array_moment_records_original_block_022 fuel momentRecordsAcc088)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_022_complete"
  err.flush

#print axioms array_moment_records_chunk_088
#print axioms array_moment_records_chunk_089
#print axioms array_moment_records_chunk_090
#print axioms array_moment_records_chunk_091
#print axioms array_moment_records_block_022
#print axioms moment_records_block_022_prefix
#print axioms moment_records_block_022_split
#print axioms array_moment_records_original_block_022
#print axioms moment_records_through_block_022

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
