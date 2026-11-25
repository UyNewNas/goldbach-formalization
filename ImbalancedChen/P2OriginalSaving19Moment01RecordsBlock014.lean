import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock013

/-! Original moment records block 14. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk056Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '1', '7', '9', '9', '3', '8', '0', '0', '3', '6', '4', '7', '2', '7', '0', '7', '1', '6', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '1', '3', '4', '0', '9', '3', '0', '5', '7', '7', '8', '4', '7', '7', '3', '4', '9', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '9', '1', '5', '7', '1', '4', '8', '0', '3', '0', '6', '6', '2', '1', '0', '3', '7', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '9', '8', '4', '2', '9', '9', '2', '3', '4', '7', '6', '3', '1', '2', '9', '1', '5', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '5', '5', '1', '7', '7', '6', '5', '1', '3', '6', '5', '2', '0', '8', '7', '9', '7', '7', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '1', '6', '6', '5', '2', '3', '6', '2', '6', '4', '4', '3', '5', '7', '3', '7', '2', '9', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '1', '9', '4', '6', '1', '8', '2', '0', '4', '1', '4', '1', '8', '8', '9', '9', '9', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '1', '5', '9', '6', '8', '3', '4', '1', '1', '0', '0', '2', '4', '7', '7', '5', '9', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '1', '5', '7', '4', '1', '2', '9', '8', '5', '5', '3', '6', '9', '9', '6', '7', '4', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '8', '6', '4', '6', '6', '5', '2', '0', '3', '4', '1', '8', '8', '2', '8', '0', '6', '4', '0', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '4', '9', '8', '6', '7', '2', '2', '4', '9', '3', '2', '5', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '5', '3', '7', '6', '9', '6', '8', '3', '6', '3', '5', '8', '8', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk056Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5', '6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '1', '1', '7', '9', '9', '3', '8', '0', '0', '3', '6', '4', '7', '2', '7', '0', '7', '1', '6', '6', '7']), .str (String.ofList ['2', '2', '9', '1', '3', '4', '0', '9', '3', '0', '5', '7', '7', '8', '4', '7', '7', '3', '4', '9', '5', '2']), .str (String.ofList ['2', '5', '6', '9', '1', '5', '7', '1', '4', '8', '0', '3', '0', '6', '6', '2', '1', '0', '3', '7', '7']), .str (String.ofList ['5', '4', '9', '8', '4', '2', '9', '9', '2', '3', '4', '7', '6', '3', '1', '2', '9', '1', '5', '6', '1']), .str (String.ofList ['1', '0', '2', '5', '5', '1', '7', '7', '6', '5', '1', '3', '6', '5', '2', '0', '8', '7', '9', '7', '7', '7']), .str (String.ofList ['1', '7', '1', '6', '6', '5', '2', '3', '6', '2', '6', '4', '4', '3', '5', '7', '3', '7', '2', '9', '6', '3']), .str (String.ofList ['1', '4', '8', '1', '9', '4', '6', '1', '8', '2', '0', '4', '1', '4', '1', '8', '8', '9', '9', '9', '7', '8']), .str (String.ofList ['9', '9', '1', '5', '9', '6', '8', '3', '4', '1', '1', '0', '0', '2', '4', '7', '7', '5', '9', '1', '0']), .str (String.ofList ['9', '9', '1', '5', '7', '4', '1', '2', '9', '8', '5', '5', '3', '6', '9', '9', '6', '7', '4', '0', '6']), .str (String.ofList ['1', '9', '8', '6', '4', '6', '6', '5', '2', '0', '3', '4', '1', '8', '8', '2', '8', '0', '6', '4', '0', '7'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '4', '9', '8', '6', '7', '2', '2', '4', '9', '3', '2', '5', '9', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '5', '3', '7', '6', '9', '6', '8', '3', '6', '3', '5', '8', '8', '0']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_056_before_generic"
  err.flush

theorem array_moment_records_chunk_056 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 125)
      (SourceJson.white (momentRecordsChunk056Chars ++ tail)) acc =
      SourceJson.array (fuel + 124) (SourceJson.white tail) (momentRecordsChunk056Push acc) := by rfl

noncomputable def momentRecordsAcc057 : List SourceJson := momentRecordsChunk056Push momentRecordsAcc056

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_056_generic_complete"
  err.flush

noncomputable def momentRecordsChunk057Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '7', '7', '5', '6', '4', '7', '5', '5', '0', '2', '3', '2', '0', '6', '8', '5', '6', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '0', '4', '6', '9', '3', '1', '6', '0', '7', '4', '6', '4', '0', '7', '1', '8', '8', '3', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '4', '6', '1', '7', '7', '2', '8', '7', '2', '4', '3', '8', '2', '5', '8', '5', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '0', '6', '4', '8', '7', '2', '0', '2', '2', '3', '8', '9', '3', '3', '5', '6', '1', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '7', '6', '3', '1', '7', '9', '8', '0', '0', '3', '0', '3', '0', '4', '2', '5', '5', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '1', '8', '8', '6', '7', '6', '3', '6', '1', '1', '4', '5', '9', '7', '1', '1', '9', '4', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '5', '8', '5', '5', '2', '1', '3', '6', '8', '0', '6', '7', '2', '5', '5', '5', '4', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '6', '5', '1', '0', '2', '4', '3', '0', '3', '2', '8', '5', '9', '3', '3', '1', '7', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '6', '4', '9', '7', '4', '9', '1', '6', '3', '0', '8', '1', '0', '6', '3', '6', '8', '4', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '5', '5', '5', '2', '6', '6', '3', '1', '3', '5', '5', '5', '2', '9', '0', '6', '6', '3', '9', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '8', '0', '3', '3', '2', '5', '7', '3', '8', '3', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '9', '1', '6', '9', '5', '8', '4', '8', '0', '1', '0', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk057Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5', '7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '0', '4', '7', '7', '5', '6', '4', '7', '5', '5', '0', '2', '3', '2', '0', '6', '8', '5', '6', '0', '0']), .str (String.ofList ['2', '0', '0', '4', '6', '9', '3', '1', '6', '0', '7', '4', '6', '4', '0', '7', '1', '8', '8', '3', '2', '6']), .str (String.ofList ['2', '0', '5', '4', '6', '1', '7', '7', '2', '8', '7', '2', '4', '3', '8', '2', '5', '8', '5', '6', '7']), .str (String.ofList ['5', '9', '0', '6', '4', '8', '7', '2', '0', '2', '2', '3', '8', '9', '3', '3', '5', '6', '1', '2', '6']), .str (String.ofList ['1', '0', '8', '7', '6', '3', '1', '7', '9', '8', '0', '0', '3', '0', '3', '0', '4', '2', '5', '5', '6', '9']), .str (String.ofList ['1', '7', '1', '8', '8', '6', '7', '6', '3', '6', '1', '1', '4', '5', '9', '7', '1', '1', '9', '4', '7', '2']), .str (String.ofList ['1', '2', '6', '5', '8', '5', '5', '2', '1', '3', '6', '8', '0', '6', '7', '2', '5', '5', '5', '4', '3', '8']), .str (String.ofList ['9', '3', '6', '5', '1', '0', '2', '4', '3', '0', '3', '2', '8', '5', '9', '3', '3', '1', '7', '9', '6']), .str (String.ofList ['9', '3', '6', '4', '9', '7', '4', '9', '1', '6', '3', '0', '8', '1', '0', '6', '3', '6', '8', '4', '0']), .str (String.ofList ['1', '8', '5', '5', '5', '2', '6', '6', '3', '1', '3', '5', '5', '5', '2', '9', '0', '6', '6', '3', '9', '0'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '8', '0', '3', '3', '2', '5', '7', '3', '8', '3', '4', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '9', '1', '6', '9', '5', '8', '4', '8', '0', '1', '0', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_057_before_generic"
  err.flush

theorem array_moment_records_chunk_057 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 124)
      (SourceJson.white (momentRecordsChunk057Chars ++ tail)) acc =
      SourceJson.array (fuel + 123) (SourceJson.white tail) (momentRecordsChunk057Push acc) := by rfl

noncomputable def momentRecordsAcc058 : List SourceJson := momentRecordsChunk057Push momentRecordsAcc057

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_057_generic_complete"
  err.flush

noncomputable def momentRecordsChunk058Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '3', '5', '0', '2', '9', '2', '8', '4', '2', '0', '2', '9', '1', '4', '1', '8', '6', '7', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '9', '9', '2', '1', '3', '1', '0', '0', '0', '4', '0', '4', '5', '0', '7', '0', '4', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '1', '8', '4', '1', '2', '1', '9', '7', '3', '1', '5', '5', '4', '0', '3', '5', '5', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '1', '5', '2', '4', '4', '2', '7', '8', '3', '4', '5', '2', '6', '9', '3', '0', '5', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '6', '5', '6', '9', '4', '1', '0', '8', '8', '2', '9', '5', '9', '0', '9', '2', '9', '5', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '6', '3', '0', '6', '7', '2', '8', '3', '4', '6', '2', '3', '3', '9', '5', '3', '1', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '1', '5', '1', '6', '8', '4', '5', '6', '2', '6', '8', '1', '1', '1', '8', '3', '3', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '2', '6', '5', '9', '0', '9', '8', '8', '7', '4', '0', '4', '5', '2', '8', '1', '8', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '2', '6', '4', '9', '4', '5', '1', '3', '5', '6', '6', '0', '1', '0', '6', '2', '4', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '7', '4', '9', '2', '1', '4', '6', '7', '5', '7', '7', '5', '7', '5', '2', '8', '7', '7', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '6', '1', '1', '9', '2', '7', '2', '9', '8', '0', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '6', '4', '8', '8', '1', '2', '2', '9', '5', '8', '3', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk058Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5', '8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '9', '3', '5', '0', '2', '9', '2', '8', '4', '2', '0', '2', '9', '1', '4', '1', '8', '6', '7', '0', '8']), .str (String.ofList ['1', '8', '9', '9', '9', '2', '1', '3', '1', '0', '0', '0', '4', '0', '4', '5', '0', '7', '0', '4', '5', '7']), .str (String.ofList ['1', '9', '1', '8', '4', '1', '2', '1', '9', '7', '3', '1', '5', '5', '4', '0', '3', '5', '5', '8', '4']), .str (String.ofList ['6', '4', '1', '5', '2', '4', '4', '2', '7', '8', '3', '4', '5', '2', '6', '9', '3', '0', '5', '8', '7']), .str (String.ofList ['1', '1', '4', '6', '5', '6', '9', '4', '1', '0', '8', '8', '2', '9', '5', '9', '0', '9', '2', '9', '5', '8']), .str (String.ofList ['1', '7', '2', '6', '3', '0', '6', '7', '2', '8', '3', '4', '6', '2', '3', '3', '9', '5', '3', '1', '4', '8']), .str (String.ofList ['1', '2', '4', '1', '5', '1', '6', '8', '4', '5', '6', '2', '6', '8', '1', '1', '1', '8', '3', '3', '1', '3']), .str (String.ofList ['9', '6', '2', '6', '5', '9', '0', '9', '8', '8', '7', '4', '0', '4', '5', '2', '8', '1', '8', '6', '7']), .str (String.ofList ['9', '6', '2', '6', '4', '9', '4', '5', '1', '3', '5', '6', '6', '0', '1', '0', '6', '2', '4', '5', '6']), .str (String.ofList ['1', '5', '7', '4', '9', '2', '1', '4', '6', '7', '5', '7', '7', '5', '7', '5', '2', '8', '7', '7', '0', '0'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '6', '1', '1', '9', '2', '7', '2', '9', '8', '0', '9', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '6', '4', '8', '8', '1', '2', '2', '9', '5', '8', '3', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_058_before_generic"
  err.flush

theorem array_moment_records_chunk_058 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 123)
      (SourceJson.white (momentRecordsChunk058Chars ++ tail)) acc =
      SourceJson.array (fuel + 122) (SourceJson.white tail) (momentRecordsChunk058Push acc) := by rfl

noncomputable def momentRecordsAcc059 : List SourceJson := momentRecordsChunk058Push momentRecordsAcc058

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_058_generic_complete"
  err.flush

noncomputable def momentRecordsChunk059Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '1', '9', '8', '1', '5', '9', '9', '8', '5', '5', '8', '8', '0', '3', '4', '3', '5', '1', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '4', '1', '7', '1', '4', '6', '4', '4', '6', '0', '9', '3', '8', '0', '6', '0', '5', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '9', '5', '0', '0', '1', '0', '3', '3', '4', '8', '5', '8', '7', '4', '2', '4', '6', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '5', '9', '6', '4', '8', '9', '3', '6', '0', '5', '0', '7', '5', '8', '7', '2', '8', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '0', '1', '1', '5', '6', '6', '2', '6', '6', '8', '8', '9', '8', '1', '9', '5', '2', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '4', '4', '3', '9', '7', '7', '1', '4', '8', '1', '9', '0', '1', '8', '9', '2', '7', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '4', '5', '4', '0', '6', '3', '0', '3', '8', '0', '4', '3', '5', '6', '1', '7', '0', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '4', '6', '1', '0', '0', '7', '9', '2', '9', '3', '1', '3', '0', '2', '8', '7', '6', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '4', '6', '0', '4', '6', '2', '1', '0', '9', '5', '9', '1', '3', '3', '8', '4', '7', '2', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '8', '3', '5', '9', '2', '2', '8', '5', '1', '4', '8', '0', '0', '6', '5', '7', '5', '4', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '5', '1', '9', '0', '9', '5', '2', '1', '3', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '5', '5', '3', '2', '3', '5', '5', '9', '1', '3', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk059Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5', '9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '0', '1', '1', '9', '8', '1', '5', '9', '9', '8', '5', '5', '8', '8', '0', '3', '4', '3', '5', '1', '1']), .str (String.ofList ['9', '9', '4', '1', '7', '1', '4', '6', '4', '4', '6', '0', '9', '3', '8', '0', '6', '0', '5', '8', '8']), .str (String.ofList ['1', '3', '9', '9', '5', '0', '0', '1', '0', '3', '3', '4', '8', '5', '8', '7', '4', '2', '4', '6', '6']), .str (String.ofList ['5', '9', '5', '9', '6', '4', '8', '9', '3', '6', '0', '5', '0', '7', '5', '8', '7', '2', '8', '7', '1']), .str (String.ofList ['1', '1', '1', '0', '1', '1', '5', '6', '6', '2', '6', '6', '8', '8', '9', '8', '1', '9', '5', '2', '6', '1']), .str (String.ofList ['1', '3', '1', '4', '4', '3', '9', '7', '7', '1', '4', '8', '1', '9', '0', '1', '8', '9', '2', '7', '3', '7']), .str (String.ofList ['9', '6', '4', '5', '4', '0', '6', '3', '0', '3', '8', '0', '4', '3', '5', '6', '1', '7', '0', '7', '0']), .str (String.ofList ['7', '5', '4', '6', '1', '0', '0', '7', '9', '2', '9', '3', '1', '3', '0', '2', '8', '7', '6', '2', '5']), .str (String.ofList ['7', '5', '4', '6', '0', '4', '6', '2', '1', '0', '9', '5', '9', '1', '3', '3', '8', '4', '7', '2', '3']), .str (String.ofList ['1', '4', '5', '8', '3', '5', '9', '2', '2', '8', '5', '1', '4', '8', '0', '0', '6', '5', '7', '5', '4', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '5', '1', '9', '0', '9', '5', '2', '1', '3', '0', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '5', '5', '3', '2', '3', '5', '5', '9', '1', '3', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_059_before_generic"
  err.flush

theorem array_moment_records_chunk_059 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 122)
      (SourceJson.white (momentRecordsChunk059Chars ++ tail)) acc =
      SourceJson.array (fuel + 121) (SourceJson.white tail) (momentRecordsChunk059Push acc) := by rfl

noncomputable def momentRecordsAcc060 : List SourceJson := momentRecordsChunk059Push momentRecordsAcc059

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_059_generic_complete"
  err.flush

noncomputable def momentRecordsBlock014Chars : List Char := momentRecordsChunk056Chars ++ momentRecordsChunk057Chars ++ momentRecordsChunk058Chars ++ momentRecordsChunk059Chars
noncomputable def momentRecordsBlock014Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk059Push (momentRecordsChunk058Push (momentRecordsChunk057Push (momentRecordsChunk056Push (acc))))

theorem array_moment_records_block_014 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 125)
      (SourceJson.white (momentRecordsBlock014Chars ++ tail)) acc =
      SourceJson.array (fuel + 121) (SourceJson.white tail) (momentRecordsBlock014Push acc) := by
  have hinput : momentRecordsBlock014Chars ++ tail = momentRecordsChunk056Chars ++ (momentRecordsChunk057Chars ++ (momentRecordsChunk058Chars ++ (momentRecordsChunk059Chars ++ (tail)))) := by
    simp only [momentRecordsBlock014Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 125) (SourceJson.white (momentRecordsBlock014Chars ++ tail)) acc =
        SourceJson.array (fuel + 125) (SourceJson.white (momentRecordsChunk056Chars ++ (momentRecordsChunk057Chars ++ (momentRecordsChunk058Chars ++ (momentRecordsChunk059Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 125) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 124) (SourceJson.white (momentRecordsChunk057Chars ++ (momentRecordsChunk058Chars ++ (momentRecordsChunk059Chars ++ (tail))))) (momentRecordsChunk056Push (acc)) := array_moment_records_chunk_056 fuel (momentRecordsChunk057Chars ++ (momentRecordsChunk058Chars ++ (momentRecordsChunk059Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 123) (SourceJson.white (momentRecordsChunk058Chars ++ (momentRecordsChunk059Chars ++ (tail)))) (momentRecordsChunk057Push (momentRecordsChunk056Push (acc))) := array_moment_records_chunk_057 fuel (momentRecordsChunk058Chars ++ (momentRecordsChunk059Chars ++ (tail))) (momentRecordsChunk056Push (acc))
    _ = SourceJson.array (fuel + 122) (SourceJson.white (momentRecordsChunk059Chars ++ (tail))) (momentRecordsChunk058Push (momentRecordsChunk057Push (momentRecordsChunk056Push (acc)))) := array_moment_records_chunk_058 fuel (momentRecordsChunk059Chars ++ (tail)) (momentRecordsChunk057Push (momentRecordsChunk056Push (acc)))
    _ = SourceJson.array (fuel + 121) (SourceJson.white tail) (momentRecordsBlock014Push acc) := array_moment_records_chunk_059 fuel (tail) (momentRecordsChunk058Push (momentRecordsChunk057Push (momentRecordsChunk056Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_014_before_raw_binding"
  err.flush

theorem moment_records_block_014_prefix :
    (momentRest01 29570).take 2058 = momentRecordsBlock014Chars := by rfl

theorem moment_records_block_014_split :
    momentRest01 29570 = momentRecordsBlock014Chars ++ momentRest01 31628 := by
  calc
    momentRest01 29570 =
        (momentRest01 29570).take 2058 ++ (momentRest01 29570).drop 2058 :=
      (List.take_append_drop 2058 (momentRest01 29570)).symm
    _ = momentRecordsBlock014Chars ++ (momentRest01 29570).drop 2058 :=
      congrArg (fun p => p ++ (momentRest01 29570).drop 2058) moment_records_block_014_prefix
    _ = momentRecordsBlock014Chars ++ momentRest01 31628 :=
      congrArg (fun rest => momentRecordsBlock014Chars ++ rest) (momentRest01_drop 29570 2058)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_014_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_014 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 125)
      (SourceJson.white (momentRest01 29570)) acc =
      SourceJson.array (fuel + 121) (SourceJson.white (momentRest01 31628)) (momentRecordsBlock014Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 125) (SourceJson.white s) acc)
      moment_records_block_014_split).trans (array_moment_records_block_014 fuel (momentRest01 31628) acc)

theorem moment_records_through_block_014 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 121) (SourceJson.white (momentRest01 31628)) momentRecordsAcc060 := by
  exact (moment_records_through_block_013 fuel).trans (array_moment_records_original_block_014 fuel momentRecordsAcc056)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_014_complete"
  err.flush

#print axioms array_moment_records_chunk_056
#print axioms array_moment_records_chunk_057
#print axioms array_moment_records_chunk_058
#print axioms array_moment_records_chunk_059
#print axioms array_moment_records_block_014
#print axioms moment_records_block_014_prefix
#print axioms moment_records_block_014_split
#print axioms array_moment_records_original_block_014
#print axioms moment_records_through_block_014

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
