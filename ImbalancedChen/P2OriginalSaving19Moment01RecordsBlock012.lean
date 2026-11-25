import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock011

/-! Original moment records block 12. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk048Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '0', '7', '3', '7', '8', '1', '5', '1', '5', '4', '3', '8', '4', '6', '2', '0', '1', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '4', '6', '4', '7', '2', '7', '1', '1', '9', '0', '1', '2', '7', '1', '5', '8', '8', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '4', '3', '3', '6', '1', '6', '6', '7', '4', '8', '5', '1', '3', '5', '8', '0', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '9', '6', '5', '1', '1', '5', '9', '2', '9', '7', '6', '7', '1', '2', '1', '5', '6', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '9', '1', '5', '2', '1', '8', '0', '9', '3', '8', '8', '6', '2', '1', '3', '0', '5', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '7', '5', '9', '4', '8', '0', '2', '5', '1', '9', '4', '7', '4', '2', '3', '7', '0', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '3', '3', '8', '3', '9', '6', '0', '4', '6', '1', '0', '6', '7', '8', '5', '3', '2', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '7', '0', '1', '6', '0', '1', '3', '7', '3', '1', '8', '3', '6', '4', '1', '5', '4', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '0', '6', '3', '6', '7', '3', '7', '1', '0', '5', '2', '9', '4', '7', '0', '6', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '1', '9', '5', '8', '5', '0', '6', '4', '4', '1', '5', '0', '9', '0', '6', '1', '8', '7', '4', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '5', '9', '4', '2', '8', '7', '1', '5', '1', '1', '5', '8', '2', '6', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '7', '8', '6', '2', '3', '1', '5', '4', '6', '8', '0', '0', '5', '4', '7', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk048Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['4', '8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '2', '9', '0', '7', '3', '7', '8', '1', '5', '1', '5', '4', '3', '8', '4', '6', '2', '0', '1', '0', '8']), .str (String.ofList ['2', '4', '9', '4', '6', '4', '7', '2', '7', '1', '1', '9', '0', '1', '2', '7', '1', '5', '8', '8', '3', '4']), .str (String.ofList ['2', '4', '9', '4', '3', '3', '6', '1', '6', '6', '7', '4', '8', '5', '1', '3', '5', '8', '0', '0', '6']), .str (String.ofList ['5', '9', '9', '6', '5', '1', '1', '5', '9', '2', '9', '7', '6', '7', '1', '2', '1', '5', '6', '7', '6']), .str (String.ofList ['1', '1', '3', '9', '1', '5', '2', '1', '8', '0', '9', '3', '8', '8', '6', '2', '1', '3', '0', '5', '6', '4']), .str (String.ofList ['1', '6', '1', '7', '5', '9', '4', '8', '0', '2', '5', '1', '9', '4', '7', '4', '2', '3', '7', '0', '7', '6']), .str (String.ofList ['1', '4', '6', '3', '3', '8', '3', '9', '6', '0', '4', '6', '1', '0', '6', '7', '8', '5', '3', '2', '2', '5']), .str (String.ofList ['1', '2', '4', '7', '0', '1', '6', '0', '1', '3', '7', '3', '1', '8', '3', '6', '4', '1', '5', '4', '8', '6']), .str (String.ofList ['1', '0', '8', '2', '0', '6', '3', '6', '7', '3', '7', '1', '0', '5', '2', '9', '4', '7', '0', '6', '1', '2']), .str (String.ofList ['1', '7', '1', '9', '5', '8', '5', '0', '6', '4', '4', '1', '5', '0', '9', '0', '6', '1', '8', '7', '4', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '6', '5', '9', '4', '2', '8', '7', '1', '5', '1', '1', '5', '8', '2', '6', '4', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '6', '7', '8', '6', '2', '3', '1', '5', '4', '6', '8', '0', '0', '5', '4', '7', '8']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_048_before_generic"
  err.flush

theorem array_moment_records_chunk_048 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 133)
      (SourceJson.white (momentRecordsChunk048Chars ++ tail)) acc =
      SourceJson.array (fuel + 132) (SourceJson.white tail) (momentRecordsChunk048Push acc) := by rfl

noncomputable def momentRecordsAcc049 : List SourceJson := momentRecordsChunk048Push momentRecordsAcc048

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_048_generic_complete"
  err.flush

noncomputable def momentRecordsChunk049Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '0', '6', '8', '8', '7', '0', '1', '9', '0', '8', '6', '8', '1', '0', '9', '5', '8', '0', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '8', '8', '0', '7', '9', '2', '4', '3', '3', '6', '9', '3', '6', '8', '3', '1', '2', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '3', '5', '3', '3', '2', '5', '0', '6', '7', '8', '3', '4', '7', '0', '7', '8', '1', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '5', '4', '4', '6', '0', '4', '2', '0', '8', '6', '3', '9', '6', '7', '3', '7', '4', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '9', '7', '3', '5', '2', '2', '9', '8', '8', '4', '6', '0', '1', '5', '2', '0', '9', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '5', '0', '2', '7', '0', '9', '9', '7', '2', '3', '6', '5', '5', '4', '4', '0', '1', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '6', '8', '2', '0', '7', '1', '2', '5', '1', '3', '5', '9', '2', '9', '1', '8', '5', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '5', '3', '0', '2', '4', '9', '5', '0', '6', '6', '0', '7', '1', '0', '2', '3', '2', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '3', '8', '4', '1', '9', '1', '5', '8', '0', '7', '5', '2', '3', '9', '6', '1', '4', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '9', '0', '4', '7', '9', '4', '0', '3', '0', '4', '5', '2', '0', '1', '8', '2', '5', '0', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '1', '6', '2', '1', '8', '2', '9', '1', '5', '1', '3', '6', '4', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '2', '1', '5', '2', '9', '3', '8', '8', '1', '4', '6', '8', '0', '9', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk049Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['4', '9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '1', '0', '6', '8', '8', '7', '0', '1', '9', '0', '8', '6', '8', '1', '0', '9', '5', '8', '0', '5', '1']), .str (String.ofList ['2', '0', '6', '8', '8', '0', '7', '9', '2', '4', '3', '3', '6', '9', '3', '6', '8', '3', '1', '2', '0', '8']), .str (String.ofList ['1', '9', '3', '5', '3', '3', '2', '5', '0', '6', '7', '8', '3', '4', '7', '0', '7', '8', '1', '3', '0']), .str (String.ofList ['6', '1', '5', '4', '4', '6', '0', '4', '2', '0', '8', '6', '3', '9', '6', '7', '3', '7', '4', '0', '5']), .str (String.ofList ['1', '1', '6', '9', '7', '3', '5', '2', '2', '9', '8', '8', '4', '6', '0', '1', '5', '2', '0', '9', '1', '2']), .str (String.ofList ['1', '6', '1', '5', '0', '2', '7', '0', '9', '9', '7', '2', '3', '6', '5', '5', '4', '4', '0', '1', '0', '2']), .str (String.ofList ['1', '2', '1', '6', '8', '2', '0', '7', '1', '2', '5', '1', '3', '5', '9', '2', '9', '1', '8', '5', '6', '7']), .str (String.ofList ['1', '0', '7', '5', '3', '0', '2', '4', '9', '5', '0', '6', '6', '0', '7', '1', '0', '2', '3', '2', '2', '9']), .str (String.ofList ['9', '7', '3', '8', '4', '1', '9', '1', '5', '8', '0', '7', '5', '2', '3', '9', '6', '1', '4', '2', '8']), .str (String.ofList ['1', '3', '3', '9', '0', '4', '7', '9', '4', '0', '3', '0', '4', '5', '2', '0', '1', '8', '2', '5', '0', '7'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '1', '6', '2', '1', '8', '2', '9', '1', '5', '1', '3', '6', '4', '0', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '2', '1', '5', '2', '9', '3', '8', '8', '1', '4', '6', '8', '0', '9', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_049_before_generic"
  err.flush

theorem array_moment_records_chunk_049 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 132)
      (SourceJson.white (momentRecordsChunk049Chars ++ tail)) acc =
      SourceJson.array (fuel + 131) (SourceJson.white tail) (momentRecordsChunk049Push acc) := by rfl

noncomputable def momentRecordsAcc050 : List SourceJson := momentRecordsChunk049Push momentRecordsAcc049

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_049_generic_complete"
  err.flush

noncomputable def momentRecordsChunk050Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '8', '1', '3', '7', '3', '9', '3', '7', '0', '8', '2', '4', '1', '6', '3', '7', '0', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '8', '9', '0', '7', '3', '9', '9', '9', '9', '1', '9', '8', '8', '2', '7', '6', '6', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '5', '4', '5', '3', '4', '7', '5', '3', '4', '1', '4', '6', '1', '4', '9', '9', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '4', '0', '9', '1', '2', '9', '4', '0', '1', '5', '8', '8', '9', '4', '7', '3', '7', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '6', '9', '7', '8', '2', '0', '0', '2', '4', '5', '1', '3', '6', '2', '7', '6', '8', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '1', '0', '1', '4', '3', '4', '2', '7', '9', '3', '0', '4', '3', '6', '3', '6', '9', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '2', '8', '8', '7', '6', '9', '9', '7', '2', '6', '9', '4', '9', '4', '4', '3', '1', '4', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '4', '9', '5', '8', '2', '3', '7', '3', '5', '2', '3', '4', '4', '3', '3', '7', '9', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '3', '3', '9', '4', '7', '6', '9', '8', '1', '1', '4', '1', '1', '9', '9', '7', '6', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '0', '2', '5', '6', '5', '4', '1', '1', '5', '3', '7', '9', '3', '3', '2', '9', '7', '8', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '3', '2', '2', '4', '2', '1', '7', '5', '8', '7', '6', '4', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '4', '9', '0', '2', '9', '1', '5', '3', '9', '3', '4', '7', '8', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk050Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '9', '2', '8', '1', '3', '7', '3', '9', '3', '7', '0', '8', '2', '4', '1', '6', '3', '7', '0', '4', '6']), .str (String.ofList ['1', '8', '9', '8', '9', '0', '7', '3', '9', '9', '9', '9', '1', '9', '8', '8', '2', '7', '6', '6', '9', '1']), .str (String.ofList ['1', '7', '8', '5', '4', '5', '3', '4', '7', '5', '3', '4', '1', '4', '6', '1', '4', '9', '9', '7', '4']), .str (String.ofList ['6', '5', '4', '0', '9', '1', '2', '9', '4', '0', '1', '5', '8', '8', '9', '4', '7', '3', '7', '1', '5']), .str (String.ofList ['1', '2', '1', '6', '9', '7', '8', '2', '0', '0', '2', '4', '5', '1', '3', '6', '2', '7', '6', '8', '6', '9']), .str (String.ofList ['1', '6', '3', '1', '0', '1', '4', '3', '4', '2', '7', '9', '3', '0', '4', '3', '6', '3', '6', '9', '9', '8']), .str (String.ofList ['1', '1', '8', '2', '8', '8', '7', '6', '9', '9', '7', '2', '6', '9', '4', '9', '4', '4', '3', '1', '4', '4']), .str (String.ofList ['1', '0', '6', '4', '9', '5', '8', '2', '3', '7', '3', '5', '2', '3', '4', '4', '3', '3', '7', '9', '7', '8']), .str (String.ofList ['9', '8', '3', '3', '9', '4', '7', '6', '9', '8', '1', '1', '4', '1', '1', '9', '9', '7', '6', '3', '1']), .str (String.ofList ['9', '2', '0', '2', '5', '6', '5', '4', '1', '1', '5', '3', '7', '9', '3', '3', '2', '9', '7', '8', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '7', '3', '2', '2', '4', '2', '1', '7', '5', '8', '7', '6', '4', '7', '6'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '7', '4', '9', '0', '2', '9', '1', '5', '3', '9', '3', '4', '7', '8', '0']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_050_before_generic"
  err.flush

theorem array_moment_records_chunk_050 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 131)
      (SourceJson.white (momentRecordsChunk050Chars ++ tail)) acc =
      SourceJson.array (fuel + 130) (SourceJson.white tail) (momentRecordsChunk050Push acc) := by rfl

noncomputable def momentRecordsAcc051 : List SourceJson := momentRecordsChunk050Push momentRecordsAcc050

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_050_generic_complete"
  err.flush

noncomputable def momentRecordsChunk051Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '1', '8', '0', '0', '3', '9', '0', '8', '7', '4', '5', '4', '4', '2', '5', '0', '5', '1', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '1', '3', '5', '1', '6', '9', '6', '1', '1', '0', '7', '4', '4', '1', '7', '1', '9', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '9', '1', '5', '8', '0', '2', '0', '2', '1', '7', '7', '3', '5', '2', '1', '7', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '9', '8', '4', '7', '0', '2', '7', '6', '3', '8', '3', '7', '3', '8', '3', '2', '0', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '5', '5', '2', '4', '5', '3', '0', '4', '4', '2', '7', '8', '5', '1', '1', '9', '3', '5', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '1', '6', '6', '5', '2', '0', '3', '4', '0', '3', '3', '5', '6', '2', '8', '4', '7', '0', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '7', '1', '7', '2', '7', '0', '0', '4', '4', '3', '9', '2', '6', '7', '6', '9', '6', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '2', '3', '8', '4', '6', '1', '5', '5', '6', '1', '8', '0', '8', '2', '7', '7', '4', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '1', '5', '7', '2', '9', '3', '4', '9', '5', '7', '7', '1', '8', '5', '2', '7', '1', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '8', '6', '5', '0', '5', '0', '7', '9', '7', '6', '2', '9', '3', '4', '3', '4', '6', '6', '5', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '0', '1', '0', '7', '2', '3', '3', '0', '8', '4', '8', '7', '5', '2', '0', '4', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '1', '6', '6', '7', '2', '0', '2', '3', '3', '7', '3', '5', '8', '5', '3', '5', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk051Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '1', '1', '8', '0', '0', '3', '9', '0', '8', '7', '4', '5', '4', '4', '2', '5', '0', '5', '1', '5', '5']), .str (String.ofList ['2', '2', '9', '1', '3', '5', '1', '6', '9', '6', '1', '1', '0', '7', '4', '4', '1', '7', '1', '9', '8', '8']), .str (String.ofList ['2', '5', '6', '9', '1', '5', '8', '0', '2', '0', '2', '1', '7', '7', '3', '5', '2', '1', '7', '6', '1']), .str (String.ofList ['5', '4', '9', '8', '4', '7', '0', '2', '7', '6', '3', '8', '3', '7', '3', '8', '3', '2', '0', '5', '6']), .str (String.ofList ['1', '0', '2', '5', '5', '2', '4', '5', '3', '0', '4', '4', '2', '7', '8', '5', '1', '1', '9', '3', '5', '8']), .str (String.ofList ['1', '7', '1', '6', '6', '5', '2', '0', '3', '4', '0', '3', '3', '5', '6', '2', '8', '4', '7', '0', '3', '7']), .str (String.ofList ['1', '3', '4', '7', '1', '7', '2', '7', '0', '0', '4', '4', '3', '9', '2', '6', '7', '6', '9', '6', '5', '0']), .str (String.ofList ['1', '1', '0', '2', '3', '8', '4', '6', '1', '5', '5', '6', '1', '8', '0', '8', '2', '7', '7', '4', '1', '8']), .str (String.ofList ['9', '9', '1', '5', '7', '2', '9', '3', '4', '9', '5', '7', '7', '1', '8', '5', '2', '7', '1', '2', '0']), .str (String.ofList ['1', '9', '8', '6', '5', '0', '5', '0', '7', '9', '7', '6', '2', '9', '3', '4', '3', '4', '6', '6', '5', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '4', '0', '1', '0', '7', '2', '3', '3', '0', '8', '4', '8', '7', '5', '2', '0', '4', '7'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '4', '1', '6', '6', '7', '2', '0', '2', '3', '3', '7', '3', '5', '8', '5', '3', '5', '6']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_051_before_generic"
  err.flush

theorem array_moment_records_chunk_051 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 130)
      (SourceJson.white (momentRecordsChunk051Chars ++ tail)) acc =
      SourceJson.array (fuel + 129) (SourceJson.white tail) (momentRecordsChunk051Push acc) := by rfl

noncomputable def momentRecordsAcc052 : List SourceJson := momentRecordsChunk051Push momentRecordsAcc051

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_051_generic_complete"
  err.flush

noncomputable def momentRecordsBlock012Chars : List Char := momentRecordsChunk048Chars ++ momentRecordsChunk049Chars ++ momentRecordsChunk050Chars ++ momentRecordsChunk051Chars
noncomputable def momentRecordsBlock012Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk051Push (momentRecordsChunk050Push (momentRecordsChunk049Push (momentRecordsChunk048Push (acc))))

theorem array_moment_records_block_012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 133)
      (SourceJson.white (momentRecordsBlock012Chars ++ tail)) acc =
      SourceJson.array (fuel + 129) (SourceJson.white tail) (momentRecordsBlock012Push acc) := by
  have hinput : momentRecordsBlock012Chars ++ tail = momentRecordsChunk048Chars ++ (momentRecordsChunk049Chars ++ (momentRecordsChunk050Chars ++ (momentRecordsChunk051Chars ++ (tail)))) := by
    simp only [momentRecordsBlock012Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 133) (SourceJson.white (momentRecordsBlock012Chars ++ tail)) acc =
        SourceJson.array (fuel + 133) (SourceJson.white (momentRecordsChunk048Chars ++ (momentRecordsChunk049Chars ++ (momentRecordsChunk050Chars ++ (momentRecordsChunk051Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 133) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 132) (SourceJson.white (momentRecordsChunk049Chars ++ (momentRecordsChunk050Chars ++ (momentRecordsChunk051Chars ++ (tail))))) (momentRecordsChunk048Push (acc)) := array_moment_records_chunk_048 fuel (momentRecordsChunk049Chars ++ (momentRecordsChunk050Chars ++ (momentRecordsChunk051Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 131) (SourceJson.white (momentRecordsChunk050Chars ++ (momentRecordsChunk051Chars ++ (tail)))) (momentRecordsChunk049Push (momentRecordsChunk048Push (acc))) := array_moment_records_chunk_049 fuel (momentRecordsChunk050Chars ++ (momentRecordsChunk051Chars ++ (tail))) (momentRecordsChunk048Push (acc))
    _ = SourceJson.array (fuel + 130) (SourceJson.white (momentRecordsChunk051Chars ++ (tail))) (momentRecordsChunk050Push (momentRecordsChunk049Push (momentRecordsChunk048Push (acc)))) := array_moment_records_chunk_050 fuel (momentRecordsChunk051Chars ++ (tail)) (momentRecordsChunk049Push (momentRecordsChunk048Push (acc)))
    _ = SourceJson.array (fuel + 129) (SourceJson.white tail) (momentRecordsBlock012Push acc) := array_moment_records_chunk_051 fuel (tail) (momentRecordsChunk050Push (momentRecordsChunk049Push (momentRecordsChunk048Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_012_before_raw_binding"
  err.flush

theorem moment_records_block_012_prefix :
    (momentRest01 25391).take 2094 = momentRecordsBlock012Chars := by rfl

theorem moment_records_block_012_split :
    momentRest01 25391 = momentRecordsBlock012Chars ++ momentRest01 27485 := by
  calc
    momentRest01 25391 =
        (momentRest01 25391).take 2094 ++ (momentRest01 25391).drop 2094 :=
      (List.take_append_drop 2094 (momentRest01 25391)).symm
    _ = momentRecordsBlock012Chars ++ (momentRest01 25391).drop 2094 :=
      congrArg (fun p => p ++ (momentRest01 25391).drop 2094) moment_records_block_012_prefix
    _ = momentRecordsBlock012Chars ++ momentRest01 27485 :=
      congrArg (fun rest => momentRecordsBlock012Chars ++ rest) (momentRest01_drop 25391 2094)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_012_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_012 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 133)
      (SourceJson.white (momentRest01 25391)) acc =
      SourceJson.array (fuel + 129) (SourceJson.white (momentRest01 27485)) (momentRecordsBlock012Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 133) (SourceJson.white s) acc)
      moment_records_block_012_split).trans (array_moment_records_block_012 fuel (momentRest01 27485) acc)

theorem moment_records_through_block_012 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 129) (SourceJson.white (momentRest01 27485)) momentRecordsAcc052 := by
  exact (moment_records_through_block_011 fuel).trans (array_moment_records_original_block_012 fuel momentRecordsAcc048)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_012_complete"
  err.flush

#print axioms array_moment_records_chunk_048
#print axioms array_moment_records_chunk_049
#print axioms array_moment_records_chunk_050
#print axioms array_moment_records_chunk_051
#print axioms array_moment_records_block_012
#print axioms moment_records_block_012_prefix
#print axioms moment_records_block_012_split
#print axioms array_moment_records_original_block_012
#print axioms moment_records_through_block_012

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
