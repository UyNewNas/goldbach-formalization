import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock011

/-! Original moment records block 12. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk048Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '4', '9', '9', '0', '0', '4', '4', '8', '5', '7', '3', '8', '6', '2', '6', '5', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '9', '4', '0', '0', '6', '6', '9', '4', '8', '5', '4', '2', '9', '7', '2', '0', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '2', '4', '0', '1', '8', '6', '6', '2', '5', '7', '3', '8', '5', '2', '6', '3', '5', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '3', '1', '0', '1', '8', '6', '5', '3', '2', '2', '5', '7', '9', '2', '8', '3', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '5', '5', '2', '8', '9', '9', '4', '9', '6', '6', '6', '5', '4', '7', '7', '4', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '5', '1', '0', '7', '8', '9', '6', '7', '3', '8', '2', '6', '2', '4', '9', '7', '9', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '2', '6', '6', '0', '5', '8', '7', '9', '4', '1', '1', '2', '2', '8', '5', '1', '6', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '1', '1', '2', '0', '2', '4', '2', '9', '6', '9', '6', '2', '9', '6', '2', '8', '5', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '7', '6', '1', '7', '7', '8', '0', '9', '8', '9', '1', '4', '5', '6', '5', '3', '1', '5', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '7', '6', '4', '1', '2', '5', '6', '1', '9', '2', '5', '1', '7', '8', '5', '4', '2', '0', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '4', '4', '7', '9', '5', '3', '0', '8', '3', '3', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '4', '6', '2', '9', '5', '1', '8', '5', '3', '9', '7', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk048Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['4', '8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '4', '5', '4', '9', '9', '0', '0', '4', '4', '8', '5', '7', '3', '8', '6', '2', '6', '5', '7', '5']), .str (String.ofList ['1', '4', '4', '9', '4', '0', '0', '6', '6', '9', '4', '8', '5', '4', '2', '9', '7', '2', '0', '2', '0']), .str (String.ofList ['1', '5', '2', '4', '0', '1', '8', '6', '6', '2', '5', '7', '3', '8', '5', '2', '6', '3', '5', '6', '3']), .str (String.ofList ['3', '9', '5', '3', '1', '0', '1', '8', '6', '5', '3', '2', '2', '5', '7', '9', '2', '8', '3', '5', '3']), .str (String.ofList ['2', '7', '6', '5', '5', '2', '8', '9', '9', '4', '9', '6', '6', '6', '5', '4', '7', '7', '4', '6', '9']), .str (String.ofList ['3', '6', '5', '1', '0', '7', '8', '9', '6', '7', '3', '8', '2', '6', '2', '4', '9', '7', '9', '9', '6']), .str (String.ofList ['5', '0', '2', '6', '6', '0', '5', '8', '7', '9', '4', '1', '1', '2', '2', '8', '5', '1', '6', '8', '1']), .str (String.ofList ['3', '3', '1', '1', '2', '0', '2', '4', '2', '9', '6', '9', '6', '2', '9', '6', '2', '8', '5', '8', '2']), .str (String.ofList ['2', '4', '7', '6', '1', '7', '7', '8', '0', '9', '8', '9', '1', '4', '5', '6', '5', '3', '1', '5', '4']), .str (String.ofList ['2', '4', '7', '6', '4', '1', '2', '5', '6', '1', '9', '2', '5', '1', '7', '8', '5', '4', '2', '0', '7'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '4', '4', '7', '9', '5', '3', '0', '8', '3', '3', '7', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '4', '6', '2', '9', '5', '1', '8', '5', '3', '9', '7', '8']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_048_before_generic"
  err.flush

theorem array_moment_records_chunk_048 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 45)
      (SourceJson.white (momentRecordsChunk048Chars ++ tail)) acc =
      SourceJson.array (fuel + 44) (SourceJson.white tail) (momentRecordsChunk048Push acc) := by rfl

noncomputable def momentRecordsAcc049 : List SourceJson := momentRecordsChunk048Push momentRecordsAcc048

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_048_generic_complete"
  err.flush

noncomputable def momentRecordsChunk049Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '2', '4', '9', '7', '5', '3', '5', '0', '9', '6', '9', '5', '9', '7', '4', '9', '8', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '0', '6', '5', '1', '9', '2', '7', '2', '1', '8', '3', '3', '7', '3', '8', '6', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '0', '7', '1', '1', '2', '4', '4', '6', '6', '4', '1', '8', '8', '0', '3', '7', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '2', '8', '0', '4', '7', '2', '2', '8', '5', '5', '9', '3', '0', '3', '3', '6', '9', '9', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '8', '2', '1', '9', '6', '6', '8', '6', '5', '2', '7', '6', '8', '1', '6', '4', '5', '5', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '3', '1', '2', '7', '7', '5', '5', '7', '5', '2', '0', '9', '1', '7', '6', '7', '5', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '4', '9', '6', '9', '1', '1', '0', '6', '4', '8', '2', '0', '4', '7', '1', '8', '6', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '8', '4', '0', '7', '7', '1', '8', '2', '7', '9', '2', '3', '8', '0', '8', '5', '0', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '4', '1', '1', '5', '6', '6', '1', '2', '3', '6', '1', '4', '4', '5', '4', '8', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '4', '3', '4', '0', '9', '3', '5', '1', '1', '6', '7', '3', '4', '1', '2', '5', '2', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '3', '5', '9', '1', '0', '9', '6', '7', '1', '1', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '3', '7', '8', '3', '1', '9', '9', '0', '7', '4', '1', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk049Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['4', '9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '8', '9', '2', '4', '9', '7', '5', '3', '5', '0', '9', '6', '9', '5', '9', '7', '4', '9', '8', '5']), .str (String.ofList ['2', '1', '7', '0', '6', '5', '1', '9', '2', '7', '2', '1', '8', '3', '3', '7', '3', '8', '6', '0', '2']), .str (String.ofList ['2', '3', '9', '0', '7', '1', '1', '2', '4', '4', '6', '6', '4', '1', '8', '8', '0', '3', '7', '4', '1']), .str (String.ofList ['6', '5', '2', '8', '0', '4', '7', '2', '2', '8', '5', '5', '9', '3', '0', '3', '3', '6', '9', '9', '9']), .str (String.ofList ['2', '3', '8', '2', '1', '9', '6', '6', '8', '6', '5', '2', '7', '6', '8', '1', '6', '4', '5', '5', '4']), .str (String.ofList ['5', '9', '3', '1', '2', '7', '7', '5', '5', '7', '5', '2', '0', '9', '1', '7', '6', '7', '5', '2', '1']), .str (String.ofList ['6', '7', '4', '9', '6', '9', '1', '1', '0', '6', '4', '8', '2', '0', '4', '7', '1', '8', '6', '6', '4']), .str (String.ofList ['6', '6', '8', '4', '0', '7', '7', '1', '8', '2', '7', '9', '2', '3', '8', '0', '8', '5', '0', '5', '9']), .str (String.ofList ['4', '2', '6', '4', '1', '1', '5', '6', '6', '1', '2', '3', '6', '1', '4', '4', '5', '4', '8', '2', '4']), .str (String.ofList ['4', '2', '6', '4', '3', '4', '0', '9', '3', '5', '1', '1', '6', '7', '3', '4', '1', '2', '5', '2', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '3', '5', '9', '1', '0', '9', '6', '7', '1', '1', '2', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '3', '7', '8', '3', '1', '9', '9', '0', '7', '4', '1', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_049_before_generic"
  err.flush

theorem array_moment_records_chunk_049 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 44)
      (SourceJson.white (momentRecordsChunk049Chars ++ tail)) acc =
      SourceJson.array (fuel + 43) (SourceJson.white tail) (momentRecordsChunk049Push acc) := by rfl

noncomputable def momentRecordsAcc050 : List SourceJson := momentRecordsChunk049Push momentRecordsAcc049

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_049_generic_complete"
  err.flush

noncomputable def momentRecordsChunk050Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '7', '3', '2', '3', '0', '8', '1', '6', '6', '8', '0', '7', '5', '3', '4', '4', '7', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '3', '7', '1', '8', '5', '9', '5', '3', '7', '0', '8', '9', '2', '4', '6', '9', '5', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '1', '6', '7', '8', '9', '8', '5', '4', '6', '5', '8', '1', '4', '5', '6', '5', '0', '5', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '7', '2', '7', '5', '0', '6', '5', '7', '2', '4', '1', '5', '6', '4', '5', '5', '2', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '3', '2', '7', '5', '3', '1', '6', '0', '0', '8', '9', '2', '1', '2', '8', '2', '5', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '6', '0', '7', '1', '8', '3', '8', '2', '1', '4', '4', '9', '5', '6', '3', '2', '9', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '9', '2', '3', '2', '7', '2', '0', '6', '6', '3', '9', '3', '6', '0', '3', '0', '4', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '1', '9', '6', '8', '3', '3', '3', '6', '9', '7', '4', '9', '5', '2', '5', '0', '0', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '6', '8', '0', '7', '6', '7', '7', '1', '2', '1', '3', '4', '1', '8', '1', '4', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '7', '0', '3', '1', '7', '9', '4', '4', '3', '0', '3', '9', '7', '0', '5', '2', '8', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '1', '0', '0', '1', '9', '5', '1', '9', '4', '0', '3', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '1', '1', '9', '7', '3', '9', '8', '9', '4', '1', '0', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk050Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '5', '7', '3', '2', '3', '0', '8', '1', '6', '6', '8', '0', '7', '5', '3', '4', '4', '7', '1', '0']), .str (String.ofList ['4', '0', '3', '7', '1', '8', '5', '9', '5', '3', '7', '0', '8', '9', '2', '4', '6', '9', '5', '9', '6']), .str (String.ofList ['2', '5', '1', '6', '7', '8', '9', '8', '5', '4', '6', '5', '8', '1', '4', '5', '6', '5', '0', '5', '4']), .str (String.ofList ['6', '4', '7', '2', '7', '5', '0', '6', '5', '7', '2', '4', '1', '5', '6', '4', '5', '5', '2', '0', '7']), .str (String.ofList ['3', '3', '3', '2', '7', '5', '3', '1', '6', '0', '0', '8', '9', '2', '1', '2', '8', '2', '5', '7', '1']), .str (String.ofList ['6', '1', '6', '0', '7', '1', '8', '3', '8', '2', '1', '4', '4', '9', '5', '6', '3', '2', '9', '5', '0']), .str (String.ofList ['4', '8', '9', '2', '3', '2', '7', '2', '0', '6', '6', '3', '9', '3', '6', '0', '3', '0', '4', '8', '3']), .str (String.ofList ['6', '7', '1', '9', '6', '8', '3', '3', '3', '6', '9', '7', '4', '9', '5', '2', '5', '0', '0', '8', '2']), .str (String.ofList ['4', '2', '6', '6', '8', '0', '7', '6', '7', '7', '1', '2', '1', '3', '4', '1', '8', '1', '4', '1', '4']), .str (String.ofList ['4', '2', '6', '7', '0', '3', '1', '7', '9', '4', '4', '3', '0', '3', '9', '7', '0', '5', '2', '8', '6'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '1', '0', '0', '1', '9', '5', '1', '9', '4', '0', '3', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '1', '1', '9', '7', '3', '9', '8', '9', '4', '1', '0', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_050_before_generic"
  err.flush

theorem array_moment_records_chunk_050 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 43)
      (SourceJson.white (momentRecordsChunk050Chars ++ tail)) acc =
      SourceJson.array (fuel + 42) (SourceJson.white tail) (momentRecordsChunk050Push acc) := by rfl

noncomputable def momentRecordsAcc051 : List SourceJson := momentRecordsChunk050Push momentRecordsAcc050

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_050_generic_complete"
  err.flush

noncomputable def momentRecordsChunk051Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '8', '5', '8', '0', '9', '3', '3', '9', '6', '3', '4', '5', '1', '4', '3', '7', '8', '9', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '0', '3', '2', '2', '8', '0', '4', '4', '4', '9', '4', '7', '7', '1', '2', '3', '2', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '7', '4', '1', '7', '1', '2', '2', '0', '0', '3', '8', '4', '5', '9', '4', '1', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '9', '3', '1', '1', '8', '0', '5', '7', '1', '7', '1', '5', '4', '3', '1', '2', '2', '2', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '6', '8', '0', '3', '7', '0', '6', '7', '7', '1', '0', '4', '3', '3', '2', '6', '5', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '2', '4', '4', '7', '6', '8', '5', '8', '1', '0', '4', '1', '3', '4', '7', '8', '5', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '3', '8', '4', '4', '6', '1', '7', '2', '9', '0', '5', '0', '2', '5', '8', '8', '4', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '3', '4', '7', '7', '3', '6', '9', '1', '1', '2', '4', '4', '2', '1', '9', '6', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '0', '0', '2', '3', '5', '1', '1', '3', '2', '7', '0', '6', '5', '8', '5', '3', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '0', '1', '7', '4', '0', '6', '6', '6', '8', '1', '4', '7', '1', '5', '5', '3', '3', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '6', '1', '5', '3', '4', '6', '7', '4', '0', '0', '8', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '6', '2', '7', '4', '5', '0', '4', '0', '2', '3', '1', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk051Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '9', '8', '5', '8', '0', '9', '3', '3', '9', '6', '3', '4', '5', '1', '4', '3', '7', '8', '9', '7']), .str (String.ofList ['4', '5', '0', '3', '2', '2', '8', '0', '4', '4', '4', '9', '4', '7', '7', '1', '2', '3', '2', '5', '3']), .str (String.ofList ['2', '3', '9', '7', '4', '1', '7', '1', '2', '2', '0', '0', '3', '8', '4', '5', '9', '4', '1', '5', '5']), .str (String.ofList ['5', '0', '9', '3', '1', '1', '8', '0', '5', '7', '1', '7', '1', '5', '4', '3', '1', '2', '2', '2', '3']), .str (String.ofList ['3', '4', '6', '8', '0', '3', '7', '0', '6', '7', '7', '1', '0', '4', '3', '3', '2', '6', '5', '1', '9']), .str (String.ofList ['5', '6', '2', '4', '4', '7', '6', '8', '5', '8', '1', '0', '4', '1', '3', '4', '7', '8', '5', '0', '9']), .str (String.ofList ['4', '2', '3', '8', '4', '4', '6', '1', '7', '2', '9', '0', '5', '0', '2', '5', '8', '8', '4', '7', '6']), .str (String.ofList ['5', '6', '3', '4', '7', '7', '3', '6', '9', '1', '1', '2', '4', '4', '2', '1', '9', '6', '4', '4', '8']), .str (String.ofList ['2', '7', '3', '0', '0', '2', '3', '5', '1', '1', '3', '2', '7', '0', '6', '5', '8', '5', '3', '9', '1']), .str (String.ofList ['2', '7', '3', '0', '1', '7', '4', '0', '6', '6', '6', '8', '1', '4', '7', '1', '5', '5', '3', '3', '4'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '6', '1', '5', '3', '4', '6', '7', '4', '0', '0', '8', '5'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '6', '2', '7', '4', '5', '0', '4', '0', '2', '3', '1', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_051_before_generic"
  err.flush

theorem array_moment_records_chunk_051 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 42)
      (SourceJson.white (momentRecordsChunk051Chars ++ tail)) acc =
      SourceJson.array (fuel + 41) (SourceJson.white tail) (momentRecordsChunk051Push acc) := by rfl

noncomputable def momentRecordsAcc052 : List SourceJson := momentRecordsChunk051Push momentRecordsAcc051

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_051_generic_complete"
  err.flush

noncomputable def momentRecordsBlock012Chars : List Char := momentRecordsChunk048Chars ++ momentRecordsChunk049Chars ++ momentRecordsChunk050Chars ++ momentRecordsChunk051Chars
noncomputable def momentRecordsBlock012Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk051Push (momentRecordsChunk050Push (momentRecordsChunk049Push (momentRecordsChunk048Push (acc))))

theorem array_moment_records_block_012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 45)
      (SourceJson.white (momentRecordsBlock012Chars ++ tail)) acc =
      SourceJson.array (fuel + 41) (SourceJson.white tail) (momentRecordsBlock012Push acc) := by
  have hinput : momentRecordsBlock012Chars ++ tail = momentRecordsChunk048Chars ++ (momentRecordsChunk049Chars ++ (momentRecordsChunk050Chars ++ (momentRecordsChunk051Chars ++ (tail)))) := by
    simp only [momentRecordsBlock012Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 45) (SourceJson.white (momentRecordsBlock012Chars ++ tail)) acc =
        SourceJson.array (fuel + 45) (SourceJson.white (momentRecordsChunk048Chars ++ (momentRecordsChunk049Chars ++ (momentRecordsChunk050Chars ++ (momentRecordsChunk051Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 45) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 44) (SourceJson.white (momentRecordsChunk049Chars ++ (momentRecordsChunk050Chars ++ (momentRecordsChunk051Chars ++ (tail))))) (momentRecordsChunk048Push (acc)) := array_moment_records_chunk_048 fuel (momentRecordsChunk049Chars ++ (momentRecordsChunk050Chars ++ (momentRecordsChunk051Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 43) (SourceJson.white (momentRecordsChunk050Chars ++ (momentRecordsChunk051Chars ++ (tail)))) (momentRecordsChunk049Push (momentRecordsChunk048Push (acc))) := array_moment_records_chunk_049 fuel (momentRecordsChunk050Chars ++ (momentRecordsChunk051Chars ++ (tail))) (momentRecordsChunk048Push (acc))
    _ = SourceJson.array (fuel + 42) (SourceJson.white (momentRecordsChunk051Chars ++ (tail))) (momentRecordsChunk050Push (momentRecordsChunk049Push (momentRecordsChunk048Push (acc)))) := array_moment_records_chunk_050 fuel (momentRecordsChunk051Chars ++ (tail)) (momentRecordsChunk049Push (momentRecordsChunk048Push (acc)))
    _ = SourceJson.array (fuel + 41) (SourceJson.white tail) (momentRecordsBlock012Push acc) := array_moment_records_chunk_051 fuel (tail) (momentRecordsChunk050Push (momentRecordsChunk049Push (momentRecordsChunk048Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_block_012_before_raw_binding"
  err.flush

theorem moment_records_block_012_prefix :
    (momentRest00 24926).take 2032 = momentRecordsBlock012Chars := by rfl

theorem moment_records_block_012_split :
    momentRest00 24926 = momentRecordsBlock012Chars ++ momentRest00 26958 := by
  calc
    momentRest00 24926 =
        (momentRest00 24926).take 2032 ++ (momentRest00 24926).drop 2032 :=
      (List.take_append_drop 2032 (momentRest00 24926)).symm
    _ = momentRecordsBlock012Chars ++ (momentRest00 24926).drop 2032 :=
      congrArg (fun p => p ++ (momentRest00 24926).drop 2032) moment_records_block_012_prefix
    _ = momentRecordsBlock012Chars ++ momentRest00 26958 :=
      congrArg (fun rest => momentRecordsBlock012Chars ++ rest) (momentRest00_drop 24926 2032)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_block_012_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_012 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 45)
      (SourceJson.white (momentRest00 24926)) acc =
      SourceJson.array (fuel + 41) (SourceJson.white (momentRest00 26958)) (momentRecordsBlock012Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 45) (SourceJson.white s) acc)
      moment_records_block_012_split).trans (array_moment_records_block_012 fuel (momentRest00 26958) acc)

theorem moment_records_through_block_012 (fuel : Nat) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRest00 364)) [] =
      SourceJson.array (fuel + 41) (SourceJson.white (momentRest00 26958)) momentRecordsAcc052 := by
  exact (moment_records_through_block_011 fuel).trans (array_moment_records_original_block_012 fuel momentRecordsAcc048)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_block_012_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment00Parsing
