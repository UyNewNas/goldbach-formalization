import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock011

/-! Original moment records block 12. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk048Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '3', '4', '5', '8', '1', '6', '0', '2', '9', '2', '5', '1', '6', '8', '5', '0', '7', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '9', '3', '8', '5', '1', '1', '1', '6', '4', '6', '6', '0', '3', '2', '2', '8', '8', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '1', '7', '3', '3', '8', '0', '0', '8', '0', '2', '9', '9', '2', '6', '4', '7', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '0', '9', '6', '0', '8', '9', '9', '8', '0', '0', '3', '7', '3', '3', '2', '6', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '2', '8', '6', '5', '8', '0', '6', '2', '6', '3', '9', '2', '8', '6', '9', '8', '0', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '2', '5', '5', '5', '2', '2', '6', '8', '9', '2', '2', '4', '9', '9', '2', '1', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '4', '1', '3', '7', '1', '2', '6', '0', '6', '1', '1', '2', '1', '8', '7', '8', '5', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '0', '2', '0', '2', '2', '2', '9', '4', '5', '6', '8', '9', '6', '2', '2', '1', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '1', '0', '1', '7', '8', '4', '0', '1', '9', '9', '4', '6', '7', '4', '4', '2', '2', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '1', '0', '1', '3', '5', '5', '7', '2', '5', '3', '4', '7', '1', '7', '2', '8', '8', '6', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '0', '7', '8', '6', '9', '4', '9', '7', '3', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '0', '9', '8', '4', '5', '5', '1', '6', '7', '1', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk048Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['4', '8'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['2', '6', '3', '4', '5', '8', '1', '6', '0', '2', '9', '2', '5', '1', '6', '8', '5', '0', '7', '5', '9']), .str (String.ofList ['3', '2', '9', '3', '8', '5', '1', '1', '1', '6', '4', '6', '6', '0', '3', '2', '2', '8', '8', '5', '1']), .str (String.ofList ['8', '8', '1', '7', '3', '3', '8', '0', '0', '8', '0', '2', '9', '9', '2', '6', '4', '7', '2', '6']), .str (String.ofList ['1', '1', '7', '0', '9', '6', '0', '8', '9', '9', '8', '0', '0', '3', '7', '3', '3', '2', '6', '3', '1']), .str (String.ofList ['2', '1', '2', '8', '6', '5', '8', '0', '6', '2', '6', '3', '9', '2', '8', '6', '9', '8', '0', '6', '7']), .str (String.ofList ['1', '4', '4', '2', '5', '5', '5', '2', '2', '6', '8', '9', '2', '2', '4', '9', '9', '2', '1', '2', '8']), .str (String.ofList ['6', '8', '4', '1', '3', '7', '1', '2', '6', '0', '6', '1', '1', '2', '1', '8', '7', '8', '5', '7', '8']), .str (String.ofList ['2', '8', '7', '0', '2', '0', '2', '2', '2', '9', '4', '5', '6', '8', '9', '6', '2', '2', '1', '9', '5']), .str (String.ofList ['2', '5', '1', '0', '1', '7', '8', '4', '0', '1', '9', '9', '4', '6', '7', '4', '4', '2', '2', '1', '5']), .str (String.ofList ['2', '5', '1', '0', '1', '3', '5', '5', '7', '2', '5', '3', '4', '7', '1', '7', '2', '8', '8', '6', '8'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['9', '0', '7', '8', '6', '9', '4', '9', '7', '3', '1', '5'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['9', '0', '9', '8', '4', '5', '5', '1', '6', '7', '1', '0']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_048_before_generic"
  err.flush

theorem array_moment_records_chunk_048 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 45)
      (SourceJson.white (momentRecordsChunk048Chars ++ tail)) acc =
      SourceJson.array (fuel + 44) (SourceJson.white tail) (momentRecordsChunk048Push acc) := by rfl

noncomputable def momentRecordsAcc049 : List SourceJson := momentRecordsChunk048Push momentRecordsAcc048

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_048_generic_complete"
  err.flush

noncomputable def momentRecordsChunk049Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '4', '2', '0', '0', '2', '4', '8', '0', '4', '5', '3', '6', '9', '5', '4', '5', '8', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '9', '5', '6', '7', '1', '9', '7', '4', '4', '3', '2', '6', '3', '8', '2', '5', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '3', '4', '6', '3', '6', '5', '8', '4', '6', '7', '9', '7', '5', '5', '3', '2', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '8', '3', '3', '1', '5', '5', '0', '6', '5', '0', '9', '8', '0', '7', '4', '5', '0', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '9', '1', '4', '0', '2', '7', '0', '7', '2', '2', '8', '5', '7', '2', '2', '0', '7', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '1', '2', '8', '2', '8', '4', '2', '1', '4', '2', '9', '6', '7', '1', '2', '7', '1', '5', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '8', '0', '5', '5', '4', '7', '4', '6', '8', '4', '5', '0', '3', '9', '4', '1', '7', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '1', '1', '1', '3', '0', '2', '4', '7', '6', '8', '3', '5', '4', '4', '4', '9', '9', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '8', '6', '6', '8', '3', '4', '5', '7', '9', '9', '9', '0', '6', '1', '1', '6', '1', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '8', '6', '9', '8', '7', '5', '6', '8', '6', '0', '8', '0', '1', '3', '2', '7', '2', '8', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '0', '9', '5', '9', '6', '1', '8', '5', '7', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '1', '5', '5', '9', '9', '0', '4', '0', '5', '4', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk049Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['4', '9'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['1', '9', '4', '2', '0', '0', '2', '4', '8', '0', '4', '5', '3', '6', '9', '5', '4', '5', '8', '0', '9']), .str (String.ofList ['2', '0', '5', '9', '5', '6', '7', '1', '9', '7', '4', '4', '3', '2', '6', '3', '8', '2', '5', '4', '8']), .str (String.ofList ['1', '3', '0', '3', '4', '6', '3', '6', '5', '8', '4', '6', '7', '9', '7', '5', '5', '3', '2', '2', '7']), .str (String.ofList ['4', '2', '8', '3', '3', '1', '5', '5', '0', '6', '5', '0', '9', '8', '0', '7', '4', '5', '0', '2', '7']), .str (String.ofList ['2', '6', '9', '1', '4', '0', '2', '7', '0', '7', '2', '2', '8', '5', '7', '2', '2', '0', '7', '4', '1']), .str (String.ofList ['2', '9', '1', '2', '8', '2', '8', '4', '2', '1', '4', '2', '9', '6', '7', '1', '2', '7', '1', '5', '4']), .str (String.ofList ['6', '0', '8', '0', '5', '5', '4', '7', '4', '6', '8', '4', '5', '0', '3', '9', '4', '1', '7', '3', '6']), .str (String.ofList ['6', '2', '1', '1', '1', '3', '0', '2', '4', '7', '6', '8', '3', '5', '4', '4', '4', '9', '9', '6', '3']), .str (String.ofList ['4', '2', '8', '6', '6', '8', '3', '4', '5', '7', '9', '9', '9', '0', '6', '1', '1', '6', '1', '1', '2']), .str (String.ofList ['4', '2', '8', '6', '9', '8', '7', '5', '6', '8', '6', '0', '8', '0', '1', '3', '2', '7', '2', '8', '9'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['2', '0', '0', '9', '5', '9', '6', '1', '8', '5', '7', '0', '5'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['2', '0', '1', '5', '5', '9', '9', '0', '4', '0', '5', '4', '2']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_049_before_generic"
  err.flush

theorem array_moment_records_chunk_049 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 44)
      (SourceJson.white (momentRecordsChunk049Chars ++ tail)) acc =
      SourceJson.array (fuel + 43) (SourceJson.white tail) (momentRecordsChunk049Push acc) := by rfl

noncomputable def momentRecordsAcc050 : List SourceJson := momentRecordsChunk049Push momentRecordsAcc049

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_049_generic_complete"
  err.flush

noncomputable def momentRecordsChunk050Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '9', '2', '9', '1', '0', '0', '5', '7', '9', '9', '0', '9', '5', '9', '2', '5', '9', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '3', '3', '5', '4', '2', '1', '7', '1', '8', '8', '0', '1', '8', '5', '6', '8', '5', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '1', '5', '7', '2', '7', '3', '8', '0', '6', '7', '3', '8', '5', '2', '1', '0', '4', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '2', '1', '9', '0', '4', '4', '7', '0', '9', '8', '2', '4', '3', '1', '0', '3', '1', '2', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '5', '6', '7', '3', '8', '2', '6', '8', '2', '9', '4', '6', '8', '9', '8', '3', '3', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '7', '1', '9', '2', '1', '6', '4', '6', '7', '2', '5', '6', '0', '6', '6', '8', '9', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '9', '4', '0', '1', '6', '0', '2', '4', '0', '3', '2', '0', '9', '5', '9', '8', '4', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '3', '9', '9', '8', '4', '9', '3', '6', '6', '8', '3', '0', '5', '1', '8', '3', '9', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '8', '6', '8', '5', '8', '0', '1', '6', '9', '1', '0', '2', '0', '3', '1', '1', '7', '7', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '8', '7', '1', '6', '1', '0', '3', '0', '2', '4', '2', '2', '6', '7', '0', '6', '9', '8', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '0', '3', '8', '4', '8', '7', '0', '8', '0', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '1', '0', '7', '9', '0', '6', '9', '1', '5', '8', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk050Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['5', '0'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['3', '5', '9', '2', '9', '1', '0', '0', '5', '7', '9', '9', '0', '9', '5', '9', '2', '5', '9', '2', '9']), .str (String.ofList ['3', '8', '3', '3', '5', '4', '2', '1', '7', '1', '8', '8', '0', '1', '8', '5', '6', '8', '5', '3', '8']), .str (String.ofList ['1', '7', '1', '5', '7', '2', '7', '3', '8', '0', '6', '7', '3', '8', '5', '2', '1', '0', '4', '3', '0']), .str (String.ofList ['4', '8', '2', '1', '9', '0', '4', '4', '7', '0', '9', '8', '2', '4', '3', '1', '0', '3', '1', '2', '3']), .str (String.ofList ['3', '6', '5', '6', '7', '3', '8', '2', '6', '8', '2', '9', '4', '6', '8', '9', '8', '3', '3', '4', '6']), .str (String.ofList ['3', '8', '7', '1', '9', '2', '1', '6', '4', '6', '7', '2', '5', '6', '0', '6', '6', '8', '9', '3', '9']), .str (String.ofList ['7', '6', '9', '4', '0', '1', '6', '0', '2', '4', '0', '3', '2', '0', '9', '5', '9', '8', '4', '2', '2']), .str (String.ofList ['6', '2', '3', '9', '9', '8', '4', '9', '3', '6', '6', '8', '3', '0', '5', '1', '8', '3', '9', '1', '6']), .str (String.ofList ['4', '2', '8', '6', '8', '5', '8', '0', '1', '6', '9', '1', '0', '2', '0', '3', '1', '1', '7', '7', '7']), .str (String.ofList ['4', '2', '8', '7', '1', '6', '1', '0', '3', '0', '2', '4', '2', '2', '6', '7', '0', '6', '9', '8', '3'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '9', '0', '3', '8', '4', '8', '7', '0', '8', '0', '6', '3'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '9', '1', '0', '7', '9', '0', '6', '9', '1', '5', '8', '4']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_050_before_generic"
  err.flush

theorem array_moment_records_chunk_050 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 43)
      (SourceJson.white (momentRecordsChunk050Chars ++ tail)) acc =
      SourceJson.array (fuel + 42) (SourceJson.white tail) (momentRecordsChunk050Push acc) := by rfl

noncomputable def momentRecordsAcc051 : List SourceJson := momentRecordsChunk050Push momentRecordsAcc050

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_050_generic_complete"
  err.flush

noncomputable def momentRecordsChunk051Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '9', '6', '9', '7', '0', '1', '4', '0', '8', '9', '1', '2', '2', '2', '2', '7', '2', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '7', '3', '0', '5', '2', '7', '8', '9', '9', '3', '3', '5', '0', '2', '1', '0', '5', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '9', '8', '4', '9', '0', '4', '9', '1', '2', '6', '5', '7', '7', '3', '3', '8', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '7', '0', '3', '1', '1', '2', '6', '8', '3', '7', '8', '7', '6', '8', '2', '9', '5', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '0', '1', '5', '3', '1', '9', '7', '2', '9', '3', '9', '9', '9', '3', '2', '8', '1', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '9', '3', '7', '9', '9', '5', '4', '0', '5', '5', '7', '6', '4', '6', '2', '2', '9', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '3', '7', '7', '3', '7', '3', '7', '1', '5', '5', '9', '4', '0', '7', '8', '0', '9', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '2', '0', '9', '6', '0', '0', '7', '5', '3', '0', '7', '5', '1', '5', '1', '3', '9', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '9', '2', '2', '2', '9', '2', '0', '3', '8', '6', '7', '0', '2', '3', '7', '4', '2', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '9', '2', '4', '6', '2', '3', '0', '5', '7', '7', '8', '8', '0', '2', '9', '1', '2', '3', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '4', '5', '2', '0', '4', '4', '3', '0', '4', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '4', '9', '8', '4', '6', '8', '0', '8', '7', '2', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk051Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['5', '1'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['3', '9', '9', '6', '9', '7', '0', '1', '4', '0', '8', '9', '1', '2', '2', '2', '2', '7', '2', '2', '1']), .str (String.ofList ['4', '2', '7', '3', '0', '5', '2', '7', '8', '9', '9', '3', '3', '5', '0', '2', '1', '0', '5', '6', '1']), .str (String.ofList ['1', '8', '6', '9', '8', '4', '9', '0', '4', '9', '1', '2', '6', '5', '7', '7', '3', '3', '8', '8', '8']), .str (String.ofList ['4', '4', '7', '0', '3', '1', '1', '2', '6', '8', '3', '7', '8', '7', '6', '8', '2', '9', '5', '1', '5']), .str (String.ofList ['3', '8', '0', '1', '5', '3', '1', '9', '7', '2', '9', '3', '9', '9', '9', '3', '2', '8', '1', '0', '5']), .str (String.ofList ['4', '1', '9', '3', '7', '9', '9', '5', '4', '0', '5', '5', '7', '6', '4', '6', '2', '2', '9', '7', '5']), .str (String.ofList ['8', '9', '3', '7', '7', '3', '7', '3', '7', '1', '5', '5', '9', '4', '0', '7', '8', '0', '9', '1', '8']), .str (String.ofList ['4', '9', '2', '0', '9', '6', '0', '0', '7', '5', '3', '0', '7', '5', '1', '5', '1', '3', '9', '0', '6']), .str (String.ofList ['2', '5', '9', '2', '2', '2', '9', '2', '0', '3', '8', '6', '7', '0', '2', '3', '7', '4', '2', '3', '7']), .str (String.ofList ['2', '5', '9', '2', '4', '6', '2', '3', '0', '5', '7', '7', '8', '8', '0', '2', '9', '1', '2', '3', '5'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '3', '4', '5', '2', '0', '4', '4', '3', '0', '4', '8', '2'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '3', '4', '9', '8', '4', '6', '8', '0', '8', '7', '2', '2']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_051_before_generic"
  err.flush

theorem array_moment_records_chunk_051 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 42)
      (SourceJson.white (momentRecordsChunk051Chars ++ tail)) acc =
      SourceJson.array (fuel + 41) (SourceJson.white tail) (momentRecordsChunk051Push acc) := by rfl

noncomputable def momentRecordsAcc052 : List SourceJson := momentRecordsChunk051Push momentRecordsAcc051

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_051_generic_complete"
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
  err.putStrLn "P26_MOMENT05 records_block_012_before_raw_binding"
  err.flush

theorem moment_records_block_012_prefix :
    (momentRest05 24907).take 2029 = momentRecordsBlock012Chars := by rfl

theorem moment_records_block_012_split :
    momentRest05 24907 = momentRecordsBlock012Chars ++ momentRest05 26936 := by
  calc
    momentRest05 24907 =
        (momentRest05 24907).take 2029 ++ (momentRest05 24907).drop 2029 :=
      (List.take_append_drop 2029 (momentRest05 24907)).symm
    _ = momentRecordsBlock012Chars ++ (momentRest05 24907).drop 2029 :=
      congrArg (fun p => p ++ (momentRest05 24907).drop 2029) moment_records_block_012_prefix
    _ = momentRecordsBlock012Chars ++ momentRest05 26936 :=
      congrArg (fun rest => momentRecordsBlock012Chars ++ rest) (momentRest05_drop 24907 2029)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_012_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_012 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 45)
      (SourceJson.white (momentRest05 24907)) acc =
      SourceJson.array (fuel + 41) (SourceJson.white (momentRest05 26936)) (momentRecordsBlock012Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 45) (SourceJson.white s) acc)
      moment_records_block_012_split).trans (array_moment_records_block_012 fuel (momentRest05 26936) acc)

theorem moment_records_through_block_012 (fuel : Nat) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRest05 364)) [] =
      SourceJson.array (fuel + 41) (SourceJson.white (momentRest05 26936)) momentRecordsAcc052 := by
  exact (moment_records_through_block_011 fuel).trans (array_moment_records_original_block_012 fuel momentRecordsAcc048)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_012_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment05Parsing
