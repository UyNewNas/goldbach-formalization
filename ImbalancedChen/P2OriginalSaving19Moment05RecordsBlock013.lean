import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock012

/-! Original moment records block 13. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk052Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '8', '1', '1', '0', '5', '3', '8', '3', '6', '3', '4', '2', '4', '1', '2', '7', '5', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '1', '3', '2', '4', '3', '3', '4', '7', '6', '2', '9', '8', '2', '4', '2', '3', '4', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '8', '2', '1', '7', '0', '8', '0', '2', '9', '8', '4', '3', '7', '9', '7', '4', '1', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '4', '1', '2', '8', '0', '1', '5', '3', '3', '4', '8', '3', '1', '0', '5', '3', '7', '8', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '2', '3', '2', '6', '0', '8', '5', '8', '7', '5', '7', '6', '7', '2', '5', '8', '0', '4', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '4', '4', '3', '3', '9', '1', '9', '4', '2', '3', '8', '9', '4', '4', '2', '4', '3', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '9', '7', '1', '6', '7', '4', '4', '3', '5', '7', '0', '8', '4', '6', '7', '6', '4', '8', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '7', '2', '5', '8', '1', '0', '1', '5', '1', '8', '5', '5', '8', '1', '9', '1', '9', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '1', '7', '9', '4', '3', '5', '5', '5', '9', '2', '3', '6', '8', '5', '7', '3', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '2', '0', '1', '1', '0', '9', '7', '6', '2', '6', '5', '5', '0', '0', '2', '0', '6', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '9', '5', '6', '3', '2', '3', '2', '0', '5', '8', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '9', '9', '9', '4', '2', '1', '3', '2', '9', '7', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk052Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['5', '2'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['3', '8', '8', '1', '1', '0', '5', '3', '8', '3', '6', '3', '4', '2', '4', '1', '2', '7', '5', '4', '5']), .str (String.ofList ['4', '2', '1', '3', '2', '4', '3', '3', '4', '7', '6', '2', '9', '8', '2', '4', '2', '3', '4', '5', '9']), .str (String.ofList ['1', '8', '8', '2', '1', '7', '0', '8', '0', '2', '9', '8', '4', '3', '7', '9', '7', '4', '1', '6', '9']), .str (String.ofList ['4', '3', '4', '1', '2', '8', '0', '1', '5', '3', '3', '4', '8', '3', '1', '0', '5', '3', '7', '8', '9']), .str (String.ofList ['3', '8', '2', '3', '2', '6', '0', '8', '5', '8', '7', '5', '7', '6', '7', '2', '5', '8', '0', '4', '4']), .str (String.ofList ['4', '1', '4', '4', '3', '3', '9', '1', '9', '4', '2', '3', '8', '9', '4', '4', '2', '4', '3', '0', '1']), .str (String.ofList ['1', '2', '0', '9', '7', '1', '6', '7', '4', '4', '3', '5', '7', '0', '8', '4', '6', '7', '6', '4', '8', '5']), .str (String.ofList ['3', '6', '7', '2', '5', '8', '1', '0', '1', '5', '1', '8', '5', '5', '8', '1', '9', '1', '9', '2', '7']), .str (String.ofList ['2', '7', '2', '1', '7', '9', '4', '3', '5', '5', '5', '9', '2', '3', '6', '8', '5', '7', '3', '4', '2']), .str (String.ofList ['2', '7', '2', '2', '0', '1', '1', '0', '9', '7', '6', '2', '6', '5', '5', '0', '0', '2', '0', '6', '9'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '1', '9', '5', '6', '3', '2', '3', '2', '0', '5', '8', '9'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '1', '9', '9', '9', '4', '2', '1', '3', '2', '9', '7', '8']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_052_before_generic"
  err.flush

theorem array_moment_records_chunk_052 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 41)
      (SourceJson.white (momentRecordsChunk052Chars ++ tail)) acc =
      SourceJson.array (fuel + 40) (SourceJson.white tail) (momentRecordsChunk052Push acc) := by rfl

noncomputable def momentRecordsAcc053 : List SourceJson := momentRecordsChunk052Push momentRecordsAcc052

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_052_generic_complete"
  err.flush

noncomputable def momentRecordsChunk053Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '0', '4', '6', '2', '2', '7', '6', '1', '9', '6', '2', '3', '6', '9', '9', '8', '3', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '7', '0', '6', '7', '7', '8', '8', '4', '5', '9', '4', '6', '3', '7', '2', '7', '8', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '4', '6', '5', '0', '1', '2', '9', '3', '9', '4', '2', '5', '0', '5', '8', '5', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '6', '2', '2', '5', '8', '3', '4', '8', '1', '2', '2', '3', '3', '5', '8', '6', '7', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '6', '9', '1', '9', '3', '4', '9', '9', '6', '9', '0', '7', '3', '7', '5', '1', '2', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '2', '1', '7', '4', '3', '1', '2', '1', '8', '5', '6', '1', '7', '1', '8', '3', '7', '5', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '6', '7', '0', '3', '3', '2', '9', '9', '0', '1', '1', '3', '7', '7', '6', '0', '6', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '4', '3', '8', '2', '0', '5', '3', '1', '8', '3', '7', '9', '1', '2', '7', '6', '3', '1', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '3', '8', '4', '1', '1', '5', '1', '0', '3', '3', '5', '7', '5', '7', '1', '7', '1', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '3', '8', '5', '8', '8', '3', '4', '2', '8', '0', '2', '7', '9', '9', '7', '2', '0', '5', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '6', '9', '3', '1', '4', '5', '1', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '7', '2', '0', '6', '5', '8', '1', '2', '5', '2', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk053Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['5', '3'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['2', '8', '0', '4', '6', '2', '2', '7', '6', '1', '9', '6', '2', '3', '6', '9', '9', '8', '3', '3', '7']), .str (String.ofList ['3', '2', '7', '0', '6', '7', '7', '8', '8', '4', '5', '9', '4', '6', '3', '7', '2', '7', '8', '0', '4']), .str (String.ofList ['1', '6', '8', '4', '6', '5', '0', '1', '2', '9', '3', '9', '4', '2', '5', '0', '5', '8', '5', '3', '9']), .str (String.ofList ['3', '3', '6', '2', '2', '5', '8', '3', '4', '8', '1', '2', '2', '3', '3', '5', '8', '6', '7', '5', '1']), .str (String.ofList ['3', '4', '6', '9', '1', '9', '3', '4', '9', '9', '6', '9', '0', '7', '3', '7', '5', '1', '2', '5', '7']), .str (String.ofList ['3', '6', '2', '1', '7', '4', '3', '1', '2', '1', '8', '5', '6', '1', '7', '1', '8', '3', '7', '5', '8']), .str (String.ofList ['1', '2', '0', '6', '7', '0', '3', '3', '2', '9', '9', '0', '1', '1', '3', '7', '7', '6', '0', '6', '1', '0']), .str (String.ofList ['3', '4', '4', '3', '8', '2', '0', '5', '3', '1', '8', '3', '7', '9', '1', '2', '7', '6', '3', '1', '1']), .str (String.ofList ['2', '2', '3', '8', '4', '1', '1', '5', '1', '0', '3', '3', '5', '7', '5', '7', '1', '7', '1', '9', '3']), .str (String.ofList ['2', '2', '3', '8', '5', '8', '8', '3', '4', '2', '8', '0', '2', '7', '9', '9', '7', '2', '0', '5', '9'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['8', '6', '9', '3', '1', '4', '5', '1', '0', '0', '0', '0'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['8', '7', '2', '0', '6', '5', '8', '1', '2', '5', '2', '8']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_053_before_generic"
  err.flush

theorem array_moment_records_chunk_053 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 40)
      (SourceJson.white (momentRecordsChunk053Chars ++ tail)) acc =
      SourceJson.array (fuel + 39) (SourceJson.white tail) (momentRecordsChunk053Push acc) := by rfl

noncomputable def momentRecordsAcc054 : List SourceJson := momentRecordsChunk053Push momentRecordsAcc053

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_053_generic_complete"
  err.flush

noncomputable def momentRecordsChunk054Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '1', '7', '0', '9', '6', '4', '1', '2', '0', '2', '6', '5', '3', '3', '1', '1', '2', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '1', '3', '4', '1', '5', '9', '9', '4', '1', '8', '7', '2', '8', '6', '3', '6', '5', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '6', '8', '0', '2', '7', '8', '0', '4', '2', '7', '3', '0', '1', '5', '4', '7', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '8', '6', '4', '6', '4', '9', '3', '2', '4', '4', '5', '1', '4', '6', '5', '5', '9', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '2', '4', '3', '7', '3', '5', '0', '0', '4', '6', '2', '1', '9', '5', '3', '8', '1', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '5', '2', '1', '5', '9', '3', '6', '0', '9', '3', '5', '4', '1', '4', '2', '5', '0', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '6', '1', '3', '6', '3', '5', '4', '5', '6', '0', '2', '4', '4', '4', '9', '1', '0', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '4', '8', '6', '5', '2', '5', '0', '9', '2', '1', '3', '3', '0', '4', '8', '1', '4', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '2', '4', '4', '7', '9', '4', '7', '9', '2', '6', '4', '1', '4', '8', '9', '1', '6', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '2', '4', '6', '1', '7', '9', '7', '2', '0', '8', '6', '0', '9', '8', '4', '5', '0', '8', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '9', '0', '6', '8', '1', '0', '8', '1', '0', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '9', '3', '0', '7', '9', '7', '5', '4', '6', '2', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk054Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['5', '4'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['2', '4', '1', '7', '0', '9', '6', '4', '1', '2', '0', '2', '6', '5', '3', '3', '1', '1', '2', '6', '1']), .str (String.ofList ['3', '0', '1', '3', '4', '1', '5', '9', '9', '4', '1', '8', '7', '2', '8', '6', '3', '6', '5', '5', '1']), .str (String.ofList ['1', '4', '6', '6', '8', '0', '2', '7', '8', '0', '4', '2', '7', '3', '0', '1', '5', '4', '7', '2', '2']), .str (String.ofList ['2', '5', '8', '6', '4', '6', '4', '9', '3', '2', '4', '4', '5', '1', '4', '6', '5', '5', '9', '8', '0']), .str (String.ofList ['2', '9', '2', '4', '3', '7', '3', '5', '0', '0', '4', '6', '2', '1', '9', '5', '3', '8', '1', '2', '4']), .str (String.ofList ['3', '2', '5', '2', '1', '5', '9', '3', '6', '0', '9', '3', '5', '4', '1', '4', '2', '5', '0', '1', '3']), .str (String.ofList ['1', '2', '7', '6', '1', '3', '6', '3', '5', '4', '5', '6', '0', '2', '4', '4', '4', '9', '1', '0', '5', '0']), .str (String.ofList ['3', '3', '4', '8', '6', '5', '2', '5', '0', '9', '2', '1', '3', '3', '0', '4', '8', '1', '4', '2', '0']), .str (String.ofList ['2', '4', '2', '4', '4', '7', '9', '4', '7', '9', '2', '6', '4', '1', '4', '8', '9', '1', '6', '9', '0']), .str (String.ofList ['2', '4', '2', '4', '6', '1', '7', '9', '7', '2', '0', '8', '6', '0', '9', '8', '4', '5', '0', '8', '3'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['7', '9', '0', '6', '8', '1', '0', '8', '1', '0', '2', '1'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['7', '9', '3', '0', '7', '9', '7', '5', '4', '6', '2', '6']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_054_before_generic"
  err.flush

theorem array_moment_records_chunk_054 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 39)
      (SourceJson.white (momentRecordsChunk054Chars ++ tail)) acc =
      SourceJson.array (fuel + 38) (SourceJson.white tail) (momentRecordsChunk054Push acc) := by rfl

noncomputable def momentRecordsAcc055 : List SourceJson := momentRecordsChunk054Push momentRecordsAcc054

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_054_generic_complete"
  err.flush

noncomputable def momentRecordsChunk055Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '9', '4', '4', '5', '3', '6', '3', '4', '4', '4', '0', '4', '1', '6', '7', '5', '4', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '9', '4', '2', '8', '8', '2', '1', '5', '3', '7', '9', '5', '9', '8', '1', '3', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '1', '7', '3', '3', '8', '0', '0', '8', '0', '2', '9', '9', '2', '6', '4', '7', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '6', '1', '6', '0', '4', '3', '2', '6', '5', '6', '9', '5', '7', '4', '9', '4', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '2', '4', '7', '3', '7', '6', '2', '1', '0', '3', '5', '1', '9', '0', '0', '5', '0', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '2', '5', '5', '5', '2', '2', '6', '8', '9', '2', '2', '4', '9', '9', '2', '1', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '1', '6', '7', '0', '6', '5', '3', '6', '4', '1', '9', '8', '6', '8', '2', '7', '8', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '6', '0', '3', '4', '4', '4', '1', '3', '7', '2', '3', '0', '3', '9', '1', '4', '3', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '5', '6', '4', '8', '9', '6', '1', '7', '2', '5', '5', '0', '8', '5', '7', '5', '6', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '5', '6', '6', '0', '4', '1', '5', '6', '6', '8', '0', '7', '6', '8', '0', '7', '6', '2', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '1', '7', '4', '6', '7', '4', '8', '1', '2', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '1', '9', '3', '0', '5', '0', '6', '5', '8', '3', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', '\r', '\n', ' ', ' ', ']']
noncomputable def momentRecordsChunk055Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['5', '5'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['1', '9', '9', '4', '4', '5', '3', '6', '3', '4', '4', '4', '0', '4', '1', '6', '7', '5', '4', '2', '6']), .str (String.ofList ['2', '5', '6', '9', '4', '2', '8', '8', '2', '1', '5', '3', '7', '9', '5', '9', '8', '1', '3', '1', '0']), .str (String.ofList ['8', '8', '1', '7', '3', '3', '8', '0', '0', '8', '0', '2', '9', '9', '2', '6', '4', '7', '2', '6']), .str (String.ofList ['1', '2', '8', '6', '1', '6', '0', '4', '3', '2', '6', '5', '6', '9', '5', '7', '4', '9', '4', '0', '9']), .str (String.ofList ['2', '0', '2', '4', '7', '3', '7', '6', '2', '1', '0', '3', '5', '1', '9', '0', '0', '5', '0', '4', '3']), .str (String.ofList ['1', '4', '4', '2', '5', '5', '5', '2', '2', '6', '8', '9', '2', '2', '4', '9', '9', '2', '1', '2', '8']), .str (String.ofList ['6', '2', '1', '6', '7', '0', '6', '5', '3', '6', '4', '1', '9', '8', '6', '8', '2', '7', '8', '6', '4']), .str (String.ofList ['3', '2', '6', '0', '3', '4', '4', '4', '1', '3', '7', '2', '3', '0', '3', '9', '1', '4', '3', '7', '3']), .str (String.ofList ['2', '2', '5', '6', '4', '8', '9', '6', '1', '7', '2', '5', '5', '0', '8', '5', '7', '5', '6', '5', '5']), .str (String.ofList ['2', '2', '5', '6', '6', '0', '4', '1', '5', '6', '6', '8', '0', '7', '6', '8', '0', '7', '6', '2', '8'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['9', '1', '7', '4', '6', '7', '4', '8', '1', '2', '1', '6'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['9', '1', '9', '3', '0', '5', '0', '6', '5', '8', '3', '6']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_055_before_generic"
  err.flush

theorem array_moment_records_chunk_055 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 38)
      (SourceJson.white (momentRecordsChunk055Chars ++ tail)) acc =
      .ok (.arr ((momentRecordsChunk055Push acc).reverse), tail) := by rfl

noncomputable def momentRecordsAcc056 : List SourceJson := momentRecordsChunk055Push momentRecordsAcc055

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_055_generic_complete"
  err.flush

noncomputable def momentRecordsBlock013Chars : List Char := momentRecordsChunk052Chars ++ momentRecordsChunk053Chars ++ momentRecordsChunk054Chars ++ momentRecordsChunk055Chars
noncomputable def momentRecordsBlock013Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk055Push (momentRecordsChunk054Push (momentRecordsChunk053Push (momentRecordsChunk052Push (acc))))

theorem array_moment_records_block_013 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 41)
      (SourceJson.white (momentRecordsBlock013Chars ++ tail)) acc =
      .ok (.arr ((momentRecordsBlock013Push acc).reverse), tail) := by
  have hinput : momentRecordsBlock013Chars ++ tail = momentRecordsChunk052Chars ++ (momentRecordsChunk053Chars ++ (momentRecordsChunk054Chars ++ (momentRecordsChunk055Chars ++ (tail)))) := by
    simp only [momentRecordsBlock013Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 41) (SourceJson.white (momentRecordsBlock013Chars ++ tail)) acc =
        SourceJson.array (fuel + 41) (SourceJson.white (momentRecordsChunk052Chars ++ (momentRecordsChunk053Chars ++ (momentRecordsChunk054Chars ++ (momentRecordsChunk055Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 41) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 40) (SourceJson.white (momentRecordsChunk053Chars ++ (momentRecordsChunk054Chars ++ (momentRecordsChunk055Chars ++ (tail))))) (momentRecordsChunk052Push (acc)) := array_moment_records_chunk_052 fuel (momentRecordsChunk053Chars ++ (momentRecordsChunk054Chars ++ (momentRecordsChunk055Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 39) (SourceJson.white (momentRecordsChunk054Chars ++ (momentRecordsChunk055Chars ++ (tail)))) (momentRecordsChunk053Push (momentRecordsChunk052Push (acc))) := array_moment_records_chunk_053 fuel (momentRecordsChunk054Chars ++ (momentRecordsChunk055Chars ++ (tail))) (momentRecordsChunk052Push (acc))
    _ = SourceJson.array (fuel + 38) (SourceJson.white (momentRecordsChunk055Chars ++ (tail))) (momentRecordsChunk054Push (momentRecordsChunk053Push (momentRecordsChunk052Push (acc)))) := array_moment_records_chunk_054 fuel (momentRecordsChunk055Chars ++ (tail)) (momentRecordsChunk053Push (momentRecordsChunk052Push (acc)))
    _ = .ok (.arr ((momentRecordsBlock013Push acc).reverse), tail) := array_moment_records_chunk_055 fuel (tail) (momentRecordsChunk054Push (momentRecordsChunk053Push (momentRecordsChunk052Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_013_before_raw_binding"
  err.flush

theorem moment_records_block_013_prefix :
    (momentRest05 26936).take 2032 = momentRecordsBlock013Chars := by rfl

theorem moment_records_block_013_split :
    momentRest05 26936 = momentRecordsBlock013Chars ++ momentRest05 28968 := by
  calc
    momentRest05 26936 =
        (momentRest05 26936).take 2032 ++ (momentRest05 26936).drop 2032 :=
      (List.take_append_drop 2032 (momentRest05 26936)).symm
    _ = momentRecordsBlock013Chars ++ (momentRest05 26936).drop 2032 :=
      congrArg (fun p => p ++ (momentRest05 26936).drop 2032) moment_records_block_013_prefix
    _ = momentRecordsBlock013Chars ++ momentRest05 28968 :=
      congrArg (fun rest => momentRecordsBlock013Chars ++ rest) (momentRest05_drop 26936 2032)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_013_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_013 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 41)
      (SourceJson.white (momentRest05 26936)) acc =
      .ok (.arr ((momentRecordsBlock013Push acc).reverse), momentRest05 28968) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 41) (SourceJson.white s) acc)
      moment_records_block_013_split).trans (array_moment_records_block_013 fuel (momentRest05 28968) acc)

noncomputable def momentRecordsArrayValue : SourceJson := .arr (momentRecordsAcc056.reverse)

theorem moment_records_through_block_013 (fuel : Nat) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRest05 364)) [] =
      .ok (momentRecordsArrayValue, momentRest05 28968) := by
  exact (moment_records_through_block_012 fuel).trans (array_moment_records_original_block_013 fuel momentRecordsAcc052)

theorem value_moment_records_original (fuel : Nat) :
    SourceJson.value (fuel + 94) (momentRest05 363) =
      .ok (momentRecordsArrayValue, momentRest05 28968) := by
  exact (value_moment_records_open fuel).trans (moment_records_through_block_013 fuel)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_013_complete"
  err.flush

#print axioms array_moment_records_chunk_052
#print axioms array_moment_records_chunk_053
#print axioms array_moment_records_chunk_054
#print axioms array_moment_records_chunk_055
#print axioms array_moment_records_block_013
#print axioms moment_records_block_013_prefix
#print axioms moment_records_block_013_split
#print axioms array_moment_records_original_block_013
#print axioms moment_records_through_block_013
#print axioms value_moment_records_original

end ImbalancedChen.P2OriginalSaving19Moment05Parsing
