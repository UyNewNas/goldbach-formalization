import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock007

/-! Original moment records block 8. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk032Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '5', '4', '7', '0', '1', '7', '3', '1', '0', '3', '0', '7', '2', '4', '9', '2', '8', '6', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '6', '3', '4', '0', '1', '8', '3', '8', '0', '0', '8', '7', '9', '6', '0', '6', '4', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '6', '9', '7', '4', '4', '8', '6', '4', '3', '4', '8', '3', '5', '2', '5', '9', '5', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '7', '5', '3', '0', '5', '5', '7', '3', '4', '8', '3', '9', '9', '6', '7', '6', '9', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '0', '1', '6', '2', '6', '6', '0', '6', '7', '5', '1', '0', '2', '7', '8', '2', '2', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '6', '9', '3', '7', '3', '6', '6', '2', '4', '7', '1', '5', '2', '9', '2', '2', '4', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '6', '2', '4', '1', '5', '2', '4', '9', '0', '0', '1', '1', '2', '1', '0', '5', '3', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '5', '8', '6', '4', '5', '0', '6', '6', '1', '2', '4', '4', '4', '8', '3', '5', '9', '9', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '6', '7', '7', '1', '7', '6', '7', '9', '5', '9', '0', '6', '8', '0', '8', '5', '1', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '3', '1', '4', '2', '6', '3', '7', '2', '1', '3', '1', '6', '4', '2', '6', '0', '7', '6', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '4', '7', '8', '5', '9', '3', '0', '2', '1', '3', '2', '7', '8', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '4', '9', '1', '8', '4', '4', '4', '3', '5', '9', '3', '8', '1', '4', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk032Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['3', '2'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['2', '1', '5', '4', '7', '0', '1', '7', '3', '1', '0', '3', '0', '7', '2', '4', '9', '2', '8', '6', '6']), .str (String.ofList ['2', '7', '2', '6', '3', '4', '0', '1', '8', '3', '8', '0', '0', '8', '7', '9', '6', '0', '6', '4', '0']), .str (String.ofList ['1', '3', '6', '9', '7', '4', '4', '8', '6', '4', '3', '4', '8', '3', '5', '2', '5', '9', '5', '6', '2']), .str (String.ofList ['2', '2', '7', '5', '3', '0', '5', '5', '7', '3', '4', '8', '3', '9', '9', '6', '7', '6', '9', '2', '7']), .str (String.ofList ['2', '9', '0', '1', '6', '2', '6', '6', '0', '6', '7', '5', '1', '0', '2', '7', '8', '2', '2', '0', '6']), .str (String.ofList ['3', '0', '6', '9', '3', '7', '3', '6', '6', '2', '4', '7', '1', '5', '2', '9', '2', '2', '4', '3', '1']), .str (String.ofList ['1', '3', '1', '6', '2', '4', '1', '5', '2', '4', '9', '0', '0', '1', '1', '2', '1', '0', '5', '3', '1', '4']), .str (String.ofList ['2', '6', '5', '8', '6', '4', '5', '0', '6', '6', '1', '2', '4', '4', '4', '8', '3', '5', '9', '9', '9']), .str (String.ofList ['3', '1', '6', '7', '7', '1', '7', '6', '7', '9', '5', '9', '0', '6', '8', '0', '8', '5', '1', '8', '6']), .str (String.ofList ['2', '2', '3', '1', '4', '2', '6', '3', '7', '2', '1', '3', '1', '6', '4', '2', '6', '0', '7', '6', '3'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['4', '4', '7', '8', '5', '9', '3', '0', '2', '1', '3', '2', '7', '8', '5', '0'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['4', '4', '9', '1', '8', '4', '4', '4', '3', '5', '9', '3', '8', '1', '4', '9']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_032_before_generic"
  err.flush

theorem array_moment_records_chunk_032 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 61)
      (SourceJson.white (momentRecordsChunk032Chars ++ tail)) acc =
      SourceJson.array (fuel + 60) (SourceJson.white tail) (momentRecordsChunk032Push acc) := by rfl

noncomputable def momentRecordsAcc033 : List SourceJson := momentRecordsChunk032Push momentRecordsAcc032

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_032_generic_complete"
  err.flush

noncomputable def momentRecordsChunk033Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '6', '8', '5', '2', '3', '7', '0', '5', '5', '9', '2', '8', '2', '1', '5', '0', '3', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '7', '7', '3', '2', '4', '4', '5', '3', '5', '0', '4', '2', '0', '7', '5', '6', '8', '2', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '4', '5', '5', '8', '4', '5', '3', '3', '7', '6', '0', '4', '0', '0', '5', '6', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '7', '1', '1', '8', '2', '7', '1', '5', '7', '2', '6', '2', '7', '9', '3', '6', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '7', '0', '6', '7', '9', '0', '2', '9', '2', '4', '2', '1', '6', '1', '9', '7', '8', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '2', '0', '7', '8', '4', '9', '2', '5', '0', '3', '6', '4', '5', '8', '2', '6', '1', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '5', '9', '3', '8', '4', '3', '0', '2', '9', '1', '3', '1', '9', '6', '8', '1', '2', '8', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '5', '1', '7', '2', '7', '2', '7', '6', '3', '7', '7', '9', '8', '9', '7', '4', '7', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '8', '2', '0', '7', '4', '2', '2', '7', '1', '7', '6', '9', '1', '1', '9', '3', '5', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '2', '9', '5', '9', '5', '5', '8', '6', '8', '6', '2', '5', '3', '9', '4', '3', '0', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '9', '6', '9', '5', '1', '3', '4', '8', '4', '3', '6', '4', '3', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '9', '7', '9', '0', '6', '5', '5', '0', '8', '2', '9', '3', '8', '5', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk033Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['3', '3'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['1', '7', '2', '6', '8', '5', '2', '3', '7', '0', '5', '5', '9', '2', '8', '2', '1', '5', '0', '3', '2']), .str (String.ofList ['2', '2', '7', '7', '3', '2', '4', '4', '5', '3', '5', '0', '4', '2', '0', '7', '5', '6', '8', '2', '3']), .str (String.ofList ['8', '2', '4', '5', '5', '8', '4', '5', '3', '3', '7', '6', '0', '4', '0', '0', '5', '6', '1', '6']), .str (String.ofList ['1', '0', '5', '7', '1', '1', '8', '2', '7', '1', '5', '7', '2', '6', '2', '7', '9', '3', '6', '1', '9']), .str (String.ofList ['1', '9', '7', '0', '6', '7', '9', '0', '2', '9', '2', '4', '2', '1', '6', '1', '9', '7', '8', '9', '2']), .str (String.ofList ['1', '2', '9', '2', '0', '7', '8', '4', '9', '2', '5', '0', '3', '6', '4', '5', '8', '2', '6', '1', '1']), .str (String.ofList ['6', '3', '5', '9', '3', '8', '4', '3', '0', '2', '9', '1', '3', '1', '9', '6', '8', '1', '2', '8', '9']), .str (String.ofList ['2', '6', '5', '1', '7', '2', '7', '2', '7', '6', '3', '7', '7', '9', '8', '9', '7', '4', '7', '7', '3']), .str (String.ofList ['2', '9', '8', '2', '0', '7', '4', '2', '2', '7', '1', '7', '6', '9', '1', '1', '9', '3', '5', '4', '6']), .str (String.ofList ['2', '0', '7', '2', '9', '5', '9', '5', '5', '8', '6', '8', '6', '2', '5', '3', '9', '4', '3', '0', '5'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['4', '9', '6', '9', '5', '1', '3', '4', '8', '4', '3', '6', '4', '3', '0', '0'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['4', '9', '7', '9', '0', '6', '5', '5', '0', '8', '2', '9', '3', '8', '5', '4']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_033_before_generic"
  err.flush

theorem array_moment_records_chunk_033 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 60)
      (SourceJson.white (momentRecordsChunk033Chars ++ tail)) acc =
      SourceJson.array (fuel + 59) (SourceJson.white tail) (momentRecordsChunk033Push acc) := by rfl

noncomputable def momentRecordsAcc034 : List SourceJson := momentRecordsChunk033Push momentRecordsAcc033

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_033_generic_complete"
  err.flush

noncomputable def momentRecordsChunk034Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '6', '1', '8', '7', '9', '2', '1', '6', '1', '6', '5', '0', '1', '9', '8', '5', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '1', '2', '1', '0', '7', '9', '4', '2', '6', '0', '9', '1', '0', '6', '6', '1', '8', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '0', '2', '2', '4', '8', '3', '8', '9', '8', '4', '7', '5', '1', '3', '4', '4', '3', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '9', '4', '3', '4', '1', '9', '1', '4', '2', '8', '1', '3', '0', '4', '4', '4', '6', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '2', '4', '6', '3', '4', '7', '4', '3', '3', '2', '1', '7', '7', '2', '0', '3', '1', '4', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '2', '9', '7', '2', '0', '1', '3', '9', '6', '4', '6', '2', '2', '1', '5', '2', '7', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '2', '8', '2', '0', '6', '3', '2', '7', '5', '2', '5', '7', '8', '1', '2', '2', '5', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '7', '0', '9', '5', '4', '8', '1', '9', '7', '9', '2', '8', '7', '0', '4', '7', '8', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '3', '8', '0', '6', '6', '3', '4', '6', '4', '2', '9', '6', '1', '7', '4', '1', '8', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '8', '3', '6', '7', '5', '9', '0', '6', '6', '4', '2', '7', '1', '7', '2', '3', '6', '4', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '5', '0', '2', '0', '8', '9', '2', '9', '7', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '5', '5', '8', '9', '5', '8', '4', '8', '9', '3', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk034Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['3', '4'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['3', '3', '2', '6', '1', '8', '7', '9', '2', '1', '6', '1', '6', '5', '0', '1', '9', '8', '5', '6', '7']), .str (String.ofList ['3', '6', '1', '2', '1', '0', '7', '9', '4', '2', '6', '0', '9', '1', '0', '6', '6', '1', '8', '4', '8']), .str (String.ofList ['1', '7', '6', '0', '2', '2', '4', '8', '3', '8', '9', '8', '4', '7', '5', '1', '3', '4', '4', '3', '3']), .str (String.ofList ['3', '7', '9', '4', '3', '4', '1', '9', '1', '4', '2', '8', '1', '3', '0', '4', '4', '4', '6', '1', '7']), .str (String.ofList ['4', '1', '2', '4', '6', '3', '4', '7', '4', '3', '3', '2', '1', '7', '7', '2', '0', '3', '1', '4', '0']), .str (String.ofList ['3', '7', '2', '9', '7', '2', '0', '1', '3', '9', '6', '4', '6', '2', '2', '1', '5', '2', '7', '2', '7']), .str (String.ofList ['1', '4', '9', '2', '8', '2', '0', '6', '3', '2', '7', '5', '2', '5', '7', '8', '1', '2', '2', '5', '5', '2']), .str (String.ofList ['2', '9', '7', '0', '9', '5', '4', '8', '1', '9', '7', '9', '2', '8', '7', '0', '4', '7', '8', '0', '1']), .str (String.ofList ['3', '8', '3', '8', '0', '6', '6', '3', '4', '6', '4', '2', '9', '6', '1', '7', '4', '1', '8', '6', '2']), .str (String.ofList ['2', '1', '8', '3', '6', '7', '5', '9', '0', '6', '6', '4', '2', '7', '1', '7', '2', '3', '6', '4', '1'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '5', '5', '0', '2', '0', '8', '9', '2', '9', '7', '8', '0'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '5', '5', '5', '8', '9', '5', '8', '4', '8', '9', '3', '3']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_034_before_generic"
  err.flush

theorem array_moment_records_chunk_034 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 59)
      (SourceJson.white (momentRecordsChunk034Chars ++ tail)) acc =
      SourceJson.array (fuel + 58) (SourceJson.white tail) (momentRecordsChunk034Push acc) := by rfl

noncomputable def momentRecordsAcc035 : List SourceJson := momentRecordsChunk034Push momentRecordsAcc034

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_034_generic_complete"
  err.flush

noncomputable def momentRecordsChunk035Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '6', '9', '7', '5', '9', '9', '2', '0', '5', '3', '1', '6', '7', '9', '1', '2', '8', '9', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '1', '0', '5', '0', '0', '0', '1', '9', '9', '7', '8', '4', '7', '7', '3', '8', '7', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '7', '9', '6', '8', '9', '4', '9', '2', '2', '0', '1', '4', '9', '4', '4', '7', '6', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '9', '5', '0', '0', '0', '0', '2', '1', '0', '0', '1', '7', '5', '9', '6', '2', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '4', '5', '0', '8', '8', '8', '6', '5', '6', '1', '0', '3', '7', '5', '9', '9', '8', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '4', '7', '3', '8', '0', '4', '6', '3', '7', '2', '5', '3', '9', '1', '9', '1', '2', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '2', '2', '5', '9', '8', '0', '1', '5', '2', '9', '4', '2', '7', '9', '5', '6', '8', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '4', '5', '4', '5', '0', '5', '4', '6', '7', '4', '9', '1', '8', '0', '9', '9', '0', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '4', '2', '3', '8', '5', '7', '6', '9', '4', '3', '5', '6', '6', '7', '0', '5', '6', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '0', '2', '5', '8', '1', '4', '5', '3', '0', '4', '8', '6', '8', '8', '1', '3', '4', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '7', '6', '8', '7', '8', '1', '3', '9', '8', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '8', '0', '3', '6', '9', '6', '1', '3', '9', '3', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk035Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['3', '5'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['2', '2', '6', '9', '7', '5', '9', '9', '2', '0', '5', '3', '1', '6', '7', '9', '1', '2', '8', '9', '4']), .str (String.ofList ['2', '7', '1', '0', '5', '0', '0', '0', '1', '9', '9', '7', '8', '4', '7', '7', '3', '8', '7', '5', '5']), .str (String.ofList ['1', '5', '7', '9', '6', '8', '9', '4', '9', '2', '2', '0', '1', '4', '9', '4', '4', '7', '6', '8', '2']), .str (String.ofList ['2', '8', '7', '9', '5', '0', '0', '0', '0', '2', '1', '0', '0', '1', '7', '5', '9', '6', '2', '7', '6']), .str (String.ofList ['3', '6', '4', '5', '0', '8', '8', '8', '6', '5', '6', '1', '0', '3', '7', '5', '9', '9', '8', '3', '9']), .str (String.ofList ['3', '2', '4', '7', '3', '8', '0', '4', '6', '3', '7', '2', '5', '3', '9', '1', '9', '1', '2', '9', '5']), .str (String.ofList ['1', '4', '8', '2', '2', '5', '9', '8', '0', '1', '5', '2', '9', '4', '2', '7', '9', '5', '6', '8', '0', '7']), .str (String.ofList ['2', '7', '4', '5', '4', '5', '0', '5', '4', '6', '7', '4', '9', '1', '8', '0', '9', '9', '0', '5', '2']), .str (String.ofList ['3', '4', '4', '2', '3', '8', '5', '7', '6', '9', '4', '3', '5', '6', '6', '7', '0', '5', '6', '3', '7']), .str (String.ofList ['1', '7', '9', '0', '2', '5', '8', '1', '4', '5', '3', '0', '4', '8', '6', '8', '8', '1', '3', '4', '1'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '0', '7', '6', '8', '7', '8', '1', '3', '9', '8', '2', '6'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '0', '8', '0', '3', '6', '9', '6', '1', '3', '9', '3', '1']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_035_before_generic"
  err.flush

theorem array_moment_records_chunk_035 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 58)
      (SourceJson.white (momentRecordsChunk035Chars ++ tail)) acc =
      SourceJson.array (fuel + 57) (SourceJson.white tail) (momentRecordsChunk035Push acc) := by rfl

noncomputable def momentRecordsAcc036 : List SourceJson := momentRecordsChunk035Push momentRecordsAcc035

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_035_generic_complete"
  err.flush

noncomputable def momentRecordsBlock008Chars : List Char := momentRecordsChunk032Chars ++ momentRecordsChunk033Chars ++ momentRecordsChunk034Chars ++ momentRecordsChunk035Chars
noncomputable def momentRecordsBlock008Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk035Push (momentRecordsChunk034Push (momentRecordsChunk033Push (momentRecordsChunk032Push (acc))))

theorem array_moment_records_block_008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 61)
      (SourceJson.white (momentRecordsBlock008Chars ++ tail)) acc =
      SourceJson.array (fuel + 57) (SourceJson.white tail) (momentRecordsBlock008Push acc) := by
  have hinput : momentRecordsBlock008Chars ++ tail = momentRecordsChunk032Chars ++ (momentRecordsChunk033Chars ++ (momentRecordsChunk034Chars ++ (momentRecordsChunk035Chars ++ (tail)))) := by
    simp only [momentRecordsBlock008Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 61) (SourceJson.white (momentRecordsBlock008Chars ++ tail)) acc =
        SourceJson.array (fuel + 61) (SourceJson.white (momentRecordsChunk032Chars ++ (momentRecordsChunk033Chars ++ (momentRecordsChunk034Chars ++ (momentRecordsChunk035Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 61) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 60) (SourceJson.white (momentRecordsChunk033Chars ++ (momentRecordsChunk034Chars ++ (momentRecordsChunk035Chars ++ (tail))))) (momentRecordsChunk032Push (acc)) := array_moment_records_chunk_032 fuel (momentRecordsChunk033Chars ++ (momentRecordsChunk034Chars ++ (momentRecordsChunk035Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 59) (SourceJson.white (momentRecordsChunk034Chars ++ (momentRecordsChunk035Chars ++ (tail)))) (momentRecordsChunk033Push (momentRecordsChunk032Push (acc))) := array_moment_records_chunk_033 fuel (momentRecordsChunk034Chars ++ (momentRecordsChunk035Chars ++ (tail))) (momentRecordsChunk032Push (acc))
    _ = SourceJson.array (fuel + 58) (SourceJson.white (momentRecordsChunk035Chars ++ (tail))) (momentRecordsChunk034Push (momentRecordsChunk033Push (momentRecordsChunk032Push (acc)))) := array_moment_records_chunk_034 fuel (momentRecordsChunk035Chars ++ (tail)) (momentRecordsChunk033Push (momentRecordsChunk032Push (acc)))
    _ = SourceJson.array (fuel + 57) (SourceJson.white tail) (momentRecordsBlock008Push acc) := array_moment_records_chunk_035 fuel (tail) (momentRecordsChunk034Push (momentRecordsChunk033Push (momentRecordsChunk032Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_008_before_raw_binding"
  err.flush

theorem moment_records_block_008_prefix :
    (momentRest05 16723).take 2046 = momentRecordsBlock008Chars := by rfl

theorem moment_records_block_008_split :
    momentRest05 16723 = momentRecordsBlock008Chars ++ momentRest05 18769 := by
  calc
    momentRest05 16723 =
        (momentRest05 16723).take 2046 ++ (momentRest05 16723).drop 2046 :=
      (List.take_append_drop 2046 (momentRest05 16723)).symm
    _ = momentRecordsBlock008Chars ++ (momentRest05 16723).drop 2046 :=
      congrArg (fun p => p ++ (momentRest05 16723).drop 2046) moment_records_block_008_prefix
    _ = momentRecordsBlock008Chars ++ momentRest05 18769 :=
      congrArg (fun rest => momentRecordsBlock008Chars ++ rest) (momentRest05_drop 16723 2046)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_008_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_008 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 61)
      (SourceJson.white (momentRest05 16723)) acc =
      SourceJson.array (fuel + 57) (SourceJson.white (momentRest05 18769)) (momentRecordsBlock008Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 61) (SourceJson.white s) acc)
      moment_records_block_008_split).trans (array_moment_records_block_008 fuel (momentRest05 18769) acc)

theorem moment_records_through_block_008 (fuel : Nat) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRest05 364)) [] =
      SourceJson.array (fuel + 57) (SourceJson.white (momentRest05 18769)) momentRecordsAcc036 := by
  exact (moment_records_through_block_007 fuel).trans (array_moment_records_original_block_008 fuel momentRecordsAcc032)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_008_complete"
  err.flush

#print axioms array_moment_records_chunk_032
#print axioms array_moment_records_chunk_033
#print axioms array_moment_records_chunk_034
#print axioms array_moment_records_chunk_035
#print axioms array_moment_records_block_008
#print axioms moment_records_block_008_prefix
#print axioms moment_records_block_008_split
#print axioms array_moment_records_original_block_008
#print axioms moment_records_through_block_008

end ImbalancedChen.P2OriginalSaving19Moment05Parsing
