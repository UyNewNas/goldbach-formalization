import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock000

/-! Original moment records block 1. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk004Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '0', '3', '0', '6', '8', '6', '4', '7', '8', '8', '0', '4', '9', '0', '0', '4', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '3', '7', '6', '6', '2', '7', '3', '4', '3', '8', '1', '3', '5', '3', '8', '1', '1', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '9', '0', '0', '6', '6', '1', '4', '8', '4', '7', '8', '4', '3', '4', '3', '5', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '1', '9', '8', '3', '8', '2', '0', '5', '7', '8', '7', '1', '1', '7', '6', '6', '1', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '8', '3', '0', '4', '2', '7', '3', '8', '4', '1', '9', '8', '9', '7', '8', '4', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '4', '2', '9', '5', '0', '8', '1', '9', '5', '0', '8', '0', '1', '5', '6', '8', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '4', '4', '4', '7', '2', '8', '3', '6', '5', '4', '8', '2', '7', '7', '9', '8', '2', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '3', '5', '1', '8', '9', '3', '3', '3', '3', '0', '5', '4', '2', '9', '8', '2', '3', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '4', '1', '7', '5', '0', '4', '0', '5', '9', '6', '7', '5', '8', '0', '3', '7', '3', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '6', '3', '3', '9', '1', '1', '3', '0', '4', '7', '5', '1', '2', '6', '3', '1', '6', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '9', '0', '9', '5', '1', '9', '3', '3', '5', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '9', '7', '7', '4', '0', '1', '6', '9', '3', '5', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk004Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['4'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['1', '6', '3', '0', '3', '0', '6', '8', '6', '4', '7', '8', '8', '0', '4', '9', '0', '0', '4', '4', '9']), .str (String.ofList ['1', '7', '6', '3', '7', '6', '6', '2', '7', '3', '4', '3', '8', '1', '3', '5', '3', '8', '1', '1', '1']), .str (String.ofList ['7', '7', '9', '0', '0', '6', '6', '1', '4', '8', '4', '7', '8', '4', '3', '4', '3', '5', '7', '0']), .str (String.ofList ['3', '2', '1', '9', '8', '3', '8', '2', '0', '5', '7', '8', '7', '1', '1', '7', '6', '6', '1', '5', '0']), .str (String.ofList ['1', '7', '2', '8', '3', '0', '4', '2', '7', '3', '8', '4', '1', '9', '8', '9', '7', '8', '4', '9', '1']), .str (String.ofList ['1', '7', '9', '4', '2', '9', '5', '0', '8', '1', '9', '5', '0', '8', '0', '1', '5', '6', '8', '7', '6']), .str (String.ofList ['5', '6', '4', '4', '4', '7', '2', '8', '3', '6', '5', '4', '8', '2', '7', '7', '9', '8', '2', '7', '8']), .str (String.ofList ['5', '2', '3', '5', '1', '8', '9', '3', '3', '3', '3', '0', '5', '4', '2', '9', '8', '2', '3', '2', '1']), .str (String.ofList ['5', '7', '4', '1', '7', '5', '0', '4', '0', '5', '9', '6', '7', '5', '8', '0', '3', '7', '3', '4', '5']), .str (String.ofList ['5', '3', '6', '3', '3', '9', '1', '1', '3', '0', '4', '7', '5', '1', '2', '6', '3', '1', '6', '6', '4'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['2', '4', '9', '0', '9', '5', '1', '9', '3', '3', '5', '6', '5'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['2', '4', '9', '7', '7', '4', '0', '1', '6', '9', '3', '5', '1']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_004_before_generic"
  err.flush

theorem array_moment_records_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 89)
      (SourceJson.white (momentRecordsChunk004Chars ++ tail)) acc =
      SourceJson.array (fuel + 88) (SourceJson.white tail) (momentRecordsChunk004Push acc) := by rfl

noncomputable def momentRecordsAcc005 : List SourceJson := momentRecordsChunk004Push momentRecordsAcc004

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_004_generic_complete"
  err.flush

noncomputable def momentRecordsChunk005Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '2', '3', '3', '6', '8', '0', '4', '5', '0', '4', '2', '6', '1', '4', '1', '8', '2', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '5', '9', '0', '7', '8', '4', '2', '0', '7', '8', '1', '3', '7', '9', '5', '9', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '9', '0', '0', '6', '6', '1', '4', '8', '4', '7', '8', '4', '3', '4', '3', '5', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '3', '4', '2', '4', '3', '8', '9', '1', '5', '1', '6', '7', '1', '9', '3', '3', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '8', '3', '0', '4', '2', '7', '3', '8', '4', '1', '9', '8', '9', '7', '8', '4', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '4', '2', '9', '5', '0', '8', '1', '9', '5', '0', '8', '0', '1', '5', '6', '8', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '4', '4', '4', '7', '2', '8', '3', '6', '5', '4', '8', '2', '7', '7', '9', '8', '2', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '3', '5', '1', '8', '9', '3', '3', '3', '3', '0', '5', '4', '2', '9', '8', '2', '3', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '7', '6', '9', '7', '5', '6', '7', '4', '0', '8', '9', '5', '8', '9', '2', '7', '3', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '9', '8', '3', '0', '0', '8', '4', '1', '0', '1', '9', '8', '5', '0', '2', '4', '2', '3', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '6', '0', '1', '0', '4', '0', '0', '0', '2', '1', '8', '2', '9', '1', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '6', '0', '7', '4', '0', '5', '3', '8', '6', '6', '1', '3', '1', '6', '4', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk005Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['5'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['1', '5', '2', '3', '3', '6', '8', '0', '4', '5', '0', '4', '2', '6', '1', '4', '1', '8', '2', '3', '1']), .str (String.ofList ['1', '6', '1', '5', '9', '0', '7', '8', '4', '2', '0', '7', '8', '1', '3', '7', '9', '5', '9', '1', '9']), .str (String.ofList ['7', '7', '9', '0', '0', '6', '6', '1', '4', '8', '4', '7', '8', '4', '3', '4', '3', '5', '7', '0']), .str (String.ofList ['2', '7', '5', '3', '4', '2', '4', '3', '8', '9', '1', '5', '1', '6', '7', '1', '9', '3', '3', '7', '0']), .str (String.ofList ['1', '7', '2', '8', '3', '0', '4', '2', '7', '3', '8', '4', '1', '9', '8', '9', '7', '8', '4', '9', '1']), .str (String.ofList ['1', '7', '9', '4', '2', '9', '5', '0', '8', '1', '9', '5', '0', '8', '0', '1', '5', '6', '8', '7', '6']), .str (String.ofList ['5', '6', '4', '4', '4', '7', '2', '8', '3', '6', '5', '4', '8', '2', '7', '7', '9', '8', '2', '7', '8']), .str (String.ofList ['5', '2', '3', '5', '1', '8', '9', '3', '3', '3', '3', '0', '5', '4', '2', '9', '8', '2', '3', '2', '1']), .str (String.ofList ['4', '7', '7', '6', '9', '7', '5', '6', '7', '4', '0', '8', '9', '5', '8', '9', '2', '7', '3', '8', '1']), .str (String.ofList ['3', '6', '9', '8', '3', '0', '0', '8', '4', '1', '0', '1', '9', '8', '5', '0', '2', '4', '2', '3', '9'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['2', '6', '0', '1', '0', '4', '0', '0', '0', '2', '1', '8', '2', '9', '1', '3', '1'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['2', '6', '0', '7', '4', '0', '5', '3', '8', '6', '6', '1', '3', '1', '6', '4', '7']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_005_before_generic"
  err.flush

theorem array_moment_records_chunk_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 88)
      (SourceJson.white (momentRecordsChunk005Chars ++ tail)) acc =
      SourceJson.array (fuel + 87) (SourceJson.white tail) (momentRecordsChunk005Push acc) := by rfl

noncomputable def momentRecordsAcc006 : List SourceJson := momentRecordsChunk005Push momentRecordsAcc005

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_005_generic_complete"
  err.flush

noncomputable def momentRecordsChunk006Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '7', '7', '0', '6', '9', '9', '0', '9', '3', '2', '7', '4', '3', '8', '3', '7', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '1', '3', '0', '2', '0', '7', '4', '2', '1', '8', '0', '8', '5', '3', '1', '4', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '4', '3', '9', '9', '6', '2', '9', '3', '4', '7', '1', '2', '6', '4', '0', '0', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '4', '7', '7', '0', '0', '3', '7', '6', '2', '3', '0', '9', '0', '4', '8', '4', '9', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '8', '5', '8', '5', '8', '9', '2', '8', '6', '4', '8', '5', '2', '5', '7', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '7', '2', '0', '1', '2', '2', '2', '5', '4', '6', '6', '2', '4', '6', '2', '6', '5', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '0', '8', '7', '6', '9', '8', '4', '9', '6', '6', '2', '3', '8', '0', '3', '6', '3', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '2', '6', '5', '6', '3', '7', '6', '7', '0', '7', '2', '4', '5', '1', '2', '2', '6', '3', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '4', '0', '8', '1', '8', '1', '9', '7', '0', '3', '0', '8', '7', '1', '6', '4', '9', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '4', '1', '1', '6', '2', '4', '9', '9', '6', '8', '7', '9', '9', '1', '7', '5', '7', '5', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '1', '2', '6', '0', '3', '0', '1', '8', '0', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '1', '6', '8', '5', '2', '2', '6', '5', '3', '6', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk006Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['6'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['1', '3', '9', '7', '7', '0', '6', '9', '9', '0', '9', '3', '2', '7', '4', '3', '8', '3', '7', '2', '0']), .str (String.ofList ['1', '4', '4', '1', '3', '0', '2', '0', '7', '4', '2', '1', '8', '0', '8', '5', '3', '1', '4', '1', '5']), .str (String.ofList ['7', '8', '4', '3', '9', '9', '6', '2', '9', '3', '4', '7', '1', '2', '6', '4', '0', '0', '8', '3']), .str (String.ofList ['2', '7', '4', '7', '7', '0', '0', '3', '7', '6', '2', '3', '0', '9', '0', '4', '8', '4', '9', '0', '7']), .str (String.ofList ['1', '8', '6', '8', '5', '8', '5', '8', '9', '2', '8', '6', '4', '8', '5', '2', '5', '7', '0', '0', '0']), .str (String.ofList ['1', '7', '7', '2', '0', '1', '2', '2', '2', '5', '4', '6', '6', '2', '4', '6', '2', '6', '5', '5', '7']), .str (String.ofList ['5', '7', '0', '8', '7', '6', '9', '8', '4', '9', '6', '6', '2', '3', '8', '0', '3', '6', '3', '2', '7']), .str (String.ofList ['4', '6', '2', '6', '5', '6', '3', '7', '6', '7', '0', '7', '2', '4', '5', '1', '2', '2', '6', '3', '3']), .str (String.ofList ['3', '2', '4', '0', '8', '1', '8', '1', '9', '7', '0', '3', '0', '8', '7', '1', '6', '4', '9', '3', '9']), .str (String.ofList ['3', '2', '4', '1', '1', '6', '2', '4', '9', '9', '6', '8', '7', '9', '9', '1', '7', '5', '7', '5', '2'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '9', '1', '2', '6', '0', '3', '0', '1', '8', '0', '4', '3'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '9', '1', '6', '8', '5', '2', '2', '6', '5', '3', '6', '1']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_006_before_generic"
  err.flush

theorem array_moment_records_chunk_006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 87)
      (SourceJson.white (momentRecordsChunk006Chars ++ tail)) acc =
      SourceJson.array (fuel + 86) (SourceJson.white tail) (momentRecordsChunk006Push acc) := by rfl

noncomputable def momentRecordsAcc007 : List SourceJson := momentRecordsChunk006Push momentRecordsAcc006

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_006_generic_complete"
  err.flush

noncomputable def momentRecordsChunk007Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '8', '2', '2', '9', '2', '2', '2', '3', '7', '4', '6', '3', '8', '6', '8', '5', '3', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '4', '7', '6', '8', '7', '7', '9', '6', '0', '2', '8', '0', '4', '4', '9', '7', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '7', '3', '9', '7', '0', '7', '3', '6', '0', '3', '9', '6', '5', '7', '8', '5', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '4', '5', '5', '7', '8', '1', '8', '3', '2', '4', '8', '7', '0', '8', '2', '9', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '7', '3', '4', '3', '5', '9', '5', '1', '9', '3', '1', '9', '4', '5', '3', '9', '6', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '8', '1', '2', '1', '3', '8', '6', '4', '2', '7', '8', '8', '9', '2', '7', '1', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '1', '8', '6', '9', '4', '0', '6', '6', '7', '3', '2', '3', '1', '2', '9', '5', '2', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '0', '6', '8', '2', '9', '6', '2', '6', '8', '8', '9', '0', '8', '6', '9', '0', '5', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '8', '9', '3', '8', '6', '4', '0', '2', '0', '2', '5', '9', '2', '1', '1', '0', '9', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '0', '2', '1', '6', '1', '5', '1', '4', '3', '9', '2', '7', '0', '2', '3', '5', '5', '1', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '0', '5', '9', '9', '8', '1', '7', '8', '2', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '1', '4', '5', '4', '0', '8', '2', '5', '0', '3', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk007Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['7'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['3', '1', '8', '2', '2', '9', '2', '2', '2', '3', '7', '4', '6', '3', '8', '6', '8', '5', '3', '4', '5']), .str (String.ofList ['3', '4', '1', '4', '7', '6', '8', '7', '7', '9', '6', '0', '2', '8', '0', '4', '4', '9', '7', '6', '7']), .str (String.ofList ['1', '4', '2', '7', '3', '9', '7', '0', '7', '3', '6', '0', '3', '9', '6', '5', '7', '8', '5', '4', '1']), .str (String.ofList ['3', '7', '4', '4', '5', '5', '7', '8', '1', '8', '3', '2', '4', '8', '7', '0', '8', '2', '9', '6', '4']), .str (String.ofList ['3', '0', '7', '3', '4', '3', '5', '9', '5', '1', '9', '3', '1', '9', '4', '5', '3', '9', '6', '1', '0']), .str (String.ofList ['3', '2', '8', '8', '1', '2', '1', '3', '8', '6', '4', '2', '7', '8', '8', '9', '2', '7', '1', '2', '4']), .str (String.ofList ['1', '0', '9', '1', '8', '6', '9', '4', '0', '6', '6', '7', '3', '2', '3', '1', '2', '9', '5', '2', '5', '2']), .str (String.ofList ['5', '0', '0', '6', '8', '2', '9', '6', '2', '6', '8', '8', '9', '0', '8', '6', '9', '0', '5', '4', '5']), .str (String.ofList ['4', '9', '8', '9', '3', '8', '6', '4', '0', '2', '0', '2', '5', '9', '2', '1', '1', '0', '9', '2', '8']), .str (String.ofList ['3', '8', '0', '2', '1', '6', '1', '5', '1', '4', '3', '9', '2', '7', '0', '2', '3', '5', '5', '1', '8'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['2', '4', '0', '5', '9', '9', '8', '1', '7', '8', '2', '0', '1'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['2', '4', '1', '4', '5', '4', '0', '8', '2', '5', '0', '3', '8']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_007_before_generic"
  err.flush

theorem array_moment_records_chunk_007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 86)
      (SourceJson.white (momentRecordsChunk007Chars ++ tail)) acc =
      SourceJson.array (fuel + 85) (SourceJson.white tail) (momentRecordsChunk007Push acc) := by rfl

noncomputable def momentRecordsAcc008 : List SourceJson := momentRecordsChunk007Push momentRecordsAcc007

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_007_generic_complete"
  err.flush

noncomputable def momentRecordsBlock001Chars : List Char := momentRecordsChunk004Chars ++ momentRecordsChunk005Chars ++ momentRecordsChunk006Chars ++ momentRecordsChunk007Chars
noncomputable def momentRecordsBlock001Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk007Push (momentRecordsChunk006Push (momentRecordsChunk005Push (momentRecordsChunk004Push (acc))))

theorem array_moment_records_block_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 89)
      (SourceJson.white (momentRecordsBlock001Chars ++ tail)) acc =
      SourceJson.array (fuel + 85) (SourceJson.white tail) (momentRecordsBlock001Push acc) := by
  have hinput : momentRecordsBlock001Chars ++ tail = momentRecordsChunk004Chars ++ (momentRecordsChunk005Chars ++ (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail)))) := by
    simp only [momentRecordsBlock001Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 89) (SourceJson.white (momentRecordsBlock001Chars ++ tail)) acc =
        SourceJson.array (fuel + 89) (SourceJson.white (momentRecordsChunk004Chars ++ (momentRecordsChunk005Chars ++ (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 89) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 88) (SourceJson.white (momentRecordsChunk005Chars ++ (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail))))) (momentRecordsChunk004Push (acc)) := array_moment_records_chunk_004 fuel (momentRecordsChunk005Chars ++ (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 87) (SourceJson.white (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail)))) (momentRecordsChunk005Push (momentRecordsChunk004Push (acc))) := array_moment_records_chunk_005 fuel (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail))) (momentRecordsChunk004Push (acc))
    _ = SourceJson.array (fuel + 86) (SourceJson.white (momentRecordsChunk007Chars ++ (tail))) (momentRecordsChunk006Push (momentRecordsChunk005Push (momentRecordsChunk004Push (acc)))) := array_moment_records_chunk_006 fuel (momentRecordsChunk007Chars ++ (tail)) (momentRecordsChunk005Push (momentRecordsChunk004Push (acc)))
    _ = SourceJson.array (fuel + 85) (SourceJson.white tail) (momentRecordsBlock001Push acc) := array_moment_records_chunk_007 fuel (tail) (momentRecordsChunk006Push (momentRecordsChunk005Push (momentRecordsChunk004Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_001_before_raw_binding"
  err.flush

theorem moment_records_block_001_prefix :
    (momentRest05 2404).take 2034 = momentRecordsBlock001Chars := by rfl

theorem moment_records_block_001_split :
    momentRest05 2404 = momentRecordsBlock001Chars ++ momentRest05 4438 := by
  calc
    momentRest05 2404 =
        (momentRest05 2404).take 2034 ++ (momentRest05 2404).drop 2034 :=
      (List.take_append_drop 2034 (momentRest05 2404)).symm
    _ = momentRecordsBlock001Chars ++ (momentRest05 2404).drop 2034 :=
      congrArg (fun p => p ++ (momentRest05 2404).drop 2034) moment_records_block_001_prefix
    _ = momentRecordsBlock001Chars ++ momentRest05 4438 :=
      congrArg (fun rest => momentRecordsBlock001Chars ++ rest) (momentRest05_drop 2404 2034)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_001_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_001 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 89)
      (SourceJson.white (momentRest05 2404)) acc =
      SourceJson.array (fuel + 85) (SourceJson.white (momentRest05 4438)) (momentRecordsBlock001Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 89) (SourceJson.white s) acc)
      moment_records_block_001_split).trans (array_moment_records_block_001 fuel (momentRest05 4438) acc)

theorem moment_records_through_block_001 (fuel : Nat) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRest05 364)) [] =
      SourceJson.array (fuel + 85) (SourceJson.white (momentRest05 4438)) momentRecordsAcc008 := by
  exact (moment_records_through_block_000 fuel).trans (array_moment_records_original_block_001 fuel momentRecordsAcc004)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_001_complete"
  err.flush

#print axioms array_moment_records_chunk_004
#print axioms array_moment_records_chunk_005
#print axioms array_moment_records_chunk_006
#print axioms array_moment_records_chunk_007
#print axioms array_moment_records_block_001
#print axioms moment_records_block_001_prefix
#print axioms moment_records_block_001_split
#print axioms array_moment_records_original_block_001
#print axioms moment_records_through_block_001

end ImbalancedChen.P2OriginalSaving19Moment05Parsing
