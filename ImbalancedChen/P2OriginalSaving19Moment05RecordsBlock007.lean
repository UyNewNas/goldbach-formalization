import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock006

/-! Original moment records block 7. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk028Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '2', '6', '4', '3', '8', '6', '3', '5', '2', '2', '1', '5', '5', '9', '3', '2', '7', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '5', '1', '0', '2', '0', '9', '1', '5', '7', '0', '8', '3', '0', '4', '5', '2', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '1', '5', '9', '7', '9', '5', '4', '2', '7', '2', '3', '7', '0', '2', '9', '0', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '4', '0', '2', '8', '2', '8', '5', '7', '2', '2', '9', '7', '2', '2', '7', '9', '9', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '5', '4', '3', '1', '1', '0', '9', '7', '0', '7', '4', '6', '2', '4', '9', '6', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '1', '8', '2', '0', '5', '6', '9', '2', '4', '6', '9', '1', '8', '6', '7', '9', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '8', '1', '4', '7', '0', '6', '3', '3', '0', '6', '5', '3', '9', '7', '8', '4', '3', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '6', '6', '5', '1', '5', '6', '5', '8', '8', '1', '4', '8', '1', '0', '8', '3', '3', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '2', '4', '2', '3', '3', '0', '3', '7', '6', '2', '5', '3', '4', '9', '6', '6', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '6', '9', '4', '8', '3', '0', '4', '7', '4', '3', '5', '2', '3', '5', '7', '1', '5', '4', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '8', '7', '8', '6', '0', '4', '3', '5', '6', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '9', '0', '0', '1', '0', '5', '6', '5', '7', '3', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk028Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['2', '8'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['1', '8', '2', '6', '4', '3', '8', '6', '3', '5', '2', '2', '1', '5', '5', '9', '3', '2', '7', '2', '8']), .str (String.ofList ['2', '4', '0', '5', '1', '0', '2', '0', '9', '1', '5', '7', '0', '8', '3', '0', '4', '5', '2', '1', '9']), .str (String.ofList ['8', '2', '1', '5', '9', '7', '9', '5', '4', '2', '7', '2', '3', '7', '0', '2', '9', '0', '9', '3']), .str (String.ofList ['1', '0', '5', '4', '0', '2', '8', '2', '8', '5', '7', '2', '2', '9', '7', '2', '2', '7', '9', '9', '4']), .str (String.ofList ['2', '0', '6', '5', '4', '3', '1', '1', '0', '9', '7', '0', '7', '4', '6', '2', '4', '9', '6', '4', '5']), .str (String.ofList ['1', '2', '8', '1', '8', '2', '0', '5', '6', '9', '2', '4', '6', '9', '1', '8', '6', '7', '9', '7', '8']), .str (String.ofList ['7', '6', '8', '1', '4', '7', '0', '6', '3', '3', '0', '6', '5', '3', '9', '7', '8', '4', '3', '1', '0']), .str (String.ofList ['3', '4', '6', '6', '5', '1', '5', '6', '5', '8', '8', '1', '4', '8', '1', '0', '8', '3', '3', '1', '5']), .str (String.ofList ['3', '4', '1', '2', '4', '2', '3', '3', '0', '3', '7', '6', '2', '5', '3', '4', '9', '6', '6', '7', '0']), .str (String.ofList ['2', '2', '6', '9', '4', '8', '3', '0', '4', '7', '4', '3', '5', '2', '3', '5', '7', '1', '5', '4', '6'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['9', '8', '7', '8', '6', '0', '4', '3', '5', '6', '0', '4'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['9', '9', '0', '0', '1', '0', '5', '6', '5', '7', '3', '4']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_028_before_generic"
  err.flush

theorem array_moment_records_chunk_028 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 65)
      (SourceJson.white (momentRecordsChunk028Chars ++ tail)) acc =
      SourceJson.array (fuel + 64) (SourceJson.white tail) (momentRecordsChunk028Push acc) := by rfl

noncomputable def momentRecordsAcc029 : List SourceJson := momentRecordsChunk028Push momentRecordsAcc028

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_028_generic_complete"
  err.flush

noncomputable def momentRecordsChunk029Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '3', '3', '6', '5', '1', '9', '7', '9', '2', '5', '7', '2', '0', '2', '5', '5', '4', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '8', '8', '9', '0', '2', '6', '2', '9', '3', '3', '7', '0', '3', '2', '8', '9', '5', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '1', '5', '7', '5', '7', '2', '7', '8', '7', '1', '8', '7', '7', '8', '4', '7', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '7', '2', '1', '4', '4', '9', '9', '7', '9', '3', '5', '7', '2', '7', '9', '5', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '3', '0', '6', '9', '3', '8', '4', '2', '0', '8', '7', '4', '2', '0', '1', '8', '2', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '0', '6', '7', '6', '5', '0', '9', '6', '0', '0', '0', '0', '5', '7', '9', '0', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '2', '8', '1', '5', '4', '6', '1', '7', '8', '4', '6', '7', '2', '0', '3', '8', '1', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '1', '9', '7', '5', '1', '9', '8', '7', '9', '6', '2', '5', '2', '5', '1', '5', '8', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '5', '6', '9', '7', '6', '4', '5', '6', '6', '7', '1', '7', '1', '3', '8', '6', '5', '4', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '5', '0', '1', '4', '9', '3', '1', '8', '0', '2', '0', '7', '7', '5', '1', '5', '7', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '4', '6', '2', '2', '5', '0', '5', '8', '6', '3', '0', '1', '4', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '4', '7', '0', '4', '3', '1', '7', '1', '0', '6', '9', '9', '5', '2', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk029Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['2', '9'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['2', '3', '3', '3', '6', '5', '1', '9', '7', '9', '2', '5', '7', '2', '0', '2', '5', '5', '4', '6', '2']), .str (String.ofList ['3', '0', '8', '8', '9', '0', '2', '6', '2', '9', '3', '3', '7', '0', '3', '2', '8', '9', '5', '5', '3']), .str (String.ofList ['1', '1', '6', '1', '5', '7', '5', '7', '2', '7', '8', '7', '1', '8', '7', '7', '8', '4', '7', '5', '7']), .str (String.ofList ['1', '5', '8', '7', '2', '1', '4', '4', '9', '9', '7', '9', '3', '5', '7', '2', '7', '9', '5', '6', '3']), .str (String.ofList ['2', '9', '3', '0', '6', '9', '3', '8', '4', '2', '0', '8', '7', '4', '2', '0', '1', '8', '2', '4', '5']), .str (String.ofList ['1', '7', '2', '0', '6', '7', '6', '5', '0', '9', '6', '0', '0', '0', '0', '5', '7', '9', '0', '5', '3']), .str (String.ofList ['6', '9', '2', '8', '1', '5', '4', '6', '1', '7', '8', '4', '6', '7', '2', '0', '3', '8', '1', '4', '1']), .str (String.ofList ['3', '1', '1', '9', '7', '5', '1', '9', '8', '7', '9', '6', '2', '5', '2', '5', '1', '5', '8', '6', '7']), .str (String.ofList ['3', '2', '5', '6', '9', '7', '6', '4', '5', '6', '6', '7', '1', '7', '1', '3', '8', '6', '5', '4', '7']), .str (String.ofList ['2', '4', '0', '5', '0', '1', '4', '9', '3', '1', '8', '0', '2', '0', '7', '7', '5', '1', '5', '7', '6'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['3', '4', '6', '2', '2', '5', '0', '5', '8', '6', '3', '0', '1', '4', '6', '9'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['3', '4', '7', '0', '4', '3', '1', '7', '1', '0', '6', '9', '9', '5', '2', '6']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_029_before_generic"
  err.flush

theorem array_moment_records_chunk_029 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 64)
      (SourceJson.white (momentRecordsChunk029Chars ++ tail)) acc =
      SourceJson.array (fuel + 63) (SourceJson.white tail) (momentRecordsChunk029Push acc) := by rfl

noncomputable def momentRecordsAcc030 : List SourceJson := momentRecordsChunk029Push momentRecordsAcc029

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_029_generic_complete"
  err.flush

noncomputable def momentRecordsChunk030Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '8', '8', '9', '1', '8', '6', '7', '5', '9', '8', '8', '2', '8', '0', '4', '4', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '3', '6', '9', '4', '1', '0', '7', '6', '6', '9', '4', '1', '6', '3', '6', '4', '0', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '4', '3', '7', '5', '2', '3', '3', '1', '2', '7', '8', '0', '8', '7', '8', '5', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '5', '2', '4', '5', '4', '3', '2', '4', '7', '9', '2', '8', '3', '7', '4', '0', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '0', '4', '5', '2', '1', '3', '7', '5', '7', '2', '9', '3', '8', '2', '5', '8', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '2', '6', '2', '5', '1', '8', '4', '0', '0', '3', '0', '6', '0', '2', '4', '2', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '3', '5', '9', '5', '9', '4', '4', '2', '4', '7', '3', '9', '9', '7', '5', '9', '9', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '7', '4', '1', '3', '9', '7', '2', '0', '8', '8', '7', '7', '6', '7', '0', '9', '1', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '6', '7', '6', '1', '4', '8', '5', '9', '2', '3', '4', '5', '3', '1', '7', '0', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '5', '2', '7', '8', '3', '8', '1', '4', '6', '2', '2', '0', '0', '7', '0', '8', '9', '4', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '9', '0', '0', '7', '9', '9', '3', '3', '9', '7', '1', '4', '0', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '9', '0', '6', '0', '6', '8', '1', '5', '1', '1', '0', '2', '3', '2', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk030Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['3', '0'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['1', '6', '1', '8', '8', '9', '1', '8', '6', '7', '5', '9', '8', '8', '2', '8', '0', '4', '4', '4', '3']), .str (String.ofList ['2', '1', '3', '6', '9', '4', '1', '0', '7', '6', '6', '9', '4', '1', '6', '3', '6', '4', '0', '3', '5']), .str (String.ofList ['7', '7', '4', '3', '7', '5', '2', '3', '3', '1', '2', '7', '8', '0', '8', '7', '8', '5', '5', '1']), .str (String.ofList ['9', '7', '5', '2', '4', '5', '4', '3', '2', '4', '7', '9', '2', '8', '3', '7', '4', '0', '2', '4']), .str (String.ofList ['1', '8', '1', '0', '4', '5', '2', '1', '3', '7', '5', '7', '2', '9', '3', '8', '2', '5', '8', '9', '5']), .str (String.ofList ['1', '1', '8', '2', '6', '2', '5', '1', '8', '4', '0', '0', '3', '0', '6', '0', '2', '4', '2', '3', '5']), .str (String.ofList ['6', '1', '3', '5', '9', '5', '9', '4', '4', '2', '4', '7', '3', '9', '9', '7', '5', '9', '9', '8', '1']), .str (String.ofList ['2', '5', '7', '4', '1', '3', '9', '7', '2', '0', '8', '8', '7', '7', '6', '7', '0', '9', '1', '6', '9']), .str (String.ofList ['2', '8', '7', '6', '7', '6', '1', '4', '8', '5', '9', '2', '3', '4', '5', '3', '1', '7', '0', '2', '7']), .str (String.ofList ['1', '8', '5', '2', '7', '8', '3', '8', '1', '4', '6', '2', '2', '0', '0', '7', '0', '8', '9', '4', '5'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['2', '9', '0', '0', '7', '9', '9', '3', '3', '9', '7', '1', '4', '0', '0', '8'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['2', '9', '0', '6', '0', '6', '8', '1', '5', '1', '1', '0', '2', '3', '2', '5']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_030_before_generic"
  err.flush

theorem array_moment_records_chunk_030 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 63)
      (SourceJson.white (momentRecordsChunk030Chars ++ tail)) acc =
      SourceJson.array (fuel + 62) (SourceJson.white tail) (momentRecordsChunk030Push acc) := by rfl

noncomputable def momentRecordsAcc031 : List SourceJson := momentRecordsChunk030Push momentRecordsAcc030

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_030_generic_complete"
  err.flush

noncomputable def momentRecordsChunk031Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '0', '8', '8', '5', '3', '2', '8', '5', '0', '7', '4', '8', '0', '2', '5', '0', '7', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '7', '8', '7', '6', '3', '2', '5', '2', '2', '8', '2', '0', '7', '4', '9', '4', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '8', '4', '1', '7', '3', '3', '1', '6', '9', '8', '1', '7', '9', '4', '9', '0', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '9', '6', '5', '5', '4', '1', '4', '7', '0', '8', '1', '7', '3', '8', '8', '6', '5', '1', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '4', '4', '4', '1', '4', '2', '9', '0', '3', '6', '4', '3', '1', '8', '1', '0', '1', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '9', '6', '1', '7', '0', '4', '5', '9', '8', '4', '4', '7', '8', '7', '6', '7', '9', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '5', '0', '8', '8', '1', '3', '0', '1', '9', '7', '8', '3', '3', '2', '0', '0', '6', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '7', '7', '1', '3', '3', '5', '7', '7', '4', '0', '0', '6', '9', '5', '3', '6', '4', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '5', '4', '5', '3', '2', '2', '6', '8', '5', '8', '0', '8', '1', '9', '1', '3', '0', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '6', '5', '7', '3', '2', '9', '4', '2', '3', '2', '0', '5', '6', '8', '9', '4', '7', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '6', '7', '3', '0', '9', '7', '7', '7', '6', '4', '9', '6', '2', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '6', '8', '7', '3', '3', '3', '3', '8', '7', '3', '9', '7', '4', '6', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk031Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['3', '1'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['2', '3', '0', '8', '8', '5', '3', '2', '8', '5', '0', '7', '4', '8', '0', '2', '5', '0', '7', '0', '7']), .str (String.ofList ['2', '7', '6', '7', '8', '7', '6', '3', '2', '5', '2', '2', '8', '2', '0', '7', '4', '9', '4', '7', '4']), .str (String.ofList ['1', '5', '6', '8', '4', '1', '7', '3', '3', '1', '6', '9', '8', '1', '7', '9', '4', '9', '0', '7', '8']), .str (String.ofList ['2', '8', '9', '6', '5', '5', '4', '1', '4', '7', '0', '8', '1', '7', '3', '8', '8', '6', '5', '1', '1']), .str (String.ofList ['3', '4', '4', '4', '4', '1', '4', '2', '9', '0', '3', '6', '4', '3', '1', '8', '1', '0', '1', '3', '5']), .str (String.ofList ['3', '3', '9', '6', '1', '7', '0', '4', '5', '9', '8', '4', '4', '7', '8', '7', '6', '7', '9', '1', '5']), .str (String.ofList ['1', '2', '4', '5', '0', '8', '8', '1', '3', '0', '1', '9', '7', '8', '3', '3', '2', '0', '0', '6', '1', '0']), .str (String.ofList ['2', '3', '7', '7', '1', '3', '3', '5', '7', '7', '4', '0', '0', '6', '9', '5', '3', '6', '4', '9', '3']), .str (String.ofList ['3', '6', '5', '4', '5', '3', '2', '2', '6', '8', '5', '8', '0', '8', '1', '9', '1', '3', '0', '1', '2']), .str (String.ofList ['1', '9', '0', '6', '5', '7', '3', '2', '9', '4', '2', '3', '2', '0', '5', '6', '8', '9', '4', '7', '7'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['4', '6', '7', '3', '0', '9', '7', '7', '7', '6', '4', '9', '6', '2', '8', '4'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['4', '6', '8', '7', '3', '3', '3', '3', '8', '7', '3', '9', '7', '4', '6', '9']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_031_before_generic"
  err.flush

theorem array_moment_records_chunk_031 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 62)
      (SourceJson.white (momentRecordsChunk031Chars ++ tail)) acc =
      SourceJson.array (fuel + 61) (SourceJson.white tail) (momentRecordsChunk031Push acc) := by rfl

noncomputable def momentRecordsAcc032 : List SourceJson := momentRecordsChunk031Push momentRecordsAcc031

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_031_generic_complete"
  err.flush

noncomputable def momentRecordsBlock007Chars : List Char := momentRecordsChunk028Chars ++ momentRecordsChunk029Chars ++ momentRecordsChunk030Chars ++ momentRecordsChunk031Chars
noncomputable def momentRecordsBlock007Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk031Push (momentRecordsChunk030Push (momentRecordsChunk029Push (momentRecordsChunk028Push (acc))))

theorem array_moment_records_block_007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 65)
      (SourceJson.white (momentRecordsBlock007Chars ++ tail)) acc =
      SourceJson.array (fuel + 61) (SourceJson.white tail) (momentRecordsBlock007Push acc) := by
  have hinput : momentRecordsBlock007Chars ++ tail = momentRecordsChunk028Chars ++ (momentRecordsChunk029Chars ++ (momentRecordsChunk030Chars ++ (momentRecordsChunk031Chars ++ (tail)))) := by
    simp only [momentRecordsBlock007Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 65) (SourceJson.white (momentRecordsBlock007Chars ++ tail)) acc =
        SourceJson.array (fuel + 65) (SourceJson.white (momentRecordsChunk028Chars ++ (momentRecordsChunk029Chars ++ (momentRecordsChunk030Chars ++ (momentRecordsChunk031Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 65) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 64) (SourceJson.white (momentRecordsChunk029Chars ++ (momentRecordsChunk030Chars ++ (momentRecordsChunk031Chars ++ (tail))))) (momentRecordsChunk028Push (acc)) := array_moment_records_chunk_028 fuel (momentRecordsChunk029Chars ++ (momentRecordsChunk030Chars ++ (momentRecordsChunk031Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 63) (SourceJson.white (momentRecordsChunk030Chars ++ (momentRecordsChunk031Chars ++ (tail)))) (momentRecordsChunk029Push (momentRecordsChunk028Push (acc))) := array_moment_records_chunk_029 fuel (momentRecordsChunk030Chars ++ (momentRecordsChunk031Chars ++ (tail))) (momentRecordsChunk028Push (acc))
    _ = SourceJson.array (fuel + 62) (SourceJson.white (momentRecordsChunk031Chars ++ (tail))) (momentRecordsChunk030Push (momentRecordsChunk029Push (momentRecordsChunk028Push (acc)))) := array_moment_records_chunk_030 fuel (momentRecordsChunk031Chars ++ (tail)) (momentRecordsChunk029Push (momentRecordsChunk028Push (acc)))
    _ = SourceJson.array (fuel + 61) (SourceJson.white tail) (momentRecordsBlock007Push acc) := array_moment_records_chunk_031 fuel (tail) (momentRecordsChunk030Push (momentRecordsChunk029Push (momentRecordsChunk028Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_007_before_raw_binding"
  err.flush

theorem moment_records_block_007_prefix :
    (momentRest05 14677).take 2046 = momentRecordsBlock007Chars := by rfl

theorem moment_records_block_007_split :
    momentRest05 14677 = momentRecordsBlock007Chars ++ momentRest05 16723 := by
  calc
    momentRest05 14677 =
        (momentRest05 14677).take 2046 ++ (momentRest05 14677).drop 2046 :=
      (List.take_append_drop 2046 (momentRest05 14677)).symm
    _ = momentRecordsBlock007Chars ++ (momentRest05 14677).drop 2046 :=
      congrArg (fun p => p ++ (momentRest05 14677).drop 2046) moment_records_block_007_prefix
    _ = momentRecordsBlock007Chars ++ momentRest05 16723 :=
      congrArg (fun rest => momentRecordsBlock007Chars ++ rest) (momentRest05_drop 14677 2046)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_007_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_007 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 65)
      (SourceJson.white (momentRest05 14677)) acc =
      SourceJson.array (fuel + 61) (SourceJson.white (momentRest05 16723)) (momentRecordsBlock007Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 65) (SourceJson.white s) acc)
      moment_records_block_007_split).trans (array_moment_records_block_007 fuel (momentRest05 16723) acc)

theorem moment_records_through_block_007 (fuel : Nat) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRest05 364)) [] =
      SourceJson.array (fuel + 61) (SourceJson.white (momentRest05 16723)) momentRecordsAcc032 := by
  exact (moment_records_through_block_006 fuel).trans (array_moment_records_original_block_007 fuel momentRecordsAcc028)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_007_complete"
  err.flush

#print axioms array_moment_records_chunk_028
#print axioms array_moment_records_chunk_029
#print axioms array_moment_records_chunk_030
#print axioms array_moment_records_chunk_031
#print axioms array_moment_records_block_007
#print axioms moment_records_block_007_prefix
#print axioms moment_records_block_007_split
#print axioms array_moment_records_original_block_007
#print axioms moment_records_through_block_007

end ImbalancedChen.P2OriginalSaving19Moment05Parsing
