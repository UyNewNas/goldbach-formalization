import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock010

/-! Original moment records block 11. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk044Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '9', '9', '7', '8', '2', '8', '3', '1', '5', '8', '8', '0', '4', '0', '3', '6', '6', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '2', '3', '0', '8', '9', '1', '3', '4', '7', '3', '0', '3', '7', '7', '5', '4', '6', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '9', '8', '4', '9', '0', '4', '9', '1', '2', '6', '5', '7', '7', '3', '3', '8', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '0', '1', '2', '2', '6', '2', '9', '7', '9', '4', '1', '9', '0', '4', '0', '6', '7', '6', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '1', '6', '3', '9', '2', '1', '8', '7', '5', '7', '0', '2', '2', '9', '6', '5', '2', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '9', '3', '7', '9', '9', '5', '4', '0', '5', '5', '7', '6', '4', '6', '2', '2', '9', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '6', '7', '6', '6', '9', '7', '1', '8', '9', '5', '8', '4', '7', '6', '3', '9', '5', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '8', '9', '7', '9', '1', '5', '4', '7', '2', '8', '2', '8', '4', '3', '9', '4', '6', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '9', '0', '2', '6', '1', '7', '4', '6', '3', '1', '2', '6', '7', '9', '0', '0', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '9', '2', '3', '2', '0', '4', '6', '4', '6', '7', '0', '1', '8', '0', '2', '0', '2', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '3', '1', '9', '2', '9', '8', '8', '3', '7', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '3', '6', '6', '8', '0', '2', '3', '6', '4', '6', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk044Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['4', '4'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['5', '1', '9', '9', '7', '8', '2', '8', '3', '1', '5', '8', '8', '0', '4', '0', '3', '6', '6', '9', '0']), .str (String.ofList ['5', '5', '2', '3', '0', '8', '9', '1', '3', '4', '7', '3', '0', '3', '7', '7', '5', '4', '6', '8', '3']), .str (String.ofList ['1', '8', '6', '9', '8', '4', '9', '0', '4', '9', '1', '2', '6', '5', '7', '7', '3', '3', '8', '8', '8']), .str (String.ofList ['4', '0', '0', '1', '2', '2', '6', '2', '9', '7', '9', '4', '1', '9', '0', '4', '0', '6', '7', '6', '8']), .str (String.ofList ['4', '3', '1', '6', '3', '9', '2', '1', '8', '7', '5', '7', '0', '2', '2', '9', '6', '5', '2', '2', '7']), .str (String.ofList ['4', '1', '9', '3', '7', '9', '9', '5', '4', '0', '5', '5', '7', '6', '4', '6', '2', '2', '9', '7', '5']), .str (String.ofList ['1', '0', '2', '6', '7', '6', '6', '9', '7', '1', '8', '9', '5', '8', '4', '7', '6', '3', '9', '5', '7', '3']), .str (String.ofList ['3', '5', '8', '9', '7', '9', '1', '5', '4', '7', '2', '8', '2', '8', '4', '3', '9', '4', '6', '3', '7']), .str (String.ofList ['2', '0', '3', '9', '0', '2', '6', '1', '7', '4', '6', '3', '1', '2', '6', '7', '9', '0', '0', '6', '1']), .str (String.ofList ['2', '0', '3', '9', '2', '3', '2', '0', '4', '6', '4', '6', '7', '0', '1', '8', '0', '2', '0', '2', '7'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '3', '3', '1', '9', '2', '9', '8', '8', '3', '7', '6', '7'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '3', '3', '6', '6', '8', '0', '2', '3', '6', '4', '6', '2']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_044_before_generic"
  err.flush

theorem array_moment_records_chunk_044 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 49)
      (SourceJson.white (momentRecordsChunk044Chars ++ tail)) acc =
      SourceJson.array (fuel + 48) (SourceJson.white tail) (momentRecordsChunk044Push acc) := by rfl

noncomputable def momentRecordsAcc045 : List SourceJson := momentRecordsChunk044Push momentRecordsAcc044

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_044_generic_complete"
  err.flush

noncomputable def momentRecordsChunk045Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '0', '9', '3', '5', '0', '0', '2', '8', '6', '6', '0', '8', '8', '5', '5', '5', '7', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '1', '1', '3', '5', '0', '2', '0', '1', '3', '8', '0', '6', '9', '3', '1', '7', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '8', '2', '1', '7', '0', '8', '0', '2', '9', '8', '4', '3', '7', '9', '7', '4', '1', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '1', '6', '5', '4', '8', '8', '3', '1', '7', '7', '2', '3', '1', '8', '9', '3', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '0', '4', '3', '8', '6', '0', '0', '6', '9', '7', '7', '1', '5', '9', '7', '6', '0', '8', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '4', '4', '3', '3', '9', '1', '9', '4', '2', '3', '8', '9', '4', '4', '2', '4', '3', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '2', '4', '0', '6', '2', '7', '4', '9', '1', '6', '9', '7', '1', '8', '1', '1', '1', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '0', '9', '1', '5', '6', '4', '1', '4', '7', '6', '5', '3', '2', '6', '2', '2', '5', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '8', '0', '8', '7', '6', '3', '7', '6', '3', '8', '1', '8', '1', '1', '0', '2', '6', '9', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '8', '1', '0', '4', '7', '6', '4', '3', '6', '1', '2', '5', '6', '5', '1', '8', '5', '9', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '8', '3', '7', '0', '6', '2', '6', '5', '3', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '8', '8', '1', '2', '8', '2', '8', '4', '3', '5', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk045Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['4', '5'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['5', '0', '0', '9', '3', '5', '0', '0', '2', '8', '6', '6', '0', '8', '8', '5', '5', '5', '7', '1', '7']), .str (String.ofList ['5', '3', '9', '1', '1', '3', '5', '0', '2', '0', '1', '3', '8', '0', '6', '9', '3', '1', '7', '4', '3']), .str (String.ofList ['1', '8', '8', '2', '1', '7', '0', '8', '0', '2', '9', '8', '4', '3', '7', '9', '7', '4', '1', '6', '9']), .str (String.ofList ['3', '9', '5', '1', '6', '5', '4', '8', '8', '3', '1', '7', '7', '2', '3', '1', '8', '9', '3', '3', '0']), .str (String.ofList ['4', '2', '0', '4', '3', '8', '6', '0', '0', '6', '9', '7', '7', '1', '5', '9', '7', '6', '0', '8', '9']), .str (String.ofList ['4', '1', '4', '4', '3', '3', '9', '1', '9', '4', '2', '3', '8', '9', '4', '4', '2', '4', '3', '0', '1']), .str (String.ofList ['1', '3', '2', '2', '4', '0', '6', '2', '7', '4', '9', '1', '6', '9', '7', '1', '8', '1', '1', '1', '7', '1']), .str (String.ofList ['2', '7', '0', '9', '1', '5', '6', '4', '1', '4', '7', '6', '5', '3', '2', '6', '2', '2', '5', '3', '4']), .str (String.ofList ['2', '2', '8', '0', '8', '7', '6', '3', '7', '6', '3', '8', '1', '8', '1', '1', '0', '2', '6', '9', '9']), .str (String.ofList ['2', '2', '8', '1', '0', '4', '7', '6', '4', '3', '6', '1', '2', '5', '6', '5', '1', '8', '5', '9', '6'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '1', '8', '3', '7', '0', '6', '2', '6', '5', '3', '6', '5'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '1', '8', '8', '1', '2', '8', '2', '8', '4', '3', '5', '2']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_045_before_generic"
  err.flush

theorem array_moment_records_chunk_045 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 48)
      (SourceJson.white (momentRecordsChunk045Chars ++ tail)) acc =
      SourceJson.array (fuel + 47) (SourceJson.white tail) (momentRecordsChunk045Push acc) := by rfl

noncomputable def momentRecordsAcc046 : List SourceJson := momentRecordsChunk045Push momentRecordsAcc045

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_045_generic_complete"
  err.flush

noncomputable def momentRecordsChunk046Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '5', '0', '8', '0', '6', '5', '7', '2', '3', '3', '0', '7', '5', '4', '9', '2', '5', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '7', '2', '1', '9', '8', '6', '1', '9', '6', '4', '9', '8', '1', '4', '6', '3', '6', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '4', '6', '5', '0', '1', '2', '9', '3', '9', '4', '2', '5', '0', '5', '8', '5', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '7', '0', '7', '0', '3', '4', '3', '9', '8', '0', '4', '7', '5', '5', '0', '9', '1', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '5', '9', '0', '6', '4', '5', '8', '4', '1', '6', '8', '6', '0', '1', '8', '8', '4', '6', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '2', '1', '7', '4', '3', '1', '2', '1', '8', '5', '6', '1', '7', '1', '8', '3', '7', '5', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '9', '6', '3', '8', '6', '6', '8', '0', '4', '9', '3', '2', '9', '8', '4', '2', '6', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '9', '4', '0', '1', '2', '9', '0', '5', '0', '2', '9', '6', '6', '7', '3', '9', '2', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '8', '6', '4', '7', '7', '1', '0', '1', '4', '0', '7', '3', '8', '6', '8', '5', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '8', '7', '3', '5', '3', '1', '9', '3', '1', '6', '7', '1', '7', '4', '3', '0', '2', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '6', '0', '4', '1', '7', '5', '1', '3', '8', '4', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '6', '3', '2', '7', '5', '3', '2', '0', '4', '3', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk046Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['4', '6'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['3', '7', '5', '0', '8', '0', '6', '5', '7', '2', '3', '3', '0', '7', '5', '4', '9', '2', '5', '8', '2']), .str (String.ofList ['4', '2', '7', '2', '1', '9', '8', '6', '1', '9', '6', '4', '9', '8', '1', '4', '6', '3', '6', '1', '5']), .str (String.ofList ['1', '6', '8', '4', '6', '5', '0', '1', '2', '9', '3', '9', '4', '2', '5', '0', '5', '8', '5', '3', '9']), .str (String.ofList ['3', '0', '7', '0', '7', '0', '3', '4', '3', '9', '8', '0', '4', '7', '5', '5', '0', '9', '1', '6', '5']), .str (String.ofList ['3', '7', '5', '9', '0', '6', '4', '5', '8', '4', '1', '6', '8', '6', '0', '1', '8', '8', '4', '6', '6']), .str (String.ofList ['3', '6', '2', '1', '7', '4', '3', '1', '2', '1', '8', '5', '6', '1', '7', '1', '8', '3', '7', '5', '8']), .str (String.ofList ['1', '3', '1', '9', '6', '3', '8', '6', '6', '8', '0', '4', '9', '3', '2', '9', '8', '4', '2', '6', '8', '2']), .str (String.ofList ['2', '5', '9', '4', '0', '1', '2', '9', '0', '5', '0', '2', '9', '6', '6', '7', '3', '9', '2', '7', '3']), .str (String.ofList ['2', '0', '6', '8', '6', '4', '7', '7', '1', '0', '1', '4', '0', '7', '3', '8', '6', '8', '5', '6', '7']), .str (String.ofList ['2', '0', '6', '8', '7', '3', '5', '3', '1', '9', '3', '1', '6', '7', '1', '7', '4', '3', '0', '2', '0'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['8', '6', '0', '4', '1', '7', '5', '1', '3', '8', '4', '4'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['8', '6', '3', '2', '7', '5', '3', '2', '0', '4', '3', '3']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_046_before_generic"
  err.flush

theorem array_moment_records_chunk_046 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 47)
      (SourceJson.white (momentRecordsChunk046Chars ++ tail)) acc =
      SourceJson.array (fuel + 46) (SourceJson.white tail) (momentRecordsChunk046Push acc) := by rfl

noncomputable def momentRecordsAcc047 : List SourceJson := momentRecordsChunk046Push momentRecordsAcc046

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_046_generic_complete"
  err.flush

noncomputable def momentRecordsChunk047Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '8', '7', '3', '1', '4', '4', '8', '3', '6', '8', '5', '9', '9', '2', '0', '9', '9', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '4', '4', '6', '3', '6', '0', '2', '3', '3', '8', '7', '1', '1', '2', '9', '6', '6', '6', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '6', '8', '0', '2', '7', '8', '0', '4', '2', '7', '3', '0', '1', '5', '4', '7', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '6', '8', '9', '4', '3', '1', '8', '9', '5', '0', '2', '4', '2', '1', '8', '3', '5', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '1', '2', '0', '6', '0', '0', '4', '5', '8', '6', '6', '3', '4', '1', '6', '0', '4', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '5', '2', '1', '5', '9', '3', '6', '0', '9', '3', '5', '4', '1', '4', '2', '5', '0', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '8', '8', '4', '8', '5', '4', '7', '7', '9', '0', '9', '5', '5', '7', '2', '7', '4', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '6', '0', '2', '8', '5', '4', '3', '1', '2', '7', '6', '7', '2', '5', '9', '9', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '1', '6', '0', '7', '2', '9', '9', '9', '6', '6', '7', '5', '2', '2', '7', '0', '3', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '1', '6', '0', '8', '0', '1', '1', '7', '7', '3', '9', '7', '7', '6', '5', '6', '6', '5', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '8', '2', '1', '3', '8', '3', '9', '2', '9', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '8', '4', '6', '7', '3', '9', '9', '4', '9', '9', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk047Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['4', '7'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['3', '1', '8', '7', '3', '1', '4', '4', '8', '3', '6', '8', '5', '9', '9', '2', '0', '9', '9', '4', '3']), .str (String.ofList ['3', '8', '4', '4', '6', '3', '6', '0', '2', '3', '3', '8', '7', '1', '1', '2', '9', '6', '6', '6', '6']), .str (String.ofList ['1', '4', '6', '6', '8', '0', '2', '7', '8', '0', '4', '2', '7', '3', '0', '1', '5', '4', '7', '2', '2']), .str (String.ofList ['2', '3', '6', '8', '9', '4', '3', '1', '8', '9', '5', '0', '2', '4', '2', '1', '8', '3', '5', '8', '0']), .str (String.ofList ['3', '1', '1', '2', '0', '6', '0', '0', '4', '5', '8', '6', '6', '3', '4', '1', '6', '0', '4', '5', '5']), .str (String.ofList ['3', '2', '5', '2', '1', '5', '9', '3', '6', '0', '9', '3', '5', '4', '1', '4', '2', '5', '0', '1', '3']), .str (String.ofList ['1', '3', '9', '8', '8', '4', '8', '5', '4', '7', '7', '9', '0', '9', '5', '5', '7', '2', '7', '4', '4', '2']), .str (String.ofList ['2', '8', '7', '6', '0', '2', '8', '5', '4', '3', '1', '2', '7', '6', '7', '2', '5', '9', '9', '8', '0']), .str (String.ofList ['2', '5', '1', '6', '0', '7', '2', '9', '9', '9', '6', '6', '7', '5', '2', '2', '7', '0', '3', '4', '5']), .str (String.ofList ['2', '5', '1', '6', '0', '8', '0', '1', '1', '7', '7', '3', '9', '7', '7', '6', '5', '6', '6', '5', '2'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['7', '8', '2', '1', '3', '8', '3', '9', '2', '9', '7', '3'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['7', '8', '4', '6', '7', '3', '9', '9', '4', '9', '9', '2']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_047_before_generic"
  err.flush

theorem array_moment_records_chunk_047 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 46)
      (SourceJson.white (momentRecordsChunk047Chars ++ tail)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white tail) (momentRecordsChunk047Push acc) := by rfl

noncomputable def momentRecordsAcc048 : List SourceJson := momentRecordsChunk047Push momentRecordsAcc047

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_047_generic_complete"
  err.flush

noncomputable def momentRecordsBlock011Chars : List Char := momentRecordsChunk044Chars ++ momentRecordsChunk045Chars ++ momentRecordsChunk046Chars ++ momentRecordsChunk047Chars
noncomputable def momentRecordsBlock011Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk047Push (momentRecordsChunk046Push (momentRecordsChunk045Push (momentRecordsChunk044Push (acc))))

theorem array_moment_records_block_011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 49)
      (SourceJson.white (momentRecordsBlock011Chars ++ tail)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white tail) (momentRecordsBlock011Push acc) := by
  have hinput : momentRecordsBlock011Chars ++ tail = momentRecordsChunk044Chars ++ (momentRecordsChunk045Chars ++ (momentRecordsChunk046Chars ++ (momentRecordsChunk047Chars ++ (tail)))) := by
    simp only [momentRecordsBlock011Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 49) (SourceJson.white (momentRecordsBlock011Chars ++ tail)) acc =
        SourceJson.array (fuel + 49) (SourceJson.white (momentRecordsChunk044Chars ++ (momentRecordsChunk045Chars ++ (momentRecordsChunk046Chars ++ (momentRecordsChunk047Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 49) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 48) (SourceJson.white (momentRecordsChunk045Chars ++ (momentRecordsChunk046Chars ++ (momentRecordsChunk047Chars ++ (tail))))) (momentRecordsChunk044Push (acc)) := array_moment_records_chunk_044 fuel (momentRecordsChunk045Chars ++ (momentRecordsChunk046Chars ++ (momentRecordsChunk047Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 47) (SourceJson.white (momentRecordsChunk046Chars ++ (momentRecordsChunk047Chars ++ (tail)))) (momentRecordsChunk045Push (momentRecordsChunk044Push (acc))) := array_moment_records_chunk_045 fuel (momentRecordsChunk046Chars ++ (momentRecordsChunk047Chars ++ (tail))) (momentRecordsChunk044Push (acc))
    _ = SourceJson.array (fuel + 46) (SourceJson.white (momentRecordsChunk047Chars ++ (tail))) (momentRecordsChunk046Push (momentRecordsChunk045Push (momentRecordsChunk044Push (acc)))) := array_moment_records_chunk_046 fuel (momentRecordsChunk047Chars ++ (tail)) (momentRecordsChunk045Push (momentRecordsChunk044Push (acc)))
    _ = SourceJson.array (fuel + 45) (SourceJson.white tail) (momentRecordsBlock011Push acc) := array_moment_records_chunk_047 fuel (tail) (momentRecordsChunk046Push (momentRecordsChunk045Push (momentRecordsChunk044Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_011_before_raw_binding"
  err.flush

theorem moment_records_block_011_prefix :
    (momentRest05 22875).take 2032 = momentRecordsBlock011Chars := by rfl

theorem moment_records_block_011_split :
    momentRest05 22875 = momentRecordsBlock011Chars ++ momentRest05 24907 := by
  calc
    momentRest05 22875 =
        (momentRest05 22875).take 2032 ++ (momentRest05 22875).drop 2032 :=
      (List.take_append_drop 2032 (momentRest05 22875)).symm
    _ = momentRecordsBlock011Chars ++ (momentRest05 22875).drop 2032 :=
      congrArg (fun p => p ++ (momentRest05 22875).drop 2032) moment_records_block_011_prefix
    _ = momentRecordsBlock011Chars ++ momentRest05 24907 :=
      congrArg (fun rest => momentRecordsBlock011Chars ++ rest) (momentRest05_drop 22875 2032)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_011_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_011 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 49)
      (SourceJson.white (momentRest05 22875)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white (momentRest05 24907)) (momentRecordsBlock011Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 49) (SourceJson.white s) acc)
      moment_records_block_011_split).trans (array_moment_records_block_011 fuel (momentRest05 24907) acc)

theorem moment_records_through_block_011 (fuel : Nat) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRest05 364)) [] =
      SourceJson.array (fuel + 45) (SourceJson.white (momentRest05 24907)) momentRecordsAcc048 := by
  exact (moment_records_through_block_010 fuel).trans (array_moment_records_original_block_011 fuel momentRecordsAcc044)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_011_complete"
  err.flush

#print axioms array_moment_records_chunk_044
#print axioms array_moment_records_chunk_045
#print axioms array_moment_records_chunk_046
#print axioms array_moment_records_chunk_047
#print axioms array_moment_records_block_011
#print axioms moment_records_block_011_prefix
#print axioms moment_records_block_011_split
#print axioms array_moment_records_original_block_011
#print axioms moment_records_through_block_011

end ImbalancedChen.P2OriginalSaving19Moment05Parsing
