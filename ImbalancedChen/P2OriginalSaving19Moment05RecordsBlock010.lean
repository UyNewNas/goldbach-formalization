import ImbalancedChen.P2OriginalSaving19Moment05RecordsBlock009

/-! Original moment records block 10. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk040Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '6', '8', '9', '6', '4', '5', '2', '5', '3', '5', '8', '6', '0', '3', '1', '9', '3', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '8', '0', '5', '7', '0', '3', '1', '6', '7', '6', '7', '6', '4', '7', '6', '4', '8', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '5', '5', '2', '0', '7', '8', '3', '4', '0', '9', '8', '8', '8', '0', '9', '8', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '1', '7', '8', '8', '6', '4', '0', '7', '1', '5', '6', '9', '8', '4', '2', '4', '2', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '7', '9', '3', '8', '6', '2', '7', '8', '3', '4', '0', '6', '6', '0', '8', '7', '6', '6', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '4', '9', '6', '1', '4', '7', '9', '7', '1', '8', '8', '3', '6', '0', '0', '2', '1', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '0', '7', '1', '6', '2', '6', '7', '4', '0', '8', '3', '3', '0', '5', '9', '5', '9', '1', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '3', '8', '8', '5', '0', '2', '0', '3', '4', '1', '8', '6', '2', '5', '3', '3', '5', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '5', '8', '9', '5', '3', '7', '6', '9', '6', '1', '9', '6', '3', '7', '3', '7', '5', '6', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '8', '5', '6', '0', '9', '2', '7', '0', '9', '5', '6', '8', '7', '4', '9', '1', '4', '4', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '8', '1', '1', '2', '4', '6', '0', '9', '1', '3', '1', '7', '0', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '8', '4', '9', '2', '3', '2', '2', '3', '0', '1', '1', '9', '4', '6', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk040Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['4', '0'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['2', '8', '6', '8', '9', '6', '4', '5', '2', '5', '3', '5', '8', '6', '0', '3', '1', '9', '3', '4', '5']), .str (String.ofList ['3', '3', '8', '0', '5', '7', '0', '3', '1', '6', '7', '6', '7', '6', '4', '7', '6', '4', '8', '7', '6']), .str (String.ofList ['1', '5', '9', '5', '5', '2', '0', '7', '8', '3', '4', '0', '9', '8', '8', '8', '0', '9', '8', '9', '0']), .str (String.ofList ['3', '1', '1', '7', '8', '8', '6', '4', '0', '7', '1', '5', '6', '9', '8', '4', '2', '4', '2', '2', '4']), .str (String.ofList ['3', '3', '7', '9', '3', '8', '6', '2', '7', '8', '3', '4', '0', '6', '6', '0', '8', '7', '6', '6', '8']), .str (String.ofList ['3', '2', '8', '4', '9', '6', '1', '4', '7', '9', '7', '1', '8', '8', '3', '6', '0', '0', '2', '1', '1']), .str (String.ofList ['1', '2', '7', '0', '7', '1', '6', '2', '6', '7', '4', '0', '8', '3', '3', '0', '5', '9', '5', '9', '1', '1']), .str (String.ofList ['2', '4', '3', '8', '8', '5', '0', '2', '0', '3', '4', '1', '8', '6', '2', '5', '3', '3', '5', '0', '7']), .str (String.ofList ['3', '3', '5', '8', '9', '5', '3', '7', '6', '9', '6', '1', '9', '6', '3', '7', '3', '7', '5', '6', '6']), .str (String.ofList ['2', '6', '8', '5', '6', '0', '9', '2', '7', '0', '9', '5', '6', '8', '7', '4', '9', '1', '4', '4', '8'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '1', '8', '1', '1', '2', '4', '6', '0', '9', '1', '3', '1', '7', '0', '2', '2'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '1', '8', '4', '9', '2', '3', '2', '2', '3', '0', '1', '1', '9', '4', '6', '3']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_040_before_generic"
  err.flush

theorem array_moment_records_chunk_040 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 53)
      (SourceJson.white (momentRecordsChunk040Chars ++ tail)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white tail) (momentRecordsChunk040Push acc) := by rfl

noncomputable def momentRecordsAcc041 : List SourceJson := momentRecordsChunk040Push momentRecordsAcc040

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_040_generic_complete"
  err.flush

noncomputable def momentRecordsChunk041Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '8', '5', '7', '3', '1', '4', '3', '4', '8', '8', '3', '4', '5', '7', '6', '7', '1', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '1', '4', '3', '3', '6', '3', '7', '4', '4', '1', '5', '0', '8', '6', '4', '2', '9', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '0', '8', '0', '7', '1', '4', '7', '3', '3', '2', '0', '8', '6', '6', '4', '4', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '4', '1', '2', '7', '6', '8', '5', '7', '6', '6', '7', '9', '2', '5', '6', '9', '8', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '6', '3', '6', '9', '5', '2', '5', '6', '3', '7', '3', '4', '4', '7', '0', '9', '4', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '7', '3', '6', '0', '9', '5', '3', '2', '1', '5', '3', '9', '4', '1', '7', '1', '2', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '3', '7', '0', '4', '3', '5', '2', '4', '3', '2', '2', '6', '6', '0', '0', '1', '3', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '1', '6', '9', '5', '5', '6', '2', '0', '9', '1', '2', '6', '4', '4', '8', '1', '6', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '6', '2', '2', '0', '8', '4', '0', '0', '5', '0', '4', '8', '1', '9', '2', '2', '5', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '0', '1', '3', '0', '3', '1', '5', '5', '7', '1', '0', '4', '4', '8', '2', '5', '0', '9', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '3', '1', '6', '8', '3', '4', '0', '6', '0', '9', '7', '7', '7', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '3', '5', '2', '5', '4', '3', '7', '4', '3', '1', '5', '8', '2', '6', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk041Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['4', '1'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['2', '5', '8', '5', '7', '3', '1', '4', '3', '4', '8', '8', '3', '4', '5', '7', '6', '7', '1', '3', '6']), .str (String.ofList ['3', '2', '1', '4', '3', '3', '6', '3', '7', '4', '4', '1', '5', '0', '8', '6', '4', '2', '9', '7', '0']), .str (String.ofList ['1', '3', '9', '0', '8', '0', '7', '1', '4', '7', '3', '3', '2', '0', '8', '6', '6', '4', '4', '7', '5']), .str (String.ofList ['2', '4', '4', '1', '2', '7', '6', '8', '5', '7', '6', '6', '7', '9', '2', '5', '6', '9', '8', '5', '7']), .str (String.ofList ['2', '8', '6', '3', '6', '9', '5', '2', '5', '6', '3', '7', '3', '4', '4', '7', '0', '9', '4', '3', '7']), .str (String.ofList ['2', '9', '7', '3', '6', '0', '9', '5', '3', '2', '1', '5', '3', '9', '4', '1', '7', '1', '2', '3', '7']), .str (String.ofList ['1', '3', '4', '3', '7', '0', '4', '3', '5', '2', '4', '3', '2', '2', '6', '6', '0', '0', '1', '3', '0', '6']), .str (String.ofList ['2', '9', '1', '6', '9', '5', '5', '6', '2', '0', '9', '1', '2', '6', '4', '4', '8', '1', '6', '4', '3']), .str (String.ofList ['3', '3', '6', '2', '2', '0', '8', '4', '0', '0', '5', '0', '4', '8', '1', '9', '2', '2', '5', '2', '2']), .str (String.ofList ['2', '9', '0', '1', '3', '0', '3', '1', '5', '5', '7', '1', '0', '4', '4', '8', '2', '5', '0', '9', '1'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '1', '3', '1', '6', '8', '3', '4', '0', '6', '0', '9', '7', '7', '7', '6', '0'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '1', '3', '5', '2', '5', '4', '3', '7', '4', '3', '1', '5', '8', '2', '6', '9']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_041_before_generic"
  err.flush

theorem array_moment_records_chunk_041 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52)
      (SourceJson.white (momentRecordsChunk041Chars ++ tail)) acc =
      SourceJson.array (fuel + 51) (SourceJson.white tail) (momentRecordsChunk041Push acc) := by rfl

noncomputable def momentRecordsAcc042 : List SourceJson := momentRecordsChunk041Push momentRecordsAcc041

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_041_generic_complete"
  err.flush

noncomputable def momentRecordsChunk042Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '5', '8', '7', '6', '3', '4', '9', '9', '1', '2', '1', '6', '7', '4', '7', '4', '6', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '6', '5', '9', '3', '0', '8', '1', '0', '9', '8', '3', '7', '5', '6', '5', '7', '0', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '6', '8', '6', '8', '6', '6', '9', '7', '2', '5', '5', '9', '2', '9', '9', '6', '3', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '3', '0', '0', '1', '3', '9', '1', '9', '7', '7', '1', '7', '7', '4', '8', '1', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '5', '4', '4', '0', '4', '2', '4', '1', '0', '0', '3', '4', '9', '2', '8', '9', '0', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '9', '3', '0', '2', '4', '7', '8', '6', '1', '2', '0', '7', '7', '9', '3', '2', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '1', '8', '0', '3', '0', '6', '7', '4', '4', '5', '7', '3', '5', '3', '2', '4', '2', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '5', '5', '5', '3', '0', '8', '6', '0', '7', '1', '4', '1', '6', '5', '4', '5', '7', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '9', '0', '3', '8', '6', '3', '2', '3', '7', '1', '0', '6', '8', '5', '5', '2', '6', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '5', '5', '5', '1', '4', '8', '4', '1', '1', '4', '1', '5', '3', '5', '6', '9', '1', '1', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '5', '6', '0', '6', '9', '3', '7', '9', '8', '8', '6', '1', '3', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '5', '8', '7', '0', '1', '2', '9', '7', '4', '9', '5', '9', '9', '2', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk042Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['4', '2'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['2', '0', '3', '5', '8', '7', '6', '3', '4', '9', '9', '1', '2', '1', '6', '7', '4', '7', '4', '6', '6']), .str (String.ofList ['2', '6', '6', '5', '9', '3', '0', '8', '1', '0', '9', '8', '3', '7', '5', '6', '5', '7', '0', '2', '0']), .str (String.ofList ['8', '3', '6', '8', '6', '8', '6', '6', '9', '7', '2', '5', '5', '9', '2', '9', '9', '6', '3', '3']), .str (String.ofList ['1', '1', '4', '3', '0', '0', '1', '3', '9', '1', '9', '7', '7', '1', '7', '7', '4', '8', '1', '2', '4']), .str (String.ofList ['1', '9', '5', '4', '4', '0', '4', '2', '4', '1', '0', '0', '3', '4', '9', '2', '8', '9', '0', '2', '1']), .str (String.ofList ['1', '2', '4', '9', '3', '0', '2', '4', '7', '8', '6', '1', '2', '0', '7', '7', '9', '3', '2', '0', '1']), .str (String.ofList ['6', '5', '1', '8', '0', '3', '0', '6', '7', '4', '4', '5', '7', '3', '5', '3', '2', '4', '2', '3', '4']), .str (String.ofList ['2', '9', '5', '5', '5', '3', '0', '8', '6', '0', '7', '1', '4', '1', '6', '5', '4', '5', '7', '9', '0']), .str (String.ofList ['3', '2', '9', '0', '3', '8', '6', '3', '2', '3', '7', '1', '0', '6', '8', '5', '5', '2', '6', '2', '9']), .str (String.ofList ['2', '6', '5', '5', '5', '1', '4', '8', '4', '1', '1', '4', '1', '5', '3', '5', '6', '9', '1', '1', '1'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '2', '5', '6', '0', '6', '9', '3', '7', '9', '8', '8', '6', '1', '3', '8', '4'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '2', '5', '8', '7', '0', '1', '2', '9', '7', '4', '9', '5', '9', '9', '2', '4']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_042_before_generic"
  err.flush

theorem array_moment_records_chunk_042 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 51)
      (SourceJson.white (momentRecordsChunk042Chars ++ tail)) acc =
      SourceJson.array (fuel + 50) (SourceJson.white tail) (momentRecordsChunk042Push acc) := by rfl

noncomputable def momentRecordsAcc043 : List SourceJson := momentRecordsChunk042Push momentRecordsAcc042

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_042_generic_complete"
  err.flush

noncomputable def momentRecordsChunk043Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '4', '0', '6', '4', '6', '1', '9', '2', '6', '7', '6', '2', '4', '6', '3', '5', '4', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '2', '6', '8', '8', '8', '9', '5', '7', '0', '9', '1', '4', '0', '4', '6', '6', '8', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '1', '5', '7', '2', '7', '3', '8', '0', '6', '7', '3', '8', '5', '2', '1', '0', '4', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '0', '4', '7', '1', '0', '0', '1', '1', '9', '1', '0', '9', '3', '1', '7', '8', '8', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '9', '6', '4', '8', '4', '4', '6', '8', '1', '6', '1', '9', '6', '1', '3', '8', '7', '8', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '7', '1', '9', '2', '1', '6', '4', '6', '7', '2', '5', '6', '0', '6', '6', '8', '9', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '4', '4', '4', '4', '9', '3', '9', '5', '2', '4', '7', '9', '2', '8', '7', '9', '8', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '9', '6', '2', '4', '8', '3', '1', '9', '9', '3', '0', '8', '7', '3', '3', '8', '3', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '5', '6', '6', '5', '5', '0', '6', '2', '4', '1', '1', '8', '3', '1', '9', '0', '1', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '5', '7', '0', '0', '8', '3', '8', '2', '7', '5', '9', '0', '1', '0', '2', '3', '2', '5', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '8', '6', '6', '5', '7', '7', '1', '0', '5', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '9', '3', '6', '0', '1', '2', '2', '6', '1', '9', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk043Push (acc : List SourceJson) : List SourceJson :=
  .obj [((String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']), .number (String.ofList ['4', '3'])), ((String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0']), .arr [.str (String.ofList ['4', '8', '4', '0', '6', '4', '6', '1', '9', '2', '6', '7', '6', '2', '4', '6', '3', '5', '4', '0', '5']), .str (String.ofList ['5', '1', '2', '6', '8', '8', '8', '9', '5', '7', '0', '9', '1', '4', '0', '4', '6', '6', '8', '4', '2']), .str (String.ofList ['1', '7', '1', '5', '7', '2', '7', '3', '8', '0', '6', '7', '3', '8', '5', '2', '1', '0', '4', '3', '0']), .str (String.ofList ['4', '2', '0', '4', '7', '1', '0', '0', '1', '1', '9', '1', '0', '9', '3', '1', '7', '8', '8', '4', '1']), .str (String.ofList ['4', '2', '9', '6', '4', '8', '4', '4', '6', '8', '1', '6', '1', '9', '6', '1', '3', '8', '7', '8', '9']), .str (String.ofList ['3', '8', '7', '1', '9', '2', '1', '6', '4', '6', '7', '2', '5', '6', '0', '6', '6', '8', '9', '3', '9']), .str (String.ofList ['9', '1', '4', '4', '4', '4', '9', '3', '9', '5', '2', '4', '7', '9', '2', '8', '7', '9', '8', '4', '3']), .str (String.ofList ['4', '6', '9', '6', '2', '4', '8', '3', '1', '9', '9', '3', '0', '8', '7', '3', '3', '8', '3', '4', '3']), .str (String.ofList ['3', '2', '5', '6', '6', '5', '5', '0', '6', '2', '4', '1', '1', '8', '3', '1', '9', '0', '1', '2', '6']), .str (String.ofList ['3', '2', '5', '7', '0', '0', '8', '3', '8', '2', '7', '5', '9', '0', '1', '0', '2', '3', '2', '5', '3'])]), ((String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '8', '8', '6', '6', '5', '7', '7', '1', '0', '5', '4', '5'])), ((String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']), .str (String.ofList ['1', '8', '9', '3', '6', '0', '1', '2', '2', '6', '1', '9', '4']))] :: acc

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_043_before_generic"
  err.flush

theorem array_moment_records_chunk_043 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 50)
      (SourceJson.white (momentRecordsChunk043Chars ++ tail)) acc =
      SourceJson.array (fuel + 49) (SourceJson.white tail) (momentRecordsChunk043Push acc) := by rfl

noncomputable def momentRecordsAcc044 : List SourceJson := momentRecordsChunk043Push momentRecordsAcc043

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_chunk_043_generic_complete"
  err.flush

noncomputable def momentRecordsBlock010Chars : List Char := momentRecordsChunk040Chars ++ momentRecordsChunk041Chars ++ momentRecordsChunk042Chars ++ momentRecordsChunk043Chars
noncomputable def momentRecordsBlock010Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk043Push (momentRecordsChunk042Push (momentRecordsChunk041Push (momentRecordsChunk040Push (acc))))

theorem array_moment_records_block_010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 53)
      (SourceJson.white (momentRecordsBlock010Chars ++ tail)) acc =
      SourceJson.array (fuel + 49) (SourceJson.white tail) (momentRecordsBlock010Push acc) := by
  have hinput : momentRecordsBlock010Chars ++ tail = momentRecordsChunk040Chars ++ (momentRecordsChunk041Chars ++ (momentRecordsChunk042Chars ++ (momentRecordsChunk043Chars ++ (tail)))) := by
    simp only [momentRecordsBlock010Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 53) (SourceJson.white (momentRecordsBlock010Chars ++ tail)) acc =
        SourceJson.array (fuel + 53) (SourceJson.white (momentRecordsChunk040Chars ++ (momentRecordsChunk041Chars ++ (momentRecordsChunk042Chars ++ (momentRecordsChunk043Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 53) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 52) (SourceJson.white (momentRecordsChunk041Chars ++ (momentRecordsChunk042Chars ++ (momentRecordsChunk043Chars ++ (tail))))) (momentRecordsChunk040Push (acc)) := array_moment_records_chunk_040 fuel (momentRecordsChunk041Chars ++ (momentRecordsChunk042Chars ++ (momentRecordsChunk043Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 51) (SourceJson.white (momentRecordsChunk042Chars ++ (momentRecordsChunk043Chars ++ (tail)))) (momentRecordsChunk041Push (momentRecordsChunk040Push (acc))) := array_moment_records_chunk_041 fuel (momentRecordsChunk042Chars ++ (momentRecordsChunk043Chars ++ (tail))) (momentRecordsChunk040Push (acc))
    _ = SourceJson.array (fuel + 50) (SourceJson.white (momentRecordsChunk043Chars ++ (tail))) (momentRecordsChunk042Push (momentRecordsChunk041Push (momentRecordsChunk040Push (acc)))) := array_moment_records_chunk_042 fuel (momentRecordsChunk043Chars ++ (tail)) (momentRecordsChunk041Push (momentRecordsChunk040Push (acc)))
    _ = SourceJson.array (fuel + 49) (SourceJson.white tail) (momentRecordsBlock010Push acc) := array_moment_records_chunk_043 fuel (tail) (momentRecordsChunk042Push (momentRecordsChunk041Push (momentRecordsChunk040Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_010_before_raw_binding"
  err.flush

theorem moment_records_block_010_prefix :
    (momentRest05 20818).take 2057 = momentRecordsBlock010Chars := by rfl

theorem moment_records_block_010_split :
    momentRest05 20818 = momentRecordsBlock010Chars ++ momentRest05 22875 := by
  calc
    momentRest05 20818 =
        (momentRest05 20818).take 2057 ++ (momentRest05 20818).drop 2057 :=
      (List.take_append_drop 2057 (momentRest05 20818)).symm
    _ = momentRecordsBlock010Chars ++ (momentRest05 20818).drop 2057 :=
      congrArg (fun p => p ++ (momentRest05 20818).drop 2057) moment_records_block_010_prefix
    _ = momentRecordsBlock010Chars ++ momentRest05 22875 :=
      congrArg (fun rest => momentRecordsBlock010Chars ++ rest) (momentRest05_drop 20818 2057)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_010_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_010 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 53)
      (SourceJson.white (momentRest05 20818)) acc =
      SourceJson.array (fuel + 49) (SourceJson.white (momentRest05 22875)) (momentRecordsBlock010Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 53) (SourceJson.white s) acc)
      moment_records_block_010_split).trans (array_moment_records_block_010 fuel (momentRest05 22875) acc)

theorem moment_records_through_block_010 (fuel : Nat) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRest05 364)) [] =
      SourceJson.array (fuel + 49) (SourceJson.white (momentRest05 22875)) momentRecordsAcc044 := by
  exact (moment_records_through_block_009 fuel).trans (array_moment_records_original_block_010 fuel momentRecordsAcc040)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 records_block_010_complete"
  err.flush

#print axioms array_moment_records_chunk_040
#print axioms array_moment_records_chunk_041
#print axioms array_moment_records_chunk_042
#print axioms array_moment_records_chunk_043
#print axioms array_moment_records_block_010
#print axioms moment_records_block_010_prefix
#print axioms moment_records_block_010_split
#print axioms array_moment_records_original_block_010
#print axioms moment_records_through_block_010

end ImbalancedChen.P2OriginalSaving19Moment05Parsing
