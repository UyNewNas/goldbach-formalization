import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock012

/-! Original moment records block 13. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk052Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '4', '0', '9', '6', '3', '4', '4', '1', '3', '3', '9', '0', '2', '7', '7', '6', '7', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '5', '6', '2', '1', '9', '4', '7', '3', '9', '7', '6', '8', '5', '0', '1', '8', '2', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '7', '3', '1', '3', '9', '0', '8', '0', '9', '9', '4', '7', '3', '0', '9', '9', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '2', '0', '4', '8', '0', '5', '2', '4', '3', '1', '2', '8', '2', '2', '1', '2', '3', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '5', '3', '5', '1', '1', '2', '6', '3', '5', '9', '5', '2', '8', '4', '5', '8', '8', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '4', '3', '8', '8', '6', '0', '4', '5', '6', '1', '3', '4', '8', '7', '1', '4', '0', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '1', '6', '1', '0', '5', '7', '2', '5', '8', '6', '6', '9', '5', '6', '8', '1', '5', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '8', '4', '0', '6', '4', '0', '7', '6', '9', '2', '5', '1', '4', '5', '7', '8', '1', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '7', '0', '1', '5', '0', '1', '5', '8', '7', '4', '1', '2', '6', '2', '8', '1', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '7', '1', '4', '5', '5', '9', '6', '9', '6', '4', '7', '3', '1', '7', '0', '5', '8', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '7', '1', '6', '3', '8', '4', '4', '0', '8', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '8', '0', '0', '3', '9', '1', '8', '1', '0', '9', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk052Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5', '2'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '9', '4', '0', '9', '6', '3', '4', '4', '1', '3', '3', '9', '0', '2', '7', '7', '6', '7', '9', '3']), .str (String.ofList ['4', '5', '5', '6', '2', '1', '9', '4', '7', '3', '9', '7', '6', '8', '5', '0', '1', '8', '2', '0', '0']), .str (String.ofList ['2', '1', '7', '7', '3', '1', '3', '9', '0', '8', '0', '9', '9', '4', '7', '3', '0', '9', '9', '2', '9']), .str (String.ofList ['4', '4', '2', '0', '4', '8', '0', '5', '2', '4', '3', '1', '2', '8', '2', '2', '1', '2', '3', '0', '9']), .str (String.ofList ['3', '1', '5', '3', '5', '1', '1', '2', '6', '3', '5', '9', '5', '2', '8', '4', '5', '8', '8', '9', '3']), .str (String.ofList ['4', '8', '4', '3', '8', '8', '6', '0', '4', '5', '6', '1', '3', '4', '8', '7', '1', '4', '0', '5', '1']), .str (String.ofList ['3', '3', '1', '6', '1', '0', '5', '7', '2', '5', '8', '6', '6', '9', '5', '6', '8', '1', '5', '5', '0']), .str (String.ofList ['4', '1', '8', '4', '0', '6', '4', '0', '7', '6', '9', '2', '5', '1', '4', '5', '7', '8', '1', '7', '1']), .str (String.ofList ['2', '9', '9', '7', '0', '1', '5', '0', '1', '5', '8', '7', '4', '1', '2', '6', '2', '8', '1', '2', '9']), .str (String.ofList ['2', '9', '9', '7', '1', '4', '5', '5', '9', '6', '9', '6', '4', '7', '3', '1', '7', '0', '5', '8', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '7', '7', '1', '6', '3', '8', '4', '4', '0', '8', '1', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '7', '8', '0', '0', '3', '9', '1', '8', '1', '0', '9', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_052_before_generic"
  err.flush

theorem array_moment_records_chunk_052 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 41)
      (SourceJson.white (momentRecordsChunk052Chars ++ tail)) acc =
      SourceJson.array (fuel + 40) (SourceJson.white tail) (momentRecordsChunk052Push acc) := by rfl

noncomputable def momentRecordsAcc053 : List SourceJson := momentRecordsChunk052Push momentRecordsAcc052

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_052_generic_complete"
  err.flush

noncomputable def momentRecordsChunk053Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '4', '9', '1', '2', '0', '0', '6', '6', '5', '0', '5', '5', '9', '9', '9', '0', '8', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '8', '6', '8', '2', '5', '6', '5', '2', '4', '6', '2', '3', '0', '4', '4', '6', '9', '3', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '7', '8', '4', '1', '6', '1', '8', '0', '1', '5', '5', '4', '8', '6', '0', '8', '9', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '9', '5', '8', '8', '2', '2', '9', '9', '3', '8', '7', '0', '7', '6', '6', '3', '1', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '4', '6', '6', '0', '5', '6', '6', '8', '9', '7', '7', '1', '6', '2', '1', '9', '4', '4', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '5', '7', '2', '7', '3', '9', '1', '5', '1', '5', '4', '2', '7', '9', '9', '5', '8', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '5', '4', '5', '7', '5', '3', '9', '3', '5', '2', '4', '7', '9', '2', '2', '9', '3', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '6', '0', '6', '3', '7', '6', '3', '0', '4', '6', '8', '1', '4', '8', '5', '7', '5', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '9', '9', '8', '1', '5', '3', '3', '6', '7', '4', '2', '4', '7', '5', '2', '1', '6', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '9', '9', '9', '2', '0', '5', '3', '7', '2', '5', '5', '0', '3', '7', '9', '7', '3', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '7', '4', '6', '7', '5', '9', '1', '3', '2', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '8', '2', '2', '2', '0', '9', '4', '4', '4', '1', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk053Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5', '3'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '4', '4', '9', '1', '2', '0', '0', '6', '6', '5', '0', '5', '5', '9', '9', '9', '0', '8', '3', '4']), .str (String.ofList ['4', '1', '8', '6', '8', '2', '5', '6', '5', '2', '4', '6', '2', '3', '0', '4', '4', '6', '9', '3', '3']), .str (String.ofList ['1', '8', '7', '8', '4', '1', '6', '1', '8', '0', '1', '5', '5', '4', '8', '6', '0', '8', '9', '8', '6']), .str (String.ofList ['3', '3', '9', '5', '8', '8', '2', '2', '9', '9', '3', '8', '7', '0', '7', '6', '6', '3', '1', '9', '8']), .str (String.ofList ['2', '9', '4', '6', '6', '0', '5', '6', '6', '8', '9', '7', '7', '1', '6', '2', '1', '9', '4', '4', '0']), .str (String.ofList ['4', '2', '5', '7', '2', '7', '3', '9', '1', '5', '1', '5', '4', '2', '7', '9', '9', '5', '8', '1', '4']), .str (String.ofList ['3', '3', '5', '4', '5', '7', '5', '3', '9', '3', '5', '2', '4', '7', '9', '2', '2', '9', '3', '8', '6']), .str (String.ofList ['3', '5', '6', '0', '6', '3', '7', '6', '3', '0', '4', '6', '8', '1', '4', '8', '5', '7', '5', '1', '6']), .str (String.ofList ['2', '8', '9', '9', '8', '1', '5', '3', '3', '6', '7', '4', '2', '4', '7', '5', '2', '1', '6', '9', '8']), .str (String.ofList ['2', '8', '9', '9', '9', '2', '0', '5', '3', '7', '2', '5', '5', '0', '3', '7', '9', '7', '3', '6', '4'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '7', '7', '4', '6', '7', '5', '9', '1', '3', '2', '9', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '7', '8', '2', '2', '2', '0', '9', '4', '4', '4', '1', '0']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_053_before_generic"
  err.flush

theorem array_moment_records_chunk_053 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 40)
      (SourceJson.white (momentRecordsChunk053Chars ++ tail)) acc =
      SourceJson.array (fuel + 39) (SourceJson.white tail) (momentRecordsChunk053Push acc) := by rfl

noncomputable def momentRecordsAcc054 : List SourceJson := momentRecordsChunk053Push momentRecordsAcc053

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_053_generic_complete"
  err.flush

noncomputable def momentRecordsChunk054Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '3', '2', '4', '3', '1', '0', '7', '2', '9', '8', '5', '4', '1', '8', '3', '0', '3', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '0', '3', '7', '7', '2', '5', '4', '7', '5', '1', '4', '8', '4', '6', '1', '2', '4', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '4', '0', '9', '2', '0', '4', '6', '4', '1', '3', '6', '5', '7', '0', '2', '8', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '5', '8', '7', '2', '9', '6', '3', '6', '3', '2', '5', '4', '6', '2', '9', '5', '8', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '3', '1', '6', '5', '1', '6', '5', '9', '7', '6', '2', '6', '1', '0', '3', '9', '4', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '3', '6', '8', '5', '0', '7', '6', '4', '0', '1', '6', '8', '7', '7', '3', '7', '7', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '7', '2', '7', '6', '6', '7', '6', '6', '3', '4', '3', '0', '2', '9', '9', '7', '1', '5', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '1', '1', '9', '8', '5', '8', '3', '7', '0', '1', '9', '1', '9', '8', '6', '8', '4', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '4', '3', '8', '3', '0', '1', '0', '5', '6', '9', '8', '4', '0', '7', '5', '7', '8', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '4', '3', '8', '9', '5', '5', '1', '1', '0', '2', '5', '4', '5', '4', '3', '9', '4', '4', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '5', '8', '4', '6', '8', '2', '1', '0', '1', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '6', '2', '6', '8', '5', '6', '1', '4', '5', '6', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk054Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5', '4'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '9', '3', '2', '4', '3', '1', '0', '7', '2', '9', '8', '5', '4', '1', '8', '3', '0', '3', '6', '2']), .str (String.ofList ['2', '8', '0', '3', '7', '7', '2', '5', '4', '7', '5', '1', '4', '8', '4', '6', '1', '2', '4', '9', '6']), .str (String.ofList ['1', '2', '9', '4', '0', '9', '2', '0', '4', '6', '4', '1', '3', '6', '5', '7', '0', '2', '8', '0', '2']), .str (String.ofList ['1', '4', '1', '5', '8', '7', '2', '9', '6', '3', '6', '3', '2', '5', '4', '6', '2', '9', '5', '8', '5']), .str (String.ofList ['2', '0', '4', '3', '1', '6', '5', '1', '6', '5', '9', '7', '6', '2', '6', '1', '0', '3', '9', '4', '7']), .str (String.ofList ['1', '9', '3', '6', '8', '5', '0', '7', '6', '4', '0', '1', '6', '8', '7', '7', '3', '7', '7', '9', '3']), .str (String.ofList ['3', '1', '7', '2', '7', '6', '6', '7', '6', '6', '3', '4', '3', '0', '2', '9', '9', '7', '1', '5', '4']), .str (String.ofList ['3', '1', '1', '1', '9', '8', '5', '8', '3', '7', '0', '1', '9', '1', '9', '8', '6', '8', '4', '5', '2']), .str (String.ofList ['1', '9', '4', '3', '8', '3', '0', '1', '0', '5', '6', '9', '8', '4', '0', '7', '5', '7', '8', '3', '1']), .str (String.ofList ['1', '9', '4', '3', '8', '9', '5', '5', '1', '1', '0', '2', '5', '4', '5', '4', '3', '9', '4', '4', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '3', '5', '8', '4', '6', '8', '2', '1', '0', '1', '3', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '3', '6', '2', '6', '8', '5', '6', '1', '4', '5', '6', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_054_before_generic"
  err.flush

theorem array_moment_records_chunk_054 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 39)
      (SourceJson.white (momentRecordsChunk054Chars ++ tail)) acc =
      SourceJson.array (fuel + 38) (SourceJson.white tail) (momentRecordsChunk054Push acc) := by rfl

noncomputable def momentRecordsAcc055 : List SourceJson := momentRecordsChunk054Push momentRecordsAcc054

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_054_generic_complete"
  err.flush

noncomputable def momentRecordsChunk055Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '2', '9', '5', '2', '3', '0', '7', '8', '8', '1', '9', '2', '6', '9', '2', '1', '9', '8', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '4', '6', '3', '6', '6', '9', '4', '3', '1', '8', '0', '9', '0', '9', '3', '8', '4', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '2', '2', '5', '6', '8', '5', '5', '5', '4', '1', '0', '9', '7', '2', '2', '0', '2', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '0', '3', '1', '9', '6', '2', '2', '2', '4', '2', '6', '7', '1', '9', '3', '0', '2', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '0', '9', '1', '8', '5', '3', '3', '3', '5', '0', '5', '3', '2', '8', '1', '1', '4', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '9', '4', '5', '3', '2', '8', '1', '2', '7', '9', '5', '5', '1', '2', '3', '8', '1', '3', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '8', '5', '0', '4', '1', '1', '1', '4', '3', '2', '9', '0', '6', '4', '5', '3', '8', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '5', '5', '6', '7', '2', '7', '2', '0', '4', '1', '0', '6', '8', '5', '3', '8', '1', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '3', '4', '3', '5', '9', '3', '7', '3', '2', '7', '1', '2', '4', '1', '3', '9', '8', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '3', '4', '6', '1', '5', '3', '3', '2', '6', '3', '4', '5', '7', '5', '7', '5', '5', '3', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '7', '8', '9', '5', '7', '8', '6', '8', '5', '6', '6', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '8', '1', '0', '7', '0', '9', '7', '9', '3', '3', '3', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', '\r', '\n', ' ', ' ', ']']
noncomputable def momentRecordsChunk055Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5', '5'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '6', '2', '9', '5', '2', '3', '0', '7', '8', '8', '1', '9', '2', '6', '9', '2', '1', '9', '8', '9']), .str (String.ofList ['1', '7', '4', '6', '3', '6', '6', '9', '4', '3', '1', '8', '0', '9', '0', '9', '3', '8', '4', '6', '3']), .str (String.ofList ['2', '2', '2', '2', '5', '6', '8', '5', '5', '5', '4', '1', '0', '9', '7', '2', '2', '0', '2', '1', '5']), .str (String.ofList ['5', '8', '0', '3', '1', '9', '6', '2', '2', '2', '4', '2', '6', '7', '1', '9', '3', '0', '2', '9', '2']), .str (String.ofList ['2', '5', '6', '0', '9', '1', '8', '5', '3', '3', '3', '5', '0', '5', '3', '2', '8', '1', '1', '4', '4']), .str (String.ofList ['5', '4', '9', '4', '5', '3', '2', '8', '1', '2', '7', '9', '5', '5', '1', '2', '3', '8', '1', '3', '2']), .str (String.ofList ['6', '8', '8', '5', '0', '4', '1', '1', '1', '4', '3', '2', '9', '0', '6', '4', '5', '3', '8', '9', '6']), .str (String.ofList ['4', '7', '5', '5', '6', '7', '2', '7', '2', '0', '4', '1', '0', '6', '8', '5', '3', '8', '1', '7', '3']), .str (String.ofList ['3', '2', '3', '4', '3', '5', '9', '3', '7', '3', '2', '7', '1', '2', '4', '1', '3', '9', '8', '0', '9']), .str (String.ofList ['3', '2', '3', '4', '6', '1', '5', '3', '3', '2', '6', '3', '4', '5', '7', '5', '7', '5', '5', '3', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '7', '8', '9', '5', '7', '8', '6', '8', '5', '6', '6', '6'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '8', '1', '0', '7', '0', '9', '7', '9', '3', '3', '3', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_055_before_generic"
  err.flush

theorem array_moment_records_chunk_055 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 38)
      (SourceJson.white (momentRecordsChunk055Chars ++ tail)) acc =
      .ok (.arr ((momentRecordsChunk055Push acc).reverse), tail) := by rfl

noncomputable def momentRecordsAcc056 : List SourceJson := momentRecordsChunk055Push momentRecordsAcc055

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_055_generic_complete"
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
  err.putStrLn "P26_MOMENT00 records_block_013_before_raw_binding"
  err.flush

theorem moment_records_block_013_prefix :
    (momentRest00 26958).take 2036 = momentRecordsBlock013Chars := by rfl

theorem moment_records_block_013_split :
    momentRest00 26958 = momentRecordsBlock013Chars ++ momentRest00 28994 := by
  calc
    momentRest00 26958 =
        (momentRest00 26958).take 2036 ++ (momentRest00 26958).drop 2036 :=
      (List.take_append_drop 2036 (momentRest00 26958)).symm
    _ = momentRecordsBlock013Chars ++ (momentRest00 26958).drop 2036 :=
      congrArg (fun p => p ++ (momentRest00 26958).drop 2036) moment_records_block_013_prefix
    _ = momentRecordsBlock013Chars ++ momentRest00 28994 :=
      congrArg (fun rest => momentRecordsBlock013Chars ++ rest) (momentRest00_drop 26958 2036)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_block_013_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_013 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 41)
      (SourceJson.white (momentRest00 26958)) acc =
      .ok (.arr ((momentRecordsBlock013Push acc).reverse), momentRest00 28994) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 41) (SourceJson.white s) acc)
      moment_records_block_013_split).trans (array_moment_records_block_013 fuel (momentRest00 28994) acc)

noncomputable def momentRecordsArrayValue : SourceJson := .arr (momentRecordsAcc056.reverse)

theorem moment_records_through_block_013 (fuel : Nat) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRest00 364)) [] =
      .ok (momentRecordsArrayValue, momentRest00 28994) := by
  exact (moment_records_through_block_012 fuel).trans (array_moment_records_original_block_013 fuel momentRecordsAcc052)

theorem value_moment_records_original (fuel : Nat) :
    SourceJson.value (fuel + 94) (momentRest00 363) =
      .ok (momentRecordsArrayValue, momentRest00 28994) := by
  exact (value_moment_records_open fuel).trans (moment_records_through_block_013 fuel)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_block_013_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment00Parsing
