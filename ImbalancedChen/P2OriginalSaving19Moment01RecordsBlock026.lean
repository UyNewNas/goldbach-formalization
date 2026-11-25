import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock025

/-! Original moment records block 26. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk104Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '3', '1', '0', '4', '6', '6', '1', '4', '2', '5', '0', '2', '3', '9', '8', '5', '8', '3', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '3', '5', '4', '1', '4', '8', '9', '0', '0', '0', '7', '5', '2', '3', '4', '9', '3', '9', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '1', '8', '7', '4', '2', '9', '4', '4', '7', '7', '2', '4', '5', '4', '5', '9', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '7', '5', '9', '5', '7', '6', '8', '0', '2', '5', '3', '7', '8', '6', '2', '0', '9', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '5', '1', '6', '5', '8', '0', '2', '5', '9', '9', '4', '5', '3', '6', '6', '5', '3', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '0', '4', '4', '6', '3', '0', '4', '7', '5', '8', '9', '9', '1', '4', '1', '0', '9', '3', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '3', '8', '8', '6', '6', '5', '6', '1', '6', '2', '3', '2', '1', '2', '3', '8', '5', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '3', '8', '9', '5', '5', '5', '6', '0', '3', '3', '5', '9', '4', '5', '4', '3', '3', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '3', '8', '8', '0', '9', '2', '9', '5', '6', '1', '6', '0', '5', '0', '4', '0', '5', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '4', '1', '1', '3', '9', '6', '7', '4', '0', '2', '8', '8', '6', '5', '2', '9', '7', '0', '2', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '7', '5', '0', '8', '9', '5', '9', '7', '5', '4', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '8', '5', '6', '3', '0', '6', '7', '8', '4', '2', '4', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk104Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '0', '4'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '7', '3', '1', '0', '4', '6', '6', '1', '4', '2', '5', '0', '2', '3', '9', '8', '5', '8', '3', '9', '2']), .str (String.ofList ['1', '6', '7', '3', '5', '4', '1', '4', '8', '9', '0', '0', '0', '7', '5', '2', '3', '4', '9', '3', '9', '9']), .str (String.ofList ['2', '3', '4', '1', '8', '7', '4', '2', '9', '4', '4', '7', '7', '2', '4', '5', '4', '5', '9', '3', '5']), .str (String.ofList ['6', '9', '7', '5', '9', '5', '7', '6', '8', '0', '2', '5', '3', '7', '8', '6', '2', '0', '9', '2', '5']), .str (String.ofList ['1', '1', '0', '5', '1', '6', '5', '8', '0', '2', '5', '9', '9', '4', '5', '3', '6', '6', '5', '3', '7', '4']), .str (String.ofList ['2', '0', '0', '4', '4', '6', '3', '0', '4', '7', '5', '8', '9', '9', '1', '4', '1', '0', '9', '3', '0', '7']), .str (String.ofList ['1', '4', '4', '3', '8', '8', '6', '6', '5', '6', '1', '6', '2', '3', '2', '1', '2', '3', '8', '5', '3', '0']), .str (String.ofList ['1', '0', '8', '3', '8', '9', '5', '5', '5', '6', '0', '3', '3', '5', '9', '4', '5', '4', '3', '3', '5', '1']), .str (String.ofList ['1', '0', '8', '3', '8', '8', '0', '9', '2', '9', '5', '6', '1', '6', '0', '5', '0', '4', '0', '5', '0', '2']), .str (String.ofList ['1', '9', '4', '1', '1', '3', '9', '6', '7', '4', '0', '2', '8', '8', '6', '5', '2', '9', '7', '0', '2', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '7', '5', '0', '8', '9', '5', '9', '7', '5', '4', '6', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '8', '5', '6', '3', '0', '6', '7', '8', '4', '2', '4', '8']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_104_before_generic"
  err.flush

theorem array_moment_records_chunk_104 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 77)
      (SourceJson.white (momentRecordsChunk104Chars ++ tail)) acc =
      SourceJson.array (fuel + 76) (SourceJson.white tail) (momentRecordsChunk104Push acc) := by rfl

noncomputable def momentRecordsAcc105 : List SourceJson := momentRecordsChunk104Push momentRecordsAcc104

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_104_generic_complete"
  err.flush

noncomputable def momentRecordsChunk105Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '5', '8', '6', '5', '9', '2', '6', '6', '9', '5', '1', '1', '7', '4', '9', '2', '4', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '3', '6', '3', '6', '4', '5', '4', '7', '0', '7', '9', '1', '4', '3', '3', '6', '3', '9', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '9', '2', '5', '8', '5', '6', '2', '8', '2', '2', '7', '5', '0', '3', '1', '2', '7', '3', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '9', '2', '6', '4', '1', '6', '1', '0', '2', '5', '1', '0', '9', '4', '5', '4', '6', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '0', '2', '8', '7', '8', '3', '0', '6', '1', '4', '6', '3', '7', '4', '9', '0', '7', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '1', '4', '7', '7', '8', '8', '2', '3', '5', '8', '9', '6', '8', '4', '7', '1', '6', '3', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '2', '7', '8', '4', '0', '8', '2', '7', '8', '8', '0', '7', '4', '5', '2', '8', '6', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '5', '7', '0', '3', '3', '6', '9', '1', '2', '0', '1', '0', '6', '1', '2', '8', '4', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '5', '6', '9', '2', '0', '0', '5', '6', '0', '3', '3', '7', '4', '6', '9', '6', '7', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '2', '9', '1', '7', '8', '3', '2', '5', '5', '9', '1', '2', '4', '6', '2', '4', '8', '0', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '4', '8', '2', '4', '2', '4', '9', '5', '0', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '8', '3', '3', '6', '0', '9', '6', '7', '9', '1', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk105Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '0', '5'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '8', '1', '5', '8', '6', '5', '9', '2', '6', '6', '9', '5', '1', '1', '7', '4', '9', '2', '4', '3', '0']), .str (String.ofList ['1', '7', '6', '3', '6', '3', '6', '4', '5', '4', '7', '0', '7', '9', '1', '4', '3', '3', '6', '3', '9', '9']), .str (String.ofList ['2', '1', '9', '2', '5', '8', '5', '6', '2', '8', '2', '2', '7', '5', '0', '3', '1', '2', '7', '3', '2']), .str (String.ofList ['7', '5', '9', '2', '6', '4', '1', '6', '1', '0', '2', '5', '1', '0', '9', '4', '5', '4', '6', '8', '7']), .str (String.ofList ['1', '0', '4', '0', '2', '8', '7', '8', '3', '0', '6', '1', '4', '6', '3', '7', '4', '9', '0', '7', '9', '1']), .str (String.ofList ['2', '0', '1', '4', '7', '7', '8', '8', '2', '3', '5', '8', '9', '6', '8', '4', '7', '1', '6', '3', '1', '6']), .str (String.ofList ['1', '4', '3', '2', '7', '8', '4', '0', '8', '2', '7', '8', '8', '0', '7', '4', '5', '2', '8', '6', '6', '3']), .str (String.ofList ['1', '1', '2', '5', '7', '0', '3', '3', '6', '9', '1', '2', '0', '1', '0', '6', '1', '2', '8', '4', '0', '1']), .str (String.ofList ['1', '1', '2', '5', '6', '9', '2', '0', '0', '5', '6', '0', '3', '3', '7', '4', '6', '9', '6', '7', '2', '8']), .str (String.ofList ['1', '7', '0', '2', '9', '1', '7', '8', '3', '2', '5', '5', '9', '1', '2', '4', '6', '2', '4', '8', '0', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '2', '4', '8', '2', '4', '2', '4', '9', '5', '0', '4', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '2', '8', '3', '3', '6', '0', '9', '6', '7', '9', '1', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_105_before_generic"
  err.flush

theorem array_moment_records_chunk_105 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 76)
      (SourceJson.white (momentRecordsChunk105Chars ++ tail)) acc =
      SourceJson.array (fuel + 75) (SourceJson.white tail) (momentRecordsChunk105Push acc) := by rfl

noncomputable def momentRecordsAcc106 : List SourceJson := momentRecordsChunk105Push momentRecordsAcc105

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_105_generic_complete"
  err.flush

noncomputable def momentRecordsChunk106Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '8', '2', '0', '2', '6', '6', '7', '7', '1', '8', '9', '6', '3', '6', '1', '4', '2', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '8', '5', '5', '9', '0', '7', '6', '4', '5', '8', '3', '0', '8', '3', '0', '9', '0', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '2', '8', '3', '4', '1', '3', '6', '9', '5', '0', '7', '4', '1', '6', '4', '3', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '0', '6', '7', '4', '3', '3', '4', '6', '7', '9', '8', '6', '3', '6', '3', '3', '8', '3', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '1', '2', '4', '9', '5', '4', '3', '4', '3', '0', '5', '6', '5', '7', '2', '8', '0', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '4', '5', '3', '7', '6', '1', '5', '4', '1', '1', '5', '2', '3', '8', '3', '7', '9', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '7', '9', '4', '5', '9', '1', '7', '5', '2', '5', '6', '6', '0', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '7', '1', '5', '4', '5', '9', '1', '5', '6', '5', '6', '0', '9', '3', '6', '9', '5', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '7', '1', '4', '7', '6', '4', '3', '8', '6', '2', '5', '0', '2', '0', '0', '0', '2', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '3', '3', '7', '3', '5', '5', '8', '6', '7', '5', '6', '3', '9', '7', '0', '1', '7', '1', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '4', '3', '2', '5', '0', '3', '9', '9', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '7', '8', '4', '3', '1', '7', '4', '2', '8', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk106Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '0', '6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '0', '8', '2', '0', '2', '6', '6', '7', '7', '1', '8', '9', '6', '3', '6', '1', '4', '2', '0', '2']), .str (String.ofList ['1', '2', '6', '8', '5', '5', '9', '0', '7', '6', '4', '5', '8', '3', '0', '8', '3', '0', '9', '0', '0', '9']), .str (String.ofList ['1', '6', '4', '8', '2', '8', '3', '4', '1', '3', '6', '9', '5', '0', '7', '4', '1', '6', '4', '3', '3']), .str (String.ofList ['7', '0', '6', '7', '4', '3', '3', '4', '6', '7', '9', '8', '6', '3', '6', '3', '3', '8', '3', '9', '2']), .str (String.ofList ['8', '0', '1', '2', '4', '9', '5', '4', '3', '4', '3', '0', '5', '6', '5', '7', '2', '8', '0', '6', '9']), .str (String.ofList ['1', '5', '8', '4', '5', '3', '7', '6', '1', '5', '4', '1', '1', '5', '2', '3', '8', '3', '7', '9', '1', '8']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '7', '9', '4', '5', '9', '1', '7', '5', '2', '5', '6', '6', '0', '6', '0']), .str (String.ofList ['9', '3', '7', '1', '5', '4', '5', '9', '1', '5', '6', '5', '6', '0', '9', '3', '6', '9', '5', '3', '1']), .str (String.ofList ['9', '3', '7', '1', '4', '7', '6', '4', '3', '8', '6', '2', '5', '0', '2', '0', '0', '0', '2', '5', '7']), .str (String.ofList ['1', '5', '9', '3', '3', '7', '3', '5', '5', '8', '6', '7', '5', '6', '3', '9', '7', '0', '1', '7', '1', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '0', '4', '3', '2', '5', '0', '3', '9', '9', '1', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '0', '7', '8', '4', '3', '1', '7', '4', '2', '8', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_106_before_generic"
  err.flush

theorem array_moment_records_chunk_106 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 75)
      (SourceJson.white (momentRecordsChunk106Chars ++ tail)) acc =
      SourceJson.array (fuel + 74) (SourceJson.white tail) (momentRecordsChunk106Push acc) := by rfl

noncomputable def momentRecordsAcc107 : List SourceJson := momentRecordsChunk106Push momentRecordsAcc106

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_106_generic_complete"
  err.flush

noncomputable def momentRecordsChunk107Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '2', '1', '7', '3', '4', '1', '9', '1', '7', '2', '6', '9', '7', '9', '4', '5', '6', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '9', '3', '7', '7', '5', '1', '4', '8', '7', '3', '7', '0', '1', '4', '2', '4', '9', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '7', '1', '4', '2', '8', '7', '5', '7', '5', '7', '7', '4', '0', '1', '2', '6', '8', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '7', '6', '3', '9', '0', '2', '7', '9', '7', '6', '0', '3', '8', '7', '0', '4', '3', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '0', '0', '9', '8', '8', '9', '1', '7', '2', '7', '4', '6', '1', '6', '0', '4', '3', '3', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '8', '7', '3', '7', '6', '4', '0', '6', '5', '1', '5', '3', '0', '1', '6', '3', '0', '5', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '3', '7', '0', '9', '5', '8', '7', '8', '3', '1', '2', '3', '1', '2', '4', '6', '3', '4', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '3', '1', '5', '5', '0', '4', '9', '1', '3', '0', '3', '5', '8', '2', '2', '2', '5', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '2', '8', '1', '8', '1', '1', '8', '6', '7', '2', '7', '3', '4', '6', '8', '4', '7', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '2', '8', '4', '4', '1', '0', '9', '0', '2', '5', '5', '0', '6', '2', '7', '1', '4', '4', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '4', '6', '7', '6', '5', '5', '6', '6', '6', '7', '7', '6', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '5', '5', '7', '2', '8', '2', '3', '6', '6', '8', '9', '4', '3', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk107Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '0', '7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['6', '6', '2', '1', '7', '3', '4', '1', '9', '1', '7', '2', '6', '9', '7', '9', '4', '5', '6', '6', '4']), .str (String.ofList ['6', '7', '9', '3', '7', '7', '5', '1', '4', '8', '7', '3', '7', '0', '1', '4', '2', '4', '9', '9', '6']), .str (String.ofList ['3', '4', '7', '1', '4', '2', '8', '7', '5', '7', '5', '7', '7', '4', '0', '1', '2', '6', '8', '5', '1']), .str (String.ofList ['5', '5', '7', '6', '3', '9', '0', '2', '7', '9', '7', '6', '0', '3', '8', '7', '0', '4', '3', '3', '0']), .str (String.ofList ['2', '1', '0', '0', '9', '8', '8', '9', '1', '7', '2', '7', '4', '6', '1', '6', '0', '4', '3', '3', '8', '6']), .str (String.ofList ['2', '5', '8', '7', '3', '7', '6', '4', '0', '6', '5', '1', '5', '3', '0', '1', '6', '3', '0', '5', '0', '2']), .str (String.ofList ['1', '9', '3', '7', '0', '9', '5', '8', '7', '8', '3', '1', '2', '3', '1', '2', '4', '6', '3', '4', '7', '2']), .str (String.ofList ['9', '1', '3', '1', '5', '5', '0', '4', '9', '1', '3', '0', '3', '5', '8', '2', '2', '2', '5', '7', '3']), .str (String.ofList ['8', '0', '2', '8', '1', '8', '1', '1', '8', '6', '7', '2', '7', '3', '4', '6', '8', '4', '7', '5', '5']), .str (String.ofList ['8', '0', '2', '8', '4', '4', '1', '0', '9', '0', '2', '5', '5', '0', '6', '2', '7', '1', '4', '4', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '4', '6', '7', '6', '5', '5', '6', '6', '6', '7', '7', '6', '4', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '5', '5', '7', '2', '8', '2', '3', '6', '6', '8', '9', '4', '3', '8']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_107_before_generic"
  err.flush

theorem array_moment_records_chunk_107 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 74)
      (SourceJson.white (momentRecordsChunk107Chars ++ tail)) acc =
      SourceJson.array (fuel + 73) (SourceJson.white tail) (momentRecordsChunk107Push acc) := by rfl

noncomputable def momentRecordsAcc108 : List SourceJson := momentRecordsChunk107Push momentRecordsAcc107

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_107_generic_complete"
  err.flush

noncomputable def momentRecordsBlock026Chars : List Char := momentRecordsChunk104Chars ++ momentRecordsChunk105Chars ++ momentRecordsChunk106Chars ++ momentRecordsChunk107Chars
noncomputable def momentRecordsBlock026Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk107Push (momentRecordsChunk106Push (momentRecordsChunk105Push (momentRecordsChunk104Push (acc))))

theorem array_moment_records_block_026 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 77)
      (SourceJson.white (momentRecordsBlock026Chars ++ tail)) acc =
      SourceJson.array (fuel + 73) (SourceJson.white tail) (momentRecordsBlock026Push acc) := by
  have hinput : momentRecordsBlock026Chars ++ tail = momentRecordsChunk104Chars ++ (momentRecordsChunk105Chars ++ (momentRecordsChunk106Chars ++ (momentRecordsChunk107Chars ++ (tail)))) := by
    simp only [momentRecordsBlock026Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 77) (SourceJson.white (momentRecordsBlock026Chars ++ tail)) acc =
        SourceJson.array (fuel + 77) (SourceJson.white (momentRecordsChunk104Chars ++ (momentRecordsChunk105Chars ++ (momentRecordsChunk106Chars ++ (momentRecordsChunk107Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 77) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 76) (SourceJson.white (momentRecordsChunk105Chars ++ (momentRecordsChunk106Chars ++ (momentRecordsChunk107Chars ++ (tail))))) (momentRecordsChunk104Push (acc)) := array_moment_records_chunk_104 fuel (momentRecordsChunk105Chars ++ (momentRecordsChunk106Chars ++ (momentRecordsChunk107Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 75) (SourceJson.white (momentRecordsChunk106Chars ++ (momentRecordsChunk107Chars ++ (tail)))) (momentRecordsChunk105Push (momentRecordsChunk104Push (acc))) := array_moment_records_chunk_105 fuel (momentRecordsChunk106Chars ++ (momentRecordsChunk107Chars ++ (tail))) (momentRecordsChunk104Push (acc))
    _ = SourceJson.array (fuel + 74) (SourceJson.white (momentRecordsChunk107Chars ++ (tail))) (momentRecordsChunk106Push (momentRecordsChunk105Push (momentRecordsChunk104Push (acc)))) := array_moment_records_chunk_106 fuel (momentRecordsChunk107Chars ++ (tail)) (momentRecordsChunk105Push (momentRecordsChunk104Push (acc)))
    _ = SourceJson.array (fuel + 73) (SourceJson.white tail) (momentRecordsBlock026Push acc) := array_moment_records_chunk_107 fuel (tail) (momentRecordsChunk106Push (momentRecordsChunk105Push (momentRecordsChunk104Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_026_before_raw_binding"
  err.flush

theorem moment_records_block_026_prefix :
    (momentRest01 54477).take 2062 = momentRecordsBlock026Chars := by rfl

theorem moment_records_block_026_split :
    momentRest01 54477 = momentRecordsBlock026Chars ++ momentRest01 56539 := by
  calc
    momentRest01 54477 =
        (momentRest01 54477).take 2062 ++ (momentRest01 54477).drop 2062 :=
      (List.take_append_drop 2062 (momentRest01 54477)).symm
    _ = momentRecordsBlock026Chars ++ (momentRest01 54477).drop 2062 :=
      congrArg (fun p => p ++ (momentRest01 54477).drop 2062) moment_records_block_026_prefix
    _ = momentRecordsBlock026Chars ++ momentRest01 56539 :=
      congrArg (fun rest => momentRecordsBlock026Chars ++ rest) (momentRest01_drop 54477 2062)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_026_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_026 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 77)
      (SourceJson.white (momentRest01 54477)) acc =
      SourceJson.array (fuel + 73) (SourceJson.white (momentRest01 56539)) (momentRecordsBlock026Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 77) (SourceJson.white s) acc)
      moment_records_block_026_split).trans (array_moment_records_block_026 fuel (momentRest01 56539) acc)

theorem moment_records_through_block_026 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 73) (SourceJson.white (momentRest01 56539)) momentRecordsAcc108 := by
  exact (moment_records_through_block_025 fuel).trans (array_moment_records_original_block_026 fuel momentRecordsAcc104)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_026_complete"
  err.flush

#print axioms array_moment_records_chunk_104
#print axioms array_moment_records_chunk_105
#print axioms array_moment_records_chunk_106
#print axioms array_moment_records_chunk_107
#print axioms array_moment_records_block_026
#print axioms moment_records_block_026_prefix
#print axioms moment_records_block_026_split
#print axioms array_moment_records_original_block_026
#print axioms moment_records_through_block_026

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
