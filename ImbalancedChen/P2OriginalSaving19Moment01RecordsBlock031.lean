import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock030

/-! Original moment records block 31. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk124Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '3', '3', '0', '1', '2', '4', '4', '8', '9', '2', '9', '6', '5', '5', '7', '7', '9', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '4', '2', '3', '4', '0', '9', '0', '9', '9', '1', '2', '8', '7', '7', '3', '3', '8', '3', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '1', '1', '7', '6', '3', '2', '1', '2', '8', '0', '4', '3', '1', '7', '8', '7', '1', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '8', '1', '7', '5', '7', '7', '5', '0', '1', '1', '1', '6', '7', '7', '3', '9', '0', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '3', '5', '9', '3', '3', '1', '5', '5', '5', '8', '9', '9', '7', '3', '0', '6', '0', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '7', '8', '4', '4', '6', '8', '2', '4', '0', '6', '8', '1', '8', '2', '3', '0', '3', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '1', '9', '2', '0', '0', '0', '1', '0', '4', '0', '8', '0', '4', '5', '0', '1', '5', '5', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '1', '7', '7', '9', '6', '8', '8', '7', '5', '8', '0', '7', '6', '6', '9', '0', '8', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '8', '6', '1', '5', '1', '8', '2', '8', '9', '2', '4', '7', '8', '0', '2', '1', '0', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '8', '6', '4', '4', '8', '8', '2', '4', '4', '1', '9', '5', '4', '2', '6', '5', '5', '5', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '7', '0', '9', '5', '1', '8', '3', '0', '9', '6', '9', '6', '9', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '8', '2', '6', '5', '9', '8', '4', '4', '0', '9', '2', '6', '7', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk124Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '2', '4'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '6', '4', '3', '3', '0', '1', '2', '4', '4', '8', '9', '2', '9', '6', '5', '5', '7', '7', '9', '4', '6']), .str (String.ofList ['1', '7', '4', '2', '3', '4', '0', '9', '0', '9', '9', '1', '2', '8', '7', '7', '3', '3', '8', '3', '2', '7']), .str (String.ofList ['3', '6', '1', '1', '7', '6', '3', '2', '1', '2', '8', '0', '4', '3', '1', '7', '8', '7', '1', '5', '2']), .str (String.ofList ['6', '3', '8', '1', '7', '5', '7', '7', '5', '0', '1', '1', '1', '6', '7', '7', '3', '9', '0', '4', '8']), .str (String.ofList ['7', '5', '3', '5', '9', '3', '3', '1', '5', '5', '5', '8', '9', '9', '7', '3', '0', '6', '0', '1', '9']), .str (String.ofList ['2', '7', '3', '7', '8', '4', '4', '6', '8', '2', '4', '0', '6', '8', '1', '8', '2', '3', '0', '3', '2', '2']), .str (String.ofList ['2', '1', '1', '9', '2', '0', '0', '0', '1', '0', '4', '0', '8', '0', '4', '5', '0', '1', '5', '5', '4', '9']), .str (String.ofList ['1', '1', '1', '1', '7', '7', '9', '6', '8', '8', '7', '5', '8', '0', '7', '6', '6', '9', '0', '8', '8', '6']), .str (String.ofList ['1', '0', '1', '8', '6', '1', '5', '1', '8', '2', '8', '9', '2', '4', '7', '8', '0', '2', '1', '0', '5', '2']), .str (String.ofList ['1', '0', '1', '8', '6', '4', '4', '8', '8', '2', '4', '4', '1', '9', '5', '4', '2', '6', '5', '5', '5', '0'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '7', '0', '9', '5', '1', '8', '3', '0', '9', '6', '9', '6', '9', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '8', '2', '6', '5', '9', '8', '4', '4', '0', '9', '2', '6', '7', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_124_before_generic"
  err.flush

theorem array_moment_records_chunk_124 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 57)
      (SourceJson.white (momentRecordsChunk124Chars ++ tail)) acc =
      SourceJson.array (fuel + 56) (SourceJson.white tail) (momentRecordsChunk124Push acc) := by rfl

noncomputable def momentRecordsAcc125 : List SourceJson := momentRecordsChunk124Push momentRecordsAcc124

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_124_generic_complete"
  err.flush

noncomputable def momentRecordsChunk125Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '5', '0', '0', '7', '1', '9', '4', '2', '8', '5', '0', '7', '0', '0', '7', '8', '9', '4', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '5', '7', '3', '1', '5', '7', '8', '0', '7', '2', '3', '2', '9', '9', '8', '9', '5', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '1', '4', '8', '8', '4', '2', '3', '9', '4', '5', '0', '6', '2', '4', '6', '2', '9', '4', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '7', '8', '1', '3', '1', '8', '9', '1', '4', '7', '9', '9', '0', '2', '0', '6', '0', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '7', '4', '0', '7', '2', '9', '5', '3', '1', '0', '2', '4', '0', '4', '0', '7', '6', '7', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '5', '3', '1', '5', '4', '5', '4', '6', '5', '2', '1', '4', '5', '9', '1', '3', '2', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '5', '8', '7', '2', '5', '7', '5', '8', '6', '9', '4', '9', '5', '3', '4', '6', '5', '6', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '1', '3', '9', '4', '8', '7', '9', '7', '9', '4', '3', '2', '3', '8', '2', '7', '3', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '6', '7', '4', '4', '9', '5', '0', '0', '0', '4', '5', '0', '4', '7', '4', '2', '3', '2', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '6', '7', '4', '8', '7', '1', '4', '9', '8', '2', '9', '0', '3', '0', '0', '6', '6', '2', '8', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '5', '7', '7', '1', '5', '1', '1', '6', '0', '3', '4', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '8', '4', '3', '2', '0', '3', '8', '2', '5', '3', '2', '1', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk125Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '2', '5'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '9', '5', '0', '0', '7', '1', '9', '4', '2', '8', '5', '0', '7', '0', '0', '7', '8', '9', '4', '3', '6']), .str (String.ofList ['2', '0', '8', '5', '7', '3', '1', '5', '7', '8', '0', '7', '2', '3', '2', '9', '9', '8', '9', '5', '2', '0']), .str (String.ofList ['3', '5', '1', '4', '8', '8', '4', '2', '3', '9', '4', '5', '0', '6', '2', '4', '6', '2', '9', '4', '4']), .str (String.ofList ['7', '1', '7', '8', '1', '3', '1', '8', '9', '1', '4', '7', '9', '9', '0', '2', '0', '6', '0', '2', '0']), .str (String.ofList ['8', '7', '7', '4', '0', '7', '2', '9', '5', '3', '1', '0', '2', '4', '0', '4', '0', '7', '6', '7', '9']), .str (String.ofList ['2', '6', '4', '5', '3', '1', '5', '4', '5', '4', '6', '5', '2', '1', '4', '5', '9', '1', '3', '2', '6', '5']), .str (String.ofList ['1', '5', '5', '8', '7', '2', '5', '7', '5', '8', '6', '9', '4', '9', '5', '3', '4', '6', '5', '6', '3', '7']), .str (String.ofList ['1', '2', '4', '1', '3', '9', '4', '8', '7', '9', '7', '9', '4', '3', '2', '3', '8', '2', '7', '3', '2', '4']), .str (String.ofList ['1', '3', '6', '7', '4', '4', '9', '5', '0', '0', '0', '4', '5', '0', '4', '7', '4', '2', '3', '2', '8', '3']), .str (String.ofList ['1', '3', '6', '7', '4', '8', '7', '1', '4', '9', '8', '2', '9', '0', '3', '0', '0', '6', '6', '2', '8', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '2', '5', '7', '7', '1', '5', '1', '1', '6', '0', '3', '4', '1', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '2', '8', '4', '3', '2', '0', '3', '8', '2', '5', '3', '2', '1', '6']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_125_before_generic"
  err.flush

theorem array_moment_records_chunk_125 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 56)
      (SourceJson.white (momentRecordsChunk125Chars ++ tail)) acc =
      SourceJson.array (fuel + 55) (SourceJson.white tail) (momentRecordsChunk125Push acc) := by rfl

noncomputable def momentRecordsAcc126 : List SourceJson := momentRecordsChunk125Push momentRecordsAcc125

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_125_generic_complete"
  err.flush

noncomputable def momentRecordsChunk126Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '8', '6', '4', '5', '0', '1', '1', '2', '8', '1', '5', '2', '6', '5', '3', '7', '1', '4', '4', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '6', '4', '0', '2', '8', '1', '4', '8', '7', '3', '4', '7', '8', '5', '4', '3', '3', '5', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '0', '7', '9', '5', '7', '0', '5', '7', '4', '4', '8', '1', '0', '2', '0', '5', '9', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '0', '3', '3', '1', '8', '9', '2', '9', '7', '2', '9', '9', '9', '0', '4', '5', '9', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '1', '5', '3', '3', '3', '6', '8', '9', '8', '7', '6', '4', '4', '5', '2', '3', '8', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '2', '5', '7', '6', '7', '6', '8', '7', '4', '8', '3', '3', '5', '7', '0', '2', '8', '8', '6', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '4', '4', '6', '8', '3', '6', '0', '3', '8', '8', '4', '5', '4', '3', '7', '3', '6', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '4', '9', '9', '4', '3', '0', '8', '4', '9', '7', '2', '4', '2', '3', '1', '6', '0', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '3', '5', '6', '9', '0', '0', '4', '3', '5', '2', '9', '4', '8', '1', '6', '7', '4', '8', '7', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '3', '5', '7', '3', '4', '1', '7', '2', '1', '0', '7', '2', '9', '3', '8', '9', '8', '9', '9', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '9', '2', '5', '7', '8', '6', '2', '8', '0', '2', '6', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '9', '8', '9', '0', '5', '8', '1', '1', '7', '2', '5', '5', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk126Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '2', '6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '1', '8', '6', '4', '5', '0', '1', '1', '2', '8', '1', '5', '2', '6', '5', '3', '7', '1', '4', '4', '7']), .str (String.ofList ['2', '3', '6', '4', '0', '2', '8', '1', '4', '8', '7', '3', '4', '7', '8', '5', '4', '3', '3', '5', '0', '5']), .str (String.ofList ['3', '4', '0', '7', '9', '5', '7', '0', '5', '7', '4', '4', '8', '1', '0', '2', '0', '5', '9', '2', '8']), .str (String.ofList ['8', '0', '0', '3', '3', '1', '8', '9', '2', '9', '7', '2', '9', '9', '9', '0', '4', '5', '9', '2', '6']), .str (String.ofList ['9', '8', '1', '5', '3', '3', '3', '6', '8', '9', '8', '7', '6', '4', '4', '5', '2', '3', '8', '2', '2']), .str (String.ofList ['2', '5', '2', '5', '7', '6', '7', '6', '8', '7', '4', '8', '3', '3', '5', '7', '0', '2', '8', '8', '6', '6']), .str (String.ofList ['1', '7', '2', '4', '4', '6', '8', '3', '6', '0', '3', '8', '8', '4', '5', '4', '3', '7', '3', '6', '8', '0']), .str (String.ofList ['1', '4', '3', '4', '9', '9', '4', '3', '0', '8', '4', '9', '7', '2', '4', '2', '3', '1', '6', '0', '1', '7']), .str (String.ofList ['1', '5', '3', '5', '6', '9', '0', '0', '4', '3', '5', '2', '9', '4', '8', '1', '6', '7', '4', '8', '7', '9']), .str (String.ofList ['1', '5', '3', '5', '7', '3', '4', '1', '7', '2', '1', '0', '7', '2', '9', '3', '8', '9', '8', '9', '9', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '9', '2', '5', '7', '8', '6', '2', '8', '0', '2', '6', '5', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '9', '8', '9', '0', '5', '8', '1', '1', '7', '2', '5', '5', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_126_before_generic"
  err.flush

theorem array_moment_records_chunk_126 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 55)
      (SourceJson.white (momentRecordsChunk126Chars ++ tail)) acc =
      SourceJson.array (fuel + 54) (SourceJson.white tail) (momentRecordsChunk126Push acc) := by rfl

noncomputable def momentRecordsAcc127 : List SourceJson := momentRecordsChunk126Push momentRecordsAcc126

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_126_generic_complete"
  err.flush

noncomputable def momentRecordsChunk127Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '7', '8', '6', '0', '0', '3', '8', '4', '9', '3', '5', '0', '3', '5', '3', '2', '0', '4', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '0', '3', '1', '3', '4', '6', '5', '7', '4', '4', '3', '9', '3', '6', '4', '5', '2', '8', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '2', '9', '4', '3', '2', '8', '7', '3', '3', '9', '5', '2', '5', '6', '9', '1', '3', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '7', '4', '5', '5', '8', '9', '1', '7', '1', '8', '5', '8', '5', '6', '1', '7', '9', '3', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '6', '2', '3', '3', '2', '0', '4', '2', '4', '2', '3', '6', '5', '7', '3', '0', '5', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '2', '1', '7', '8', '2', '9', '9', '4', '8', '9', '2', '2', '2', '2', '1', '1', '4', '5', '4', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '6', '2', '7', '4', '3', '3', '9', '3', '9', '6', '0', '7', '5', '6', '5', '5', '0', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '8', '8', '6', '8', '1', '1', '5', '4', '3', '4', '8', '2', '6', '4', '2', '7', '1', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '3', '8', '9', '7', '9', '9', '0', '7', '1', '7', '3', '9', '0', '6', '2', '9', '0', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '3', '9', '4', '7', '9', '1', '9', '7', '5', '6', '0', '5', '7', '9', '5', '4', '4', '0', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '3', '1', '3', '5', '5', '2', '0', '1', '6', '6', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '4', '7', '1', '8', '0', '4', '6', '8', '0', '3', '9', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk127Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '2', '7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '3', '7', '8', '6', '0', '0', '3', '8', '4', '9', '3', '5', '0', '3', '5', '3', '2', '0', '4', '8', '8']), .str (String.ofList ['2', '6', '0', '3', '1', '3', '4', '6', '5', '7', '4', '4', '3', '9', '3', '6', '4', '5', '2', '8', '3', '1']), .str (String.ofList ['3', '2', '2', '9', '4', '3', '2', '8', '7', '3', '3', '9', '5', '2', '5', '6', '9', '1', '3', '2', '8']), .str (String.ofList ['8', '7', '7', '4', '5', '5', '8', '9', '1', '7', '1', '8', '5', '8', '5', '6', '1', '7', '9', '3', '3']), .str (String.ofList ['1', '1', '3', '6', '2', '3', '3', '2', '0', '4', '2', '4', '2', '3', '6', '5', '7', '3', '0', '5', '8', '3']), .str (String.ofList ['2', '5', '2', '1', '7', '8', '2', '9', '9', '4', '8', '9', '2', '2', '2', '2', '1', '1', '4', '5', '4', '0']), .str (String.ofList ['1', '9', '0', '6', '2', '7', '4', '3', '3', '9', '3', '9', '6', '0', '7', '5', '6', '5', '5', '0', '1', '9']), .str (String.ofList ['1', '6', '5', '8', '8', '6', '8', '1', '1', '5', '4', '3', '4', '8', '2', '6', '4', '2', '7', '1', '6', '2']), .str (String.ofList ['1', '6', '9', '3', '8', '9', '7', '9', '9', '0', '7', '1', '7', '3', '9', '0', '6', '2', '9', '0', '4', '5']), .str (String.ofList ['1', '6', '9', '3', '9', '4', '7', '9', '1', '9', '7', '5', '6', '0', '5', '7', '9', '5', '4', '4', '0', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '1', '3', '1', '3', '5', '5', '2', '0', '1', '6', '6', '7', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '1', '4', '7', '1', '8', '0', '4', '6', '8', '0', '3', '9', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_127_before_generic"
  err.flush

theorem array_moment_records_chunk_127 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 54)
      (SourceJson.white (momentRecordsChunk127Chars ++ tail)) acc =
      SourceJson.array (fuel + 53) (SourceJson.white tail) (momentRecordsChunk127Push acc) := by rfl

noncomputable def momentRecordsAcc128 : List SourceJson := momentRecordsChunk127Push momentRecordsAcc127

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_127_generic_complete"
  err.flush

noncomputable def momentRecordsBlock031Chars : List Char := momentRecordsChunk124Chars ++ momentRecordsChunk125Chars ++ momentRecordsChunk126Chars ++ momentRecordsChunk127Chars
noncomputable def momentRecordsBlock031Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk127Push (momentRecordsChunk126Push (momentRecordsChunk125Push (momentRecordsChunk124Push (acc))))

theorem array_moment_records_block_031 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 57)
      (SourceJson.white (momentRecordsBlock031Chars ++ tail)) acc =
      SourceJson.array (fuel + 53) (SourceJson.white tail) (momentRecordsBlock031Push acc) := by
  have hinput : momentRecordsBlock031Chars ++ tail = momentRecordsChunk124Chars ++ (momentRecordsChunk125Chars ++ (momentRecordsChunk126Chars ++ (momentRecordsChunk127Chars ++ (tail)))) := by
    simp only [momentRecordsBlock031Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 57) (SourceJson.white (momentRecordsBlock031Chars ++ tail)) acc =
        SourceJson.array (fuel + 57) (SourceJson.white (momentRecordsChunk124Chars ++ (momentRecordsChunk125Chars ++ (momentRecordsChunk126Chars ++ (momentRecordsChunk127Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 57) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 56) (SourceJson.white (momentRecordsChunk125Chars ++ (momentRecordsChunk126Chars ++ (momentRecordsChunk127Chars ++ (tail))))) (momentRecordsChunk124Push (acc)) := array_moment_records_chunk_124 fuel (momentRecordsChunk125Chars ++ (momentRecordsChunk126Chars ++ (momentRecordsChunk127Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 55) (SourceJson.white (momentRecordsChunk126Chars ++ (momentRecordsChunk127Chars ++ (tail)))) (momentRecordsChunk125Push (momentRecordsChunk124Push (acc))) := array_moment_records_chunk_125 fuel (momentRecordsChunk126Chars ++ (momentRecordsChunk127Chars ++ (tail))) (momentRecordsChunk124Push (acc))
    _ = SourceJson.array (fuel + 54) (SourceJson.white (momentRecordsChunk127Chars ++ (tail))) (momentRecordsChunk126Push (momentRecordsChunk125Push (momentRecordsChunk124Push (acc)))) := array_moment_records_chunk_126 fuel (momentRecordsChunk127Chars ++ (tail)) (momentRecordsChunk125Push (momentRecordsChunk124Push (acc)))
    _ = SourceJson.array (fuel + 53) (SourceJson.white tail) (momentRecordsBlock031Push acc) := array_moment_records_chunk_127 fuel (tail) (momentRecordsChunk126Push (momentRecordsChunk125Push (momentRecordsChunk124Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_031_before_raw_binding"
  err.flush

theorem moment_records_block_031_prefix :
    (momentRest01 64797).take 2079 = momentRecordsBlock031Chars := by rfl

theorem moment_records_block_031_split :
    momentRest01 64797 = momentRecordsBlock031Chars ++ momentRest01 66876 := by
  calc
    momentRest01 64797 =
        (momentRest01 64797).take 2079 ++ (momentRest01 64797).drop 2079 :=
      (List.take_append_drop 2079 (momentRest01 64797)).symm
    _ = momentRecordsBlock031Chars ++ (momentRest01 64797).drop 2079 :=
      congrArg (fun p => p ++ (momentRest01 64797).drop 2079) moment_records_block_031_prefix
    _ = momentRecordsBlock031Chars ++ momentRest01 66876 :=
      congrArg (fun rest => momentRecordsBlock031Chars ++ rest) (momentRest01_drop 64797 2079)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_031_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_031 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 57)
      (SourceJson.white (momentRest01 64797)) acc =
      SourceJson.array (fuel + 53) (SourceJson.white (momentRest01 66876)) (momentRecordsBlock031Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 57) (SourceJson.white s) acc)
      moment_records_block_031_split).trans (array_moment_records_block_031 fuel (momentRest01 66876) acc)

theorem moment_records_through_block_031 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 53) (SourceJson.white (momentRest01 66876)) momentRecordsAcc128 := by
  exact (moment_records_through_block_030 fuel).trans (array_moment_records_original_block_031 fuel momentRecordsAcc124)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_031_complete"
  err.flush

#print axioms array_moment_records_chunk_124
#print axioms array_moment_records_chunk_125
#print axioms array_moment_records_chunk_126
#print axioms array_moment_records_chunk_127
#print axioms array_moment_records_block_031
#print axioms moment_records_block_031_prefix
#print axioms moment_records_block_031_split
#print axioms array_moment_records_original_block_031
#print axioms moment_records_through_block_031

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
