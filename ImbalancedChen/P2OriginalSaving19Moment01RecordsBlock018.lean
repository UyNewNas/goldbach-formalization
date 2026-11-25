import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock017

/-! Original moment records block 18. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk072Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '6', '8', '1', '0', '8', '4', '8', '6', '0', '0', '3', '6', '2', '0', '2', '2', '2', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '2', '8', '8', '4', '5', '4', '9', '7', '6', '6', '0', '5', '8', '5', '6', '7', '2', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '6', '3', '5', '1', '6', '4', '9', '7', '4', '4', '0', '3', '2', '5', '7', '8', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '5', '3', '3', '3', '7', '0', '5', '1', '4', '9', '9', '7', '1', '2', '7', '6', '4', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '9', '4', '8', '2', '7', '0', '6', '9', '1', '2', '8', '2', '9', '4', '1', '0', '7', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '8', '2', '3', '0', '3', '0', '1', '7', '8', '9', '9', '6', '8', '3', '2', '9', '2', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '2', '6', '9', '8', '1', '4', '0', '0', '7', '6', '5', '2', '0', '4', '8', '5', '2', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '4', '5', '3', '8', '1', '5', '1', '4', '8', '6', '6', '3', '0', '9', '3', '4', '9', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '9', '8', '7', '7', '9', '8', '1', '0', '1', '5', '0', '1', '5', '4', '3', '3', '6', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '9', '9', '4', '4', '8', '3', '5', '3', '7', '6', '7', '8', '1', '0', '7', '2', '2', '8', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '5', '9', '7', '4', '0', '3', '5', '0', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '6', '2', '2', '8', '7', '1', '3', '2', '3', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk072Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['7', '2'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '0', '6', '6', '8', '1', '0', '8', '4', '8', '6', '0', '0', '3', '6', '2', '0', '2', '2', '2', '0', '1']), .str (String.ofList ['1', '0', '6', '2', '8', '8', '4', '5', '4', '9', '7', '6', '6', '0', '5', '8', '5', '6', '7', '2', '5', '6']), .str (String.ofList ['1', '1', '8', '6', '3', '5', '1', '6', '4', '9', '7', '4', '4', '0', '3', '2', '5', '7', '8', '0', '4']), .str (String.ofList ['6', '4', '5', '3', '3', '3', '7', '0', '5', '1', '4', '9', '9', '7', '1', '2', '7', '6', '4', '2', '4']), .str (String.ofList ['1', '2', '5', '9', '4', '8', '2', '7', '0', '6', '9', '1', '2', '8', '2', '9', '4', '1', '0', '7', '4', '9']), .str (String.ofList ['1', '1', '7', '8', '2', '3', '0', '3', '0', '1', '7', '8', '9', '9', '6', '8', '3', '2', '9', '2', '5', '7']), .str (String.ofList ['9', '0', '2', '6', '9', '8', '1', '4', '0', '0', '7', '6', '5', '2', '0', '4', '8', '5', '2', '2', '2']), .str (String.ofList ['8', '1', '4', '5', '3', '8', '1', '5', '1', '4', '8', '6', '6', '3', '0', '9', '3', '4', '9', '4', '5']), .str (String.ofList ['7', '3', '9', '8', '7', '7', '9', '8', '1', '0', '1', '5', '0', '1', '5', '4', '3', '3', '6', '4', '9']), .str (String.ofList ['7', '3', '9', '9', '4', '4', '8', '3', '5', '3', '7', '6', '7', '8', '1', '0', '7', '2', '2', '8', '7'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '5', '9', '7', '4', '0', '3', '5', '0', '8', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '6', '2', '2', '8', '7', '1', '3', '2', '3', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_072_before_generic"
  err.flush

theorem array_moment_records_chunk_072 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 109)
      (SourceJson.white (momentRecordsChunk072Chars ++ tail)) acc =
      SourceJson.array (fuel + 108) (SourceJson.white tail) (momentRecordsChunk072Push acc) := by rfl

noncomputable def momentRecordsAcc073 : List SourceJson := momentRecordsChunk072Push momentRecordsAcc072

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_072_generic_complete"
  err.flush

noncomputable def momentRecordsChunk073Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '5', '3', '3', '5', '7', '0', '3', '9', '3', '6', '1', '8', '3', '8', '4', '3', '2', '2', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '1', '5', '9', '9', '4', '5', '9', '8', '7', '9', '0', '1', '6', '9', '3', '2', '7', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '9', '7', '3', '6', '4', '8', '0', '6', '8', '1', '3', '9', '7', '8', '9', '4', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '9', '0', '1', '0', '4', '5', '2', '7', '1', '1', '8', '3', '3', '4', '3', '8', '6', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '9', '9', '2', '2', '6', '4', '5', '7', '0', '5', '5', '6', '4', '6', '3', '6', '4', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '3', '4', '6', '9', '4', '0', '7', '8', '1', '1', '9', '0', '6', '0', '8', '8', '3', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '1', '5', '8', '2', '3', '3', '5', '1', '3', '1', '4', '0', '4', '8', '4', '8', '1', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '2', '9', '2', '8', '7', '7', '8', '1', '6', '3', '2', '2', '2', '5', '8', '3', '8', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '2', '6', '9', '2', '4', '2', '3', '7', '7', '6', '0', '4', '4', '1', '7', '9', '8', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '8', '7', '4', '8', '9', '9', '1', '1', '2', '5', '9', '7', '8', '7', '6', '8', '2', '1', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '6', '3', '2', '1', '8', '0', '9', '7', '1', '4', '8', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '6', '9', '2', '6', '0', '8', '1', '3', '7', '7', '8', '8', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk073Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['7', '3'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '0', '6', '5', '3', '3', '5', '7', '0', '3', '9', '3', '6', '1', '8', '3', '8', '4', '3', '2', '2', '3']), .str (String.ofList ['1', '0', '6', '1', '5', '9', '9', '4', '5', '9', '8', '7', '9', '0', '1', '6', '9', '3', '2', '7', '7', '0']), .str (String.ofList ['1', '1', '7', '9', '7', '3', '6', '4', '8', '0', '6', '8', '1', '3', '9', '7', '8', '9', '4', '8', '8']), .str (String.ofList ['6', '1', '9', '0', '1', '0', '4', '5', '2', '7', '1', '1', '8', '3', '3', '4', '3', '8', '6', '8', '0']), .str (String.ofList ['1', '2', '4', '9', '9', '2', '2', '6', '4', '5', '7', '0', '5', '5', '6', '4', '6', '3', '6', '4', '3', '4']), .str (String.ofList ['1', '1', '3', '3', '4', '6', '9', '4', '0', '7', '8', '1', '1', '9', '0', '6', '0', '8', '8', '3', '4', '1']), .str (String.ofList ['9', '0', '1', '5', '8', '2', '3', '3', '5', '1', '3', '1', '4', '0', '4', '8', '4', '8', '1', '5', '7']), .str (String.ofList ['8', '1', '2', '9', '2', '8', '7', '7', '8', '1', '6', '3', '2', '2', '2', '5', '8', '3', '8', '9', '6']), .str (String.ofList ['7', '4', '2', '6', '9', '2', '4', '2', '3', '7', '7', '6', '0', '4', '4', '1', '7', '9', '8', '6', '0']), .str (String.ofList ['7', '2', '8', '7', '4', '8', '9', '9', '1', '1', '2', '5', '9', '7', '8', '7', '6', '8', '2', '1', '2'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '6', '3', '2', '1', '8', '0', '9', '7', '1', '4', '8', '2', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '6', '9', '2', '6', '0', '8', '1', '3', '7', '7', '8', '8', '0']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_073_before_generic"
  err.flush

theorem array_moment_records_chunk_073 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 108)
      (SourceJson.white (momentRecordsChunk073Chars ++ tail)) acc =
      SourceJson.array (fuel + 107) (SourceJson.white tail) (momentRecordsChunk073Push acc) := by rfl

noncomputable def momentRecordsAcc074 : List SourceJson := momentRecordsChunk073Push momentRecordsAcc073

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_073_generic_complete"
  err.flush

noncomputable def momentRecordsChunk074Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '5', '4', '2', '6', '6', '3', '9', '4', '4', '6', '2', '2', '2', '8', '3', '9', '4', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '2', '4', '6', '9', '5', '1', '1', '8', '2', '2', '4', '0', '7', '3', '1', '7', '4', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '1', '1', '5', '4', '8', '8', '8', '8', '4', '0', '7', '9', '8', '4', '1', '4', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '4', '5', '2', '6', '6', '1', '9', '5', '4', '8', '4', '1', '4', '5', '2', '0', '2', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '3', '7', '4', '8', '3', '7', '8', '5', '9', '3', '8', '4', '6', '0', '1', '2', '4', '5', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '3', '9', '0', '6', '2', '4', '9', '8', '6', '1', '0', '8', '4', '7', '9', '3', '5', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '6', '5', '2', '3', '7', '5', '6', '3', '8', '0', '9', '3', '2', '3', '1', '7', '3', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '5', '7', '3', '7', '9', '7', '1', '2', '3', '6', '6', '4', '1', '7', '9', '9', '3', '8', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '7', '0', '1', '0', '3', '5', '7', '3', '2', '9', '9', '4', '0', '4', '3', '9', '5', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '0', '6', '8', '4', '1', '2', '6', '8', '9', '1', '2', '3', '3', '5', '4', '3', '4', '1', '5', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '1', '8', '5', '5', '7', '9', '0', '6', '0', '6', '7', '1', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '0', '0', '7', '9', '8', '0', '8', '8', '9', '3', '2', '7', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk074Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['7', '4'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '0', '6', '5', '4', '2', '6', '6', '3', '9', '4', '4', '6', '2', '2', '2', '8', '3', '9', '4', '2', '7']), .str (String.ofList ['1', '0', '6', '2', '4', '6', '9', '5', '1', '1', '8', '2', '2', '4', '0', '7', '3', '1', '7', '4', '4', '2']), .str (String.ofList ['1', '1', '9', '1', '1', '5', '4', '8', '8', '8', '8', '4', '0', '7', '9', '8', '4', '1', '4', '1', '0']), .str (String.ofList ['6', '1', '4', '5', '2', '6', '6', '1', '9', '5', '4', '8', '4', '1', '4', '5', '2', '0', '2', '2', '1']), .str (String.ofList ['1', '2', '3', '7', '4', '8', '3', '7', '8', '5', '9', '3', '8', '4', '6', '0', '1', '2', '4', '5', '9', '5']), .str (String.ofList ['1', '1', '3', '3', '9', '0', '6', '2', '4', '9', '8', '6', '1', '0', '8', '4', '7', '9', '3', '5', '5', '1']), .str (String.ofList ['8', '9', '6', '5', '2', '3', '7', '5', '6', '3', '8', '0', '9', '3', '2', '3', '1', '7', '3', '2', '7']), .str (String.ofList ['8', '0', '5', '7', '3', '7', '9', '7', '1', '2', '3', '6', '6', '4', '1', '7', '9', '9', '3', '8', '9']), .str (String.ofList ['7', '4', '7', '0', '1', '0', '3', '5', '7', '3', '2', '9', '9', '4', '0', '4', '3', '9', '5', '2', '9']), .str (String.ofList ['7', '0', '6', '8', '4', '1', '2', '6', '8', '9', '1', '2', '3', '3', '5', '4', '3', '4', '1', '5', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '1', '8', '5', '5', '7', '9', '0', '6', '0', '6', '7', '1', '3', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '2', '0', '0', '7', '9', '8', '0', '8', '8', '9', '3', '2', '7', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_074_before_generic"
  err.flush

theorem array_moment_records_chunk_074 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 107)
      (SourceJson.white (momentRecordsChunk074Chars ++ tail)) acc =
      SourceJson.array (fuel + 106) (SourceJson.white tail) (momentRecordsChunk074Push acc) := by rfl

noncomputable def momentRecordsAcc075 : List SourceJson := momentRecordsChunk074Push momentRecordsAcc074

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_074_generic_complete"
  err.flush

noncomputable def momentRecordsChunk075Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '7', '6', '4', '7', '1', '2', '9', '8', '0', '1', '6', '3', '4', '0', '0', '9', '3', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '2', '4', '6', '8', '0', '2', '3', '3', '6', '6', '2', '0', '0', '5', '7', '6', '4', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '3', '3', '4', '0', '1', '8', '9', '9', '5', '6', '2', '3', '8', '9', '6', '2', '9', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '7', '9', '0', '0', '3', '0', '7', '9', '3', '6', '5', '0', '0', '7', '2', '9', '0', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '2', '9', '2', '3', '8', '6', '6', '2', '9', '1', '7', '8', '2', '2', '6', '1', '7', '5', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '8', '9', '7', '6', '7', '1', '2', '7', '6', '8', '5', '7', '7', '2', '9', '6', '3', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '0', '2', '6', '7', '2', '9', '2', '1', '7', '6', '2', '1', '3', '1', '3', '5', '3', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '4', '2', '8', '1', '7', '7', '9', '6', '6', '7', '0', '7', '4', '1', '8', '8', '9', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '4', '2', '7', '7', '1', '7', '0', '2', '6', '4', '5', '7', '5', '5', '2', '5', '4', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '9', '5', '8', '0', '9', '7', '9', '2', '7', '2', '9', '9', '9', '2', '5', '0', '0', '9', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '9', '2', '9', '4', '1', '6', '8', '7', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '0', '9', '0', '2', '9', '8', '2', '4', '7', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk075Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['7', '5'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '0', '7', '7', '6', '4', '7', '1', '2', '9', '8', '0', '1', '6', '3', '4', '0', '0', '9', '3', '5', '3']), .str (String.ofList ['1', '0', '7', '2', '4', '6', '8', '0', '2', '3', '3', '6', '6', '2', '0', '0', '5', '7', '6', '4', '9', '2']), .str (String.ofList ['1', '2', '4', '3', '3', '4', '0', '1', '8', '9', '9', '5', '6', '2', '3', '8', '9', '6', '2', '9', '7']), .str (String.ofList ['5', '8', '7', '9', '0', '0', '3', '0', '7', '9', '3', '6', '5', '0', '0', '7', '2', '9', '0', '7', '8']), .str (String.ofList ['1', '2', '0', '2', '9', '2', '3', '8', '6', '6', '2', '9', '1', '7', '8', '2', '2', '6', '1', '7', '5', '8']), .str (String.ofList ['1', '1', '9', '8', '9', '7', '6', '7', '1', '2', '7', '6', '8', '5', '7', '7', '2', '9', '6', '3', '8', '4']), .str (String.ofList ['9', '4', '0', '2', '6', '7', '2', '9', '2', '1', '7', '6', '2', '1', '3', '1', '3', '5', '3', '7', '2']), .str (String.ofList ['7', '4', '4', '2', '8', '1', '7', '7', '9', '6', '6', '7', '0', '7', '4', '1', '8', '8', '9', '6', '5']), .str (String.ofList ['7', '4', '4', '2', '7', '7', '1', '7', '0', '2', '6', '4', '5', '7', '5', '5', '2', '5', '4', '4', '3']), .str (String.ofList ['7', '5', '9', '5', '8', '0', '9', '7', '9', '2', '7', '2', '9', '9', '9', '2', '5', '0', '0', '9', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '2', '9', '2', '9', '4', '1', '6', '8', '7', '5', '5'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '3', '0', '9', '0', '2', '9', '8', '2', '4', '7', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_075_before_generic"
  err.flush

theorem array_moment_records_chunk_075 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 106)
      (SourceJson.white (momentRecordsChunk075Chars ++ tail)) acc =
      SourceJson.array (fuel + 105) (SourceJson.white tail) (momentRecordsChunk075Push acc) := by rfl

noncomputable def momentRecordsAcc076 : List SourceJson := momentRecordsChunk075Push momentRecordsAcc075

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_075_generic_complete"
  err.flush

noncomputable def momentRecordsBlock018Chars : List Char := momentRecordsChunk072Chars ++ momentRecordsChunk073Chars ++ momentRecordsChunk074Chars ++ momentRecordsChunk075Chars
noncomputable def momentRecordsBlock018Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk075Push (momentRecordsChunk074Push (momentRecordsChunk073Push (momentRecordsChunk072Push (acc))))

theorem array_moment_records_block_018 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 109)
      (SourceJson.white (momentRecordsBlock018Chars ++ tail)) acc =
      SourceJson.array (fuel + 105) (SourceJson.white tail) (momentRecordsBlock018Push acc) := by
  have hinput : momentRecordsBlock018Chars ++ tail = momentRecordsChunk072Chars ++ (momentRecordsChunk073Chars ++ (momentRecordsChunk074Chars ++ (momentRecordsChunk075Chars ++ (tail)))) := by
    simp only [momentRecordsBlock018Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 109) (SourceJson.white (momentRecordsBlock018Chars ++ tail)) acc =
        SourceJson.array (fuel + 109) (SourceJson.white (momentRecordsChunk072Chars ++ (momentRecordsChunk073Chars ++ (momentRecordsChunk074Chars ++ (momentRecordsChunk075Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 109) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 108) (SourceJson.white (momentRecordsChunk073Chars ++ (momentRecordsChunk074Chars ++ (momentRecordsChunk075Chars ++ (tail))))) (momentRecordsChunk072Push (acc)) := array_moment_records_chunk_072 fuel (momentRecordsChunk073Chars ++ (momentRecordsChunk074Chars ++ (momentRecordsChunk075Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 107) (SourceJson.white (momentRecordsChunk074Chars ++ (momentRecordsChunk075Chars ++ (tail)))) (momentRecordsChunk073Push (momentRecordsChunk072Push (acc))) := array_moment_records_chunk_073 fuel (momentRecordsChunk074Chars ++ (momentRecordsChunk075Chars ++ (tail))) (momentRecordsChunk072Push (acc))
    _ = SourceJson.array (fuel + 106) (SourceJson.white (momentRecordsChunk075Chars ++ (tail))) (momentRecordsChunk074Push (momentRecordsChunk073Push (momentRecordsChunk072Push (acc)))) := array_moment_records_chunk_074 fuel (momentRecordsChunk075Chars ++ (tail)) (momentRecordsChunk073Push (momentRecordsChunk072Push (acc)))
    _ = SourceJson.array (fuel + 105) (SourceJson.white tail) (momentRecordsBlock018Push acc) := array_moment_records_chunk_075 fuel (tail) (momentRecordsChunk074Push (momentRecordsChunk073Push (momentRecordsChunk072Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_018_before_raw_binding"
  err.flush

theorem moment_records_block_018_prefix :
    (momentRest01 37817).take 2048 = momentRecordsBlock018Chars := by rfl

theorem moment_records_block_018_split :
    momentRest01 37817 = momentRecordsBlock018Chars ++ momentRest01 39865 := by
  calc
    momentRest01 37817 =
        (momentRest01 37817).take 2048 ++ (momentRest01 37817).drop 2048 :=
      (List.take_append_drop 2048 (momentRest01 37817)).symm
    _ = momentRecordsBlock018Chars ++ (momentRest01 37817).drop 2048 :=
      congrArg (fun p => p ++ (momentRest01 37817).drop 2048) moment_records_block_018_prefix
    _ = momentRecordsBlock018Chars ++ momentRest01 39865 :=
      congrArg (fun rest => momentRecordsBlock018Chars ++ rest) (momentRest01_drop 37817 2048)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_018_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_018 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 109)
      (SourceJson.white (momentRest01 37817)) acc =
      SourceJson.array (fuel + 105) (SourceJson.white (momentRest01 39865)) (momentRecordsBlock018Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 109) (SourceJson.white s) acc)
      moment_records_block_018_split).trans (array_moment_records_block_018 fuel (momentRest01 39865) acc)

theorem moment_records_through_block_018 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 105) (SourceJson.white (momentRest01 39865)) momentRecordsAcc076 := by
  exact (moment_records_through_block_017 fuel).trans (array_moment_records_original_block_018 fuel momentRecordsAcc072)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_018_complete"
  err.flush

#print axioms array_moment_records_chunk_072
#print axioms array_moment_records_chunk_073
#print axioms array_moment_records_chunk_074
#print axioms array_moment_records_chunk_075
#print axioms array_moment_records_block_018
#print axioms moment_records_block_018_prefix
#print axioms moment_records_block_018_split
#print axioms array_moment_records_original_block_018
#print axioms moment_records_through_block_018

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
