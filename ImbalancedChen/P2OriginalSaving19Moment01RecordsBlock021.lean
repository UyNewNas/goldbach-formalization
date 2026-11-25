import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock020

/-! Original moment records block 21. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk084Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '4', '8', '2', '5', '7', '9', '4', '2', '8', '8', '4', '9', '4', '1', '5', '7', '6', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '9', '1', '7', '4', '1', '3', '5', '5', '3', '7', '8', '9', '4', '9', '2', '5', '7', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '5', '7', '8', '8', '6', '3', '3', '8', '3', '0', '1', '4', '4', '6', '1', '8', '7', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '0', '8', '1', '7', '1', '2', '4', '3', '4', '4', '8', '5', '0', '7', '3', '7', '0', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '0', '7', '3', '1', '4', '5', '4', '6', '7', '9', '8', '1', '6', '0', '8', '6', '6', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '7', '4', '8', '1', '7', '9', '8', '7', '5', '1', '3', '3', '9', '8', '9', '5', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '4', '5', '5', '1', '0', '8', '5', '9', '9', '5', '1', '2', '6', '1', '9', '4', '0', '7', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '4', '6', '2', '0', '0', '3', '6', '2', '5', '3', '6', '1', '1', '0', '4', '7', '6', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '0', '9', '2', '1', '5', '0', '1', '5', '1', '5', '7', '2', '5', '5', '7', '6', '5', '9', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '5', '5', '3', '8', '6', '3', '4', '7', '6', '6', '7', '2', '0', '1', '7', '2', '1', '4', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '0', '4', '3', '1', '0', '4', '3', '3', '1', '0', '2', '3', '3', '3', '4', '9', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '0', '7', '0', '8', '2', '2', '7', '8', '1', '8', '4', '8', '2', '1', '3', '4', '1', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk084Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['8', '4'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '0', '0', '4', '8', '2', '5', '7', '9', '4', '2', '8', '8', '4', '9', '4', '1', '5', '7', '6', '3', '8']), .str (String.ofList ['1', '0', '4', '9', '1', '7', '4', '1', '3', '5', '5', '3', '7', '8', '9', '4', '9', '2', '5', '7', '1', '8']), .str (String.ofList ['2', '9', '5', '7', '8', '8', '6', '3', '3', '8', '3', '0', '1', '4', '4', '6', '1', '8', '7', '1', '6']), .str (String.ofList ['5', '7', '0', '8', '1', '7', '1', '2', '4', '3', '4', '4', '8', '5', '0', '7', '3', '7', '0', '0', '1']), .str (String.ofList ['1', '3', '2', '0', '7', '3', '1', '4', '5', '4', '6', '7', '9', '8', '1', '6', '0', '8', '6', '6', '7', '6']), .str (String.ofList ['1', '9', '7', '4', '8', '1', '7', '9', '8', '7', '5', '1', '3', '3', '9', '8', '9', '5', '4', '4', '4', '8']), .str (String.ofList ['1', '3', '0', '4', '5', '5', '1', '0', '8', '5', '9', '9', '5', '1', '2', '6', '1', '9', '4', '0', '7', '7']), .str (String.ofList ['1', '0', '0', '4', '6', '2', '0', '0', '3', '6', '2', '5', '3', '6', '1', '1', '0', '4', '7', '6', '5', '1']), .str (String.ofList ['1', '1', '0', '0', '9', '2', '1', '5', '0', '1', '5', '1', '5', '7', '2', '5', '5', '7', '6', '5', '9', '9']), .str (String.ofList ['1', '3', '3', '5', '5', '3', '8', '6', '3', '4', '7', '6', '6', '7', '2', '0', '1', '7', '2', '1', '4', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '0', '4', '3', '1', '0', '4', '3', '3', '1', '0', '2', '3', '3', '3', '4', '9', '2', '7'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '0', '7', '0', '8', '2', '2', '7', '8', '1', '8', '4', '8', '2', '1', '3', '4', '1', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_084_before_generic"
  err.flush

theorem array_moment_records_chunk_084 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 97)
      (SourceJson.white (momentRecordsChunk084Chars ++ tail)) acc =
      SourceJson.array (fuel + 96) (SourceJson.white tail) (momentRecordsChunk084Push acc) := by rfl

noncomputable def momentRecordsAcc085 : List SourceJson := momentRecordsChunk084Push momentRecordsAcc084

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_084_generic_complete"
  err.flush

noncomputable def momentRecordsChunk085Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '2', '2', '8', '1', '5', '4', '8', '5', '3', '2', '7', '0', '2', '4', '1', '8', '0', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '7', '1', '7', '4', '2', '9', '4', '7', '0', '6', '8', '2', '3', '4', '0', '4', '1', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '5', '7', '8', '8', '7', '8', '3', '9', '0', '0', '3', '0', '9', '9', '9', '7', '8', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '9', '9', '9', '2', '7', '8', '3', '4', '4', '5', '2', '3', '6', '6', '0', '8', '8', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '7', '7', '7', '3', '4', '3', '7', '3', '1', '7', '2', '7', '5', '2', '2', '0', '4', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '0', '6', '3', '2', '9', '3', '7', '0', '9', '7', '3', '3', '0', '0', '7', '1', '2', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '4', '3', '7', '4', '4', '3', '1', '0', '1', '1', '5', '8', '2', '2', '9', '0', '1', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '0', '4', '1', '0', '0', '5', '5', '7', '0', '8', '4', '6', '9', '9', '5', '0', '9', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '6', '1', '1', '8', '3', '4', '7', '5', '4', '9', '0', '8', '3', '1', '5', '8', '6', '3', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '4', '1', '5', '2', '3', '1', '8', '5', '6', '7', '4', '7', '4', '4', '7', '2', '6', '3', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '9', '2', '6', '6', '7', '8', '9', '9', '6', '9', '3', '2', '1', '8', '0', '0', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '9', '7', '2', '9', '3', '9', '8', '9', '8', '0', '2', '4', '7', '9', '2', '2', '5', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk085Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['8', '5'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '0', '2', '2', '2', '8', '1', '5', '4', '8', '5', '3', '2', '7', '0', '2', '4', '1', '8', '0', '6', '3']), .str (String.ofList ['1', '0', '8', '7', '1', '7', '4', '2', '9', '4', '7', '0', '6', '8', '2', '3', '4', '0', '4', '1', '7', '1']), .str (String.ofList ['2', '9', '5', '7', '8', '8', '7', '8', '3', '9', '0', '0', '3', '0', '9', '9', '9', '7', '8', '3', '9']), .str (String.ofList ['5', '5', '9', '9', '9', '2', '7', '8', '3', '4', '4', '5', '2', '3', '6', '6', '0', '8', '8', '2', '0']), .str (String.ofList ['1', '3', '1', '7', '7', '7', '3', '4', '3', '7', '3', '1', '7', '2', '7', '5', '2', '2', '0', '4', '2', '7']), .str (String.ofList ['2', '0', '6', '0', '6', '3', '2', '9', '3', '7', '0', '9', '7', '3', '3', '0', '0', '7', '1', '2', '1', '4']), .str (String.ofList ['1', '3', '1', '4', '3', '7', '4', '4', '3', '1', '0', '1', '1', '5', '8', '2', '2', '9', '0', '1', '1', '7']), .str (String.ofList ['1', '0', '2', '0', '4', '1', '0', '0', '5', '5', '7', '0', '8', '4', '6', '9', '9', '5', '0', '9', '2', '5']), .str (String.ofList ['1', '0', '5', '6', '1', '1', '8', '3', '4', '7', '5', '4', '9', '0', '8', '3', '1', '5', '8', '6', '3', '2']), .str (String.ofList ['1', '5', '6', '4', '1', '5', '2', '3', '1', '8', '5', '6', '7', '4', '7', '4', '4', '7', '2', '6', '3', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '9', '2', '6', '6', '7', '8', '9', '9', '6', '9', '3', '2', '1', '8', '0', '0', '6', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '9', '7', '2', '9', '3', '9', '8', '9', '8', '0', '2', '4', '7', '9', '2', '2', '5', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_085_before_generic"
  err.flush

theorem array_moment_records_chunk_085 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 96)
      (SourceJson.white (momentRecordsChunk085Chars ++ tail)) acc =
      SourceJson.array (fuel + 95) (SourceJson.white tail) (momentRecordsChunk085Push acc) := by rfl

noncomputable def momentRecordsAcc086 : List SourceJson := momentRecordsChunk085Push momentRecordsAcc085

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_085_generic_complete"
  err.flush

noncomputable def momentRecordsChunk086Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '4', '4', '2', '2', '5', '9', '0', '5', '0', '9', '3', '1', '3', '6', '8', '9', '7', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '4', '3', '0', '8', '9', '9', '3', '1', '7', '9', '9', '9', '6', '3', '8', '6', '6', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '8', '0', '5', '9', '7', '4', '9', '7', '2', '3', '8', '5', '8', '0', '9', '7', '6', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '2', '6', '5', '1', '7', '6', '3', '6', '7', '3', '8', '2', '7', '6', '6', '2', '0', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '5', '1', '7', '3', '2', '7', '9', '8', '9', '0', '6', '6', '5', '4', '5', '0', '4', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '1', '0', '6', '7', '0', '2', '3', '6', '6', '4', '1', '7', '1', '5', '3', '5', '1', '0', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '0', '1', '2', '8', '8', '4', '3', '0', '1', '2', '9', '6', '2', '4', '8', '1', '2', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '8', '0', '2', '2', '6', '0', '2', '0', '1', '1', '7', '1', '6', '5', '7', '7', '5', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '7', '1', '2', '9', '3', '3', '3', '9', '9', '4', '6', '9', '9', '9', '3', '4', '6', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '7', '2', '0', '3', '7', '6', '9', '2', '4', '9', '2', '9', '6', '0', '2', '4', '4', '2', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '4', '4', '1', '9', '4', '5', '8', '6', '4', '5', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '8', '8', '9', '9', '2', '5', '4', '7', '5', '5', '8', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk086Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['8', '6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '5', '1', '4', '4', '2', '2', '5', '9', '0', '5', '0', '9', '3', '1', '3', '6', '8', '9', '7', '1', '9']), .str (String.ofList ['1', '5', '8', '4', '3', '0', '8', '9', '9', '3', '1', '7', '9', '9', '9', '6', '3', '8', '6', '6', '0', '6']), .str (String.ofList ['3', '1', '8', '0', '5', '9', '7', '4', '9', '7', '2', '3', '8', '5', '8', '0', '9', '7', '6', '8', '8']), .str (String.ofList ['7', '1', '2', '6', '5', '1', '7', '6', '3', '6', '7', '3', '8', '2', '7', '6', '6', '2', '0', '0', '2']), .str (String.ofList ['1', '4', '1', '5', '1', '7', '3', '2', '7', '9', '8', '9', '0', '6', '6', '5', '4', '5', '0', '4', '2', '9']), .str (String.ofList ['2', '3', '1', '0', '6', '7', '0', '2', '3', '6', '6', '4', '1', '7', '1', '5', '3', '5', '1', '0', '2', '6']), .str (String.ofList ['1', '5', '4', '0', '1', '2', '8', '8', '4', '3', '0', '1', '2', '9', '6', '2', '4', '8', '1', '2', '0', '6']), .str (String.ofList ['1', '2', '4', '8', '0', '2', '2', '6', '0', '2', '0', '1', '1', '7', '1', '6', '5', '7', '7', '5', '3', '7']), .str (String.ofList ['1', '3', '3', '7', '1', '2', '9', '3', '3', '3', '9', '9', '4', '6', '9', '9', '9', '3', '4', '6', '1', '7']), .str (String.ofList ['1', '3', '3', '7', '2', '0', '3', '7', '6', '9', '2', '4', '9', '2', '9', '6', '0', '2', '4', '4', '2', '2'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '0', '4', '4', '1', '9', '4', '5', '8', '6', '4', '5', '2', '5'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '0', '8', '8', '9', '9', '2', '5', '4', '7', '5', '5', '8', '8']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_086_before_generic"
  err.flush

theorem array_moment_records_chunk_086 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 95)
      (SourceJson.white (momentRecordsChunk086Chars ++ tail)) acc =
      SourceJson.array (fuel + 94) (SourceJson.white tail) (momentRecordsChunk086Push acc) := by rfl

noncomputable def momentRecordsAcc087 : List SourceJson := momentRecordsChunk086Push momentRecordsAcc086

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_086_generic_complete"
  err.flush

noncomputable def momentRecordsChunk087Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '6', '4', '3', '2', '1', '4', '8', '9', '9', '9', '1', '7', '2', '7', '4', '8', '1', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '0', '0', '0', '0', '4', '3', '4', '6', '5', '0', '4', '2', '4', '7', '1', '3', '9', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '2', '1', '4', '4', '9', '6', '5', '9', '3', '5', '9', '4', '8', '5', '5', '2', '5', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '3', '6', '6', '8', '8', '7', '3', '3', '7', '7', '3', '8', '3', '3', '6', '9', '1', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '5', '6', '0', '3', '1', '4', '4', '0', '5', '1', '9', '7', '5', '1', '9', '0', '3', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '5', '6', '9', '9', '4', '5', '7', '1', '0', '8', '6', '7', '0', '9', '7', '4', '6', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '0', '6', '1', '8', '1', '9', '1', '3', '5', '5', '5', '1', '3', '4', '2', '6', '2', '4', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '7', '9', '4', '4', '2', '7', '0', '7', '1', '1', '3', '8', '9', '9', '0', '9', '1', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '5', '3', '1', '8', '0', '0', '3', '0', '4', '4', '3', '1', '9', '0', '6', '3', '6', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '6', '2', '5', '2', '2', '8', '2', '9', '1', '0', '7', '2', '2', '8', '7', '4', '2', '5', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '4', '7', '2', '9', '5', '7', '9', '8', '9', '7', '8', '6', '2', '7', '4', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '5', '1', '9', '7', '0', '6', '0', '9', '3', '4', '4', '6', '8', '7', '7', '5', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk087Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['8', '7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '7', '6', '4', '3', '2', '1', '4', '8', '9', '9', '9', '1', '7', '2', '7', '4', '8', '1', '2', '2']), .str (String.ofList ['1', '4', '9', '0', '0', '0', '0', '4', '3', '4', '6', '5', '0', '4', '2', '4', '7', '1', '3', '9', '1', '8']), .str (String.ofList ['3', '0', '2', '1', '4', '4', '9', '6', '5', '9', '3', '5', '9', '4', '8', '5', '5', '2', '5', '1', '4']), .str (String.ofList ['6', '3', '3', '6', '6', '8', '8', '7', '3', '3', '7', '7', '3', '8', '3', '3', '6', '9', '1', '6', '9']), .str (String.ofList ['1', '4', '3', '5', '6', '0', '3', '1', '4', '4', '0', '5', '1', '9', '7', '5', '1', '9', '0', '3', '5', '5']), .str (String.ofList ['1', '8', '9', '5', '6', '9', '9', '4', '5', '7', '1', '0', '8', '6', '7', '0', '9', '7', '4', '6', '1', '3']), .str (String.ofList ['1', '5', '0', '6', '1', '8', '1', '9', '1', '3', '5', '5', '5', '1', '3', '4', '2', '6', '2', '4', '5', '2']), .str (String.ofList ['1', '2', '1', '7', '9', '4', '4', '2', '7', '0', '7', '1', '1', '3', '8', '9', '9', '0', '9', '1', '8', '6']), .str (String.ofList ['1', '2', '8', '5', '3', '1', '8', '0', '0', '3', '0', '4', '4', '3', '1', '9', '0', '6', '3', '6', '5', '9']), .str (String.ofList ['1', '4', '2', '6', '2', '5', '2', '2', '8', '2', '9', '1', '0', '7', '2', '2', '8', '7', '4', '2', '5', '6'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '4', '7', '2', '9', '5', '7', '9', '8', '9', '7', '8', '6', '2', '7', '4', '4', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '5', '1', '9', '7', '0', '6', '0', '9', '3', '4', '4', '6', '8', '7', '7', '5', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_087_before_generic"
  err.flush

theorem array_moment_records_chunk_087 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 94)
      (SourceJson.white (momentRecordsChunk087Chars ++ tail)) acc =
      SourceJson.array (fuel + 93) (SourceJson.white tail) (momentRecordsChunk087Push acc) := by rfl

noncomputable def momentRecordsAcc088 : List SourceJson := momentRecordsChunk087Push momentRecordsAcc087

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_087_generic_complete"
  err.flush

noncomputable def momentRecordsBlock021Chars : List Char := momentRecordsChunk084Chars ++ momentRecordsChunk085Chars ++ momentRecordsChunk086Chars ++ momentRecordsChunk087Chars
noncomputable def momentRecordsBlock021Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk087Push (momentRecordsChunk086Push (momentRecordsChunk085Push (momentRecordsChunk084Push (acc))))

theorem array_moment_records_block_021 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 97)
      (SourceJson.white (momentRecordsBlock021Chars ++ tail)) acc =
      SourceJson.array (fuel + 93) (SourceJson.white tail) (momentRecordsBlock021Push acc) := by
  have hinput : momentRecordsBlock021Chars ++ tail = momentRecordsChunk084Chars ++ (momentRecordsChunk085Chars ++ (momentRecordsChunk086Chars ++ (momentRecordsChunk087Chars ++ (tail)))) := by
    simp only [momentRecordsBlock021Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 97) (SourceJson.white (momentRecordsBlock021Chars ++ tail)) acc =
        SourceJson.array (fuel + 97) (SourceJson.white (momentRecordsChunk084Chars ++ (momentRecordsChunk085Chars ++ (momentRecordsChunk086Chars ++ (momentRecordsChunk087Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 97) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 96) (SourceJson.white (momentRecordsChunk085Chars ++ (momentRecordsChunk086Chars ++ (momentRecordsChunk087Chars ++ (tail))))) (momentRecordsChunk084Push (acc)) := array_moment_records_chunk_084 fuel (momentRecordsChunk085Chars ++ (momentRecordsChunk086Chars ++ (momentRecordsChunk087Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 95) (SourceJson.white (momentRecordsChunk086Chars ++ (momentRecordsChunk087Chars ++ (tail)))) (momentRecordsChunk085Push (momentRecordsChunk084Push (acc))) := array_moment_records_chunk_085 fuel (momentRecordsChunk086Chars ++ (momentRecordsChunk087Chars ++ (tail))) (momentRecordsChunk084Push (acc))
    _ = SourceJson.array (fuel + 94) (SourceJson.white (momentRecordsChunk087Chars ++ (tail))) (momentRecordsChunk086Push (momentRecordsChunk085Push (momentRecordsChunk084Push (acc)))) := array_moment_records_chunk_086 fuel (momentRecordsChunk087Chars ++ (tail)) (momentRecordsChunk085Push (momentRecordsChunk084Push (acc)))
    _ = SourceJson.array (fuel + 93) (SourceJson.white tail) (momentRecordsBlock021Push acc) := array_moment_records_chunk_087 fuel (tail) (momentRecordsChunk086Push (momentRecordsChunk085Push (momentRecordsChunk084Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_021_before_raw_binding"
  err.flush

theorem moment_records_block_021_prefix :
    (momentRest01 44028).take 2100 = momentRecordsBlock021Chars := by rfl

theorem moment_records_block_021_split :
    momentRest01 44028 = momentRecordsBlock021Chars ++ momentRest01 46128 := by
  calc
    momentRest01 44028 =
        (momentRest01 44028).take 2100 ++ (momentRest01 44028).drop 2100 :=
      (List.take_append_drop 2100 (momentRest01 44028)).symm
    _ = momentRecordsBlock021Chars ++ (momentRest01 44028).drop 2100 :=
      congrArg (fun p => p ++ (momentRest01 44028).drop 2100) moment_records_block_021_prefix
    _ = momentRecordsBlock021Chars ++ momentRest01 46128 :=
      congrArg (fun rest => momentRecordsBlock021Chars ++ rest) (momentRest01_drop 44028 2100)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_021_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_021 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 97)
      (SourceJson.white (momentRest01 44028)) acc =
      SourceJson.array (fuel + 93) (SourceJson.white (momentRest01 46128)) (momentRecordsBlock021Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 97) (SourceJson.white s) acc)
      moment_records_block_021_split).trans (array_moment_records_block_021 fuel (momentRest01 46128) acc)

theorem moment_records_through_block_021 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 93) (SourceJson.white (momentRest01 46128)) momentRecordsAcc088 := by
  exact (moment_records_through_block_020 fuel).trans (array_moment_records_original_block_021 fuel momentRecordsAcc084)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_021_complete"
  err.flush

#print axioms array_moment_records_chunk_084
#print axioms array_moment_records_chunk_085
#print axioms array_moment_records_chunk_086
#print axioms array_moment_records_chunk_087
#print axioms array_moment_records_block_021
#print axioms moment_records_block_021_prefix
#print axioms moment_records_block_021_split
#print axioms array_moment_records_original_block_021
#print axioms moment_records_through_block_021

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
