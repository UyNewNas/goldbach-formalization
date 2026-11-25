import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock022

/-! Original moment records block 23. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk092Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '7', '1', '9', '7', '9', '2', '9', '3', '1', '1', '6', '4', '4', '0', '8', '9', '0', '7', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '9', '4', '2', '8', '3', '8', '7', '8', '3', '1', '8', '3', '8', '7', '3', '3', '3', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '1', '9', '1', '2', '2', '3', '7', '8', '4', '2', '2', '8', '3', '0', '4', '1', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '6', '5', '5', '0', '4', '1', '3', '6', '5', '5', '6', '8', '9', '9', '8', '8', '4', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '7', '2', '8', '4', '1', '4', '3', '9', '1', '7', '7', '9', '7', '5', '0', '0', '0', '9', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '5', '6', '6', '3', '4', '8', '4', '5', '2', '3', '9', '9', '2', '4', '0', '3', '6', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '0', '1', '9', '5', '0', '2', '9', '0', '7', '1', '9', '9', '1', '2', '4', '0', '4', '0', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '2', '2', '5', '2', '7', '4', '1', '4', '0', '9', '2', '6', '1', '4', '9', '4', '8', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '4', '1', '9', '9', '7', '8', '5', '1', '3', '5', '4', '7', '5', '0', '2', '7', '4', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '4', '3', '1', '1', '3', '9', '1', '6', '8', '7', '9', '4', '6', '6', '8', '4', '6', '7', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '5', '5', '6', '0', '9', '6', '5', '3', '4', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '5', '8', '3', '3', '3', '8', '3', '4', '8', '6', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk092Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['9', '2'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '9', '7', '1', '9', '7', '9', '2', '9', '3', '1', '1', '6', '4', '4', '0', '8', '9', '0', '7', '7', '4']), .str (String.ofList ['1', '9', '2', '9', '4', '2', '8', '3', '8', '7', '8', '3', '1', '8', '3', '8', '7', '3', '3', '3', '3', '6']), .str (String.ofList ['2', '0', '4', '1', '9', '1', '2', '2', '3', '7', '8', '4', '2', '2', '8', '3', '0', '4', '1', '6', '7']), .str (String.ofList ['8', '1', '6', '5', '5', '0', '4', '1', '3', '6', '5', '5', '6', '8', '9', '9', '8', '8', '4', '8', '4']), .str (String.ofList ['1', '0', '2', '7', '2', '8', '4', '1', '4', '3', '9', '1', '7', '7', '9', '7', '5', '0', '0', '0', '9', '4']), .str (String.ofList ['1', '9', '2', '5', '6', '6', '3', '4', '8', '4', '5', '2', '3', '9', '9', '2', '4', '0', '3', '6', '6', '1']), .str (String.ofList ['1', '3', '9', '0', '1', '9', '5', '0', '2', '9', '0', '7', '1', '9', '9', '1', '2', '4', '0', '4', '0', '3']), .str (String.ofList ['1', '2', '6', '2', '2', '5', '2', '7', '4', '1', '4', '0', '9', '2', '6', '1', '4', '9', '4', '8', '0', '8']), .str (String.ofList ['1', '1', '4', '4', '1', '9', '9', '7', '8', '5', '1', '3', '5', '4', '7', '5', '0', '2', '7', '4', '1', '9']), .str (String.ofList ['1', '1', '4', '4', '3', '1', '1', '3', '9', '1', '6', '8', '7', '9', '4', '6', '6', '8', '4', '6', '7', '2'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '5', '5', '6', '0', '9', '6', '5', '3', '4', '6', '9'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '5', '8', '3', '3', '3', '8', '3', '4', '8', '6', '8']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_092_before_generic"
  err.flush

theorem array_moment_records_chunk_092 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 89)
      (SourceJson.white (momentRecordsChunk092Chars ++ tail)) acc =
      SourceJson.array (fuel + 88) (SourceJson.white tail) (momentRecordsChunk092Push acc) := by rfl

noncomputable def momentRecordsAcc093 : List SourceJson := momentRecordsChunk092Push momentRecordsAcc092

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_092_generic_complete"
  err.flush

noncomputable def momentRecordsChunk093Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '1', '4', '6', '7', '9', '5', '2', '9', '6', '5', '9', '3', '4', '1', '5', '2', '0', '4', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '3', '5', '0', '1', '0', '0', '2', '3', '7', '6', '7', '2', '1', '9', '8', '4', '0', '3', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '5', '6', '8', '0', '7', '7', '3', '4', '8', '0', '4', '3', '6', '0', '7', '5', '3', '9', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '7', '8', '6', '2', '4', '2', '3', '2', '1', '1', '3', '2', '2', '7', '3', '9', '8', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '4', '7', '6', '1', '6', '7', '8', '3', '5', '7', '3', '6', '4', '8', '6', '8', '7', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '2', '7', '9', '1', '8', '8', '0', '1', '3', '5', '9', '5', '1', '0', '5', '8', '4', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '9', '6', '5', '6', '4', '0', '4', '6', '3', '7', '5', '3', '7', '0', '5', '3', '3', '4', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '3', '9', '0', '6', '6', '8', '2', '8', '6', '9', '3', '3', '3', '0', '9', '8', '3', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '7', '1', '5', '6', '3', '3', '3', '5', '0', '5', '5', '6', '4', '3', '6', '0', '1', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '2', '7', '1', '1', '6', '8', '8', '5', '3', '6', '7', '7', '5', '4', '0', '6', '5', '0', '8', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '7', '1', '8', '5', '0', '5', '8', '3', '6', '9', '4', '8', '8', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '8', '4', '8', '8', '1', '3', '6', '5', '6', '2', '4', '2', '9', '9', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk093Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['9', '3'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '0', '1', '4', '6', '7', '9', '5', '2', '9', '6', '5', '9', '3', '4', '1', '5', '2', '0', '4', '5', '2']), .str (String.ofList ['2', '1', '3', '5', '0', '1', '0', '0', '2', '3', '7', '6', '7', '2', '1', '9', '8', '4', '0', '3', '8', '3']), .str (String.ofList ['2', '6', '5', '6', '8', '0', '7', '7', '3', '4', '8', '0', '4', '3', '6', '0', '7', '5', '3', '9', '4']), .str (String.ofList ['7', '4', '7', '8', '6', '2', '4', '2', '3', '2', '1', '1', '3', '2', '2', '7', '3', '9', '8', '8', '1']), .str (String.ofList ['1', '4', '2', '4', '7', '6', '1', '6', '7', '8', '3', '5', '7', '3', '6', '4', '8', '6', '8', '7', '6', '2']), .str (String.ofList ['1', '8', '9', '2', '7', '9', '1', '8', '8', '0', '1', '3', '5', '9', '5', '1', '0', '5', '8', '4', '1', '8']), .str (String.ofList ['1', '6', '8', '9', '6', '5', '6', '4', '0', '4', '6', '3', '7', '5', '3', '7', '0', '5', '3', '3', '4', '4']), .str (String.ofList ['1', '4', '9', '3', '9', '0', '6', '6', '8', '2', '8', '6', '9', '3', '3', '3', '0', '9', '8', '3', '3', '7']), .str (String.ofList ['1', '3', '1', '7', '1', '5', '6', '3', '3', '3', '5', '0', '5', '5', '6', '4', '3', '6', '0', '1', '9', '6']), .str (String.ofList ['1', '6', '2', '7', '1', '1', '6', '8', '8', '5', '3', '6', '7', '7', '5', '4', '0', '6', '5', '0', '8', '6'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '7', '1', '8', '5', '0', '5', '8', '3', '6', '9', '4', '8', '8', '5', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '8', '4', '8', '8', '1', '3', '6', '5', '6', '2', '4', '2', '9', '9', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_093_before_generic"
  err.flush

theorem array_moment_records_chunk_093 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 88)
      (SourceJson.white (momentRecordsChunk093Chars ++ tail)) acc =
      SourceJson.array (fuel + 87) (SourceJson.white tail) (momentRecordsChunk093Push acc) := by rfl

noncomputable def momentRecordsAcc094 : List SourceJson := momentRecordsChunk093Push momentRecordsAcc093

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_093_generic_complete"
  err.flush

noncomputable def momentRecordsChunk094Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '1', '1', '2', '0', '9', '3', '1', '4', '7', '5', '0', '9', '6', '0', '9', '7', '5', '3', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '4', '3', '4', '5', '3', '8', '6', '7', '0', '0', '1', '5', '7', '4', '2', '4', '1', '9', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '6', '8', '7', '2', '8', '8', '1', '2', '6', '5', '3', '6', '0', '0', '2', '8', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '9', '6', '0', '7', '3', '6', '8', '1', '9', '6', '0', '5', '5', '6', '3', '1', '6', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '6', '3', '4', '0', '5', '6', '4', '3', '2', '8', '0', '3', '4', '5', '2', '8', '6', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '8', '8', '9', '1', '4', '3', '9', '0', '2', '2', '6', '2', '7', '4', '2', '8', '3', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '8', '1', '3', '1', '5', '5', '5', '7', '3', '1', '3', '0', '1', '0', '8', '0', '5', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '9', '6', '2', '2', '9', '0', '1', '5', '0', '9', '9', '1', '7', '6', '0', '4', '5', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '8', '5', '9', '6', '1', '5', '5', '7', '6', '3', '6', '6', '3', '9', '8', '2', '0', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '5', '8', '3', '6', '7', '1', '6', '2', '5', '5', '6', '6', '9', '8', '0', '8', '9', '2', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '1', '2', '9', '2', '0', '9', '0', '6', '2', '1', '2', '9', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '1', '9', '4', '4', '7', '6', '9', '0', '6', '1', '8', '2', '3', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk094Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['9', '4'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '0', '1', '1', '2', '0', '9', '3', '1', '4', '7', '5', '0', '9', '6', '0', '9', '7', '5', '3', '6', '0']), .str (String.ofList ['1', '9', '4', '3', '4', '5', '3', '8', '6', '7', '0', '0', '1', '5', '7', '4', '2', '4', '1', '9', '1', '2']), .str (String.ofList ['2', '0', '3', '6', '8', '7', '2', '8', '8', '1', '2', '6', '5', '3', '6', '0', '0', '2', '8', '4', '9']), .str (String.ofList ['7', '8', '9', '6', '0', '7', '3', '6', '8', '1', '9', '6', '0', '5', '5', '6', '3', '1', '6', '4', '6']), .str (String.ofList ['1', '0', '2', '6', '3', '4', '0', '5', '6', '4', '3', '2', '8', '0', '3', '4', '5', '2', '8', '6', '7', '6']), .str (String.ofList ['1', '9', '0', '8', '8', '9', '1', '4', '3', '9', '0', '2', '2', '6', '2', '7', '4', '2', '8', '3', '2', '2']), .str (String.ofList ['1', '3', '8', '8', '1', '3', '1', '5', '5', '5', '7', '3', '1', '3', '0', '1', '0', '8', '0', '5', '1', '9']), .str (String.ofList ['1', '2', '5', '9', '6', '2', '2', '9', '0', '1', '5', '0', '9', '9', '1', '7', '6', '0', '4', '5', '6', '7']), .str (String.ofList ['1', '1', '4', '8', '5', '9', '6', '1', '5', '5', '7', '6', '3', '6', '6', '3', '9', '8', '2', '0', '5', '3']), .str (String.ofList ['1', '1', '2', '5', '8', '3', '6', '7', '1', '6', '2', '5', '5', '6', '6', '9', '8', '0', '8', '9', '2', '2'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '1', '2', '9', '2', '0', '9', '0', '6', '2', '1', '2', '9', '4', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '1', '9', '4', '4', '7', '6', '9', '0', '6', '1', '8', '2', '3', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_094_before_generic"
  err.flush

theorem array_moment_records_chunk_094 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 87)
      (SourceJson.white (momentRecordsChunk094Chars ++ tail)) acc =
      SourceJson.array (fuel + 86) (SourceJson.white tail) (momentRecordsChunk094Push acc) := by rfl

noncomputable def momentRecordsAcc095 : List SourceJson := momentRecordsChunk094Push momentRecordsAcc094

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_094_generic_complete"
  err.flush

noncomputable def momentRecordsChunk095Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '4', '5', '6', '9', '5', '8', '1', '1', '2', '7', '0', '0', '2', '8', '7', '6', '5', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '2', '6', '7', '6', '2', '7', '4', '1', '1', '3', '6', '3', '8', '6', '9', '1', '7', '7', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '0', '8', '5', '6', '3', '5', '0', '7', '2', '3', '2', '5', '8', '3', '3', '8', '8', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '5', '9', '6', '9', '3', '3', '4', '0', '2', '4', '6', '6', '5', '6', '9', '4', '3', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '5', '2', '3', '6', '9', '2', '7', '9', '3', '6', '0', '9', '0', '0', '8', '5', '2', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '4', '0', '3', '4', '8', '0', '1', '9', '4', '4', '7', '1', '8', '0', '8', '1', '4', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '6', '5', '6', '1', '0', '2', '4', '4', '4', '7', '8', '4', '1', '6', '7', '4', '0', '2', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '2', '3', '6', '5', '2', '3', '7', '8', '6', '1', '3', '8', '2', '5', '3', '5', '2', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '2', '1', '5', '2', '0', '2', '4', '1', '1', '4', '9', '8', '4', '4', '5', '8', '0', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '9', '9', '7', '4', '7', '2', '4', '2', '6', '3', '3', '3', '0', '5', '4', '8', '8', '1', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '0', '4', '5', '1', '9', '8', '4', '2', '3', '0', '3', '0', '4', '9', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '2', '1', '8', '0', '3', '1', '4', '9', '2', '0', '3', '4', '6', '3', '8', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk095Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['9', '5'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '7', '2', '4', '5', '6', '9', '5', '8', '1', '1', '2', '7', '0', '0', '2', '8', '7', '6', '5', '9', '0']), .str (String.ofList ['1', '8', '2', '6', '7', '6', '2', '7', '4', '1', '1', '3', '6', '3', '8', '6', '9', '1', '7', '7', '0', '9']), .str (String.ofList ['2', '8', '0', '8', '5', '6', '3', '5', '0', '7', '2', '3', '2', '5', '8', '3', '3', '8', '8', '5', '5']), .str (String.ofList ['6', '9', '5', '9', '6', '9', '3', '3', '4', '0', '2', '4', '6', '6', '5', '6', '9', '4', '3', '6', '0']), .str (String.ofList ['1', '4', '2', '5', '2', '3', '6', '9', '2', '7', '9', '3', '6', '0', '9', '0', '0', '8', '5', '2', '4', '3']), .str (String.ofList ['1', '8', '9', '4', '0', '3', '4', '8', '0', '1', '9', '4', '4', '7', '1', '8', '0', '8', '1', '4', '9', '5']), .str (String.ofList ['1', '6', '0', '6', '5', '6', '1', '0', '2', '4', '4', '4', '7', '8', '4', '1', '6', '7', '4', '0', '2', '3']), .str (String.ofList ['1', '3', '7', '2', '3', '6', '5', '2', '3', '7', '8', '6', '1', '3', '8', '2', '5', '3', '5', '2', '8', '4']), .str (String.ofList ['1', '1', '9', '2', '1', '5', '2', '0', '2', '4', '1', '1', '4', '9', '8', '4', '4', '5', '8', '0', '3', '0']), .str (String.ofList ['1', '7', '8', '9', '9', '7', '4', '7', '2', '4', '2', '6', '3', '3', '3', '0', '5', '4', '8', '8', '1', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '5', '0', '4', '5', '1', '9', '8', '4', '2', '3', '0', '3', '0', '4', '9', '6', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '5', '2', '1', '8', '0', '3', '1', '4', '9', '2', '0', '3', '4', '6', '3', '8', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_095_before_generic"
  err.flush

theorem array_moment_records_chunk_095 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 86)
      (SourceJson.white (momentRecordsChunk095Chars ++ tail)) acc =
      SourceJson.array (fuel + 85) (SourceJson.white tail) (momentRecordsChunk095Push acc) := by rfl

noncomputable def momentRecordsAcc096 : List SourceJson := momentRecordsChunk095Push momentRecordsAcc095

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_095_generic_complete"
  err.flush

noncomputable def momentRecordsBlock023Chars : List Char := momentRecordsChunk092Chars ++ momentRecordsChunk093Chars ++ momentRecordsChunk094Chars ++ momentRecordsChunk095Chars
noncomputable def momentRecordsBlock023Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk095Push (momentRecordsChunk094Push (momentRecordsChunk093Push (momentRecordsChunk092Push (acc))))

theorem array_moment_records_block_023 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 89)
      (SourceJson.white (momentRecordsBlock023Chars ++ tail)) acc =
      SourceJson.array (fuel + 85) (SourceJson.white tail) (momentRecordsBlock023Push acc) := by
  have hinput : momentRecordsBlock023Chars ++ tail = momentRecordsChunk092Chars ++ (momentRecordsChunk093Chars ++ (momentRecordsChunk094Chars ++ (momentRecordsChunk095Chars ++ (tail)))) := by
    simp only [momentRecordsBlock023Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 89) (SourceJson.white (momentRecordsBlock023Chars ++ tail)) acc =
        SourceJson.array (fuel + 89) (SourceJson.white (momentRecordsChunk092Chars ++ (momentRecordsChunk093Chars ++ (momentRecordsChunk094Chars ++ (momentRecordsChunk095Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 89) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 88) (SourceJson.white (momentRecordsChunk093Chars ++ (momentRecordsChunk094Chars ++ (momentRecordsChunk095Chars ++ (tail))))) (momentRecordsChunk092Push (acc)) := array_moment_records_chunk_092 fuel (momentRecordsChunk093Chars ++ (momentRecordsChunk094Chars ++ (momentRecordsChunk095Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 87) (SourceJson.white (momentRecordsChunk094Chars ++ (momentRecordsChunk095Chars ++ (tail)))) (momentRecordsChunk093Push (momentRecordsChunk092Push (acc))) := array_moment_records_chunk_093 fuel (momentRecordsChunk094Chars ++ (momentRecordsChunk095Chars ++ (tail))) (momentRecordsChunk092Push (acc))
    _ = SourceJson.array (fuel + 86) (SourceJson.white (momentRecordsChunk095Chars ++ (tail))) (momentRecordsChunk094Push (momentRecordsChunk093Push (momentRecordsChunk092Push (acc)))) := array_moment_records_chunk_094 fuel (momentRecordsChunk095Chars ++ (tail)) (momentRecordsChunk093Push (momentRecordsChunk092Push (acc)))
    _ = SourceJson.array (fuel + 85) (SourceJson.white tail) (momentRecordsBlock023Push acc) := array_moment_records_chunk_095 fuel (tail) (momentRecordsChunk094Push (momentRecordsChunk093Push (momentRecordsChunk092Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_023_before_raw_binding"
  err.flush

theorem moment_records_block_023_prefix :
    (momentRest01 48208).take 2084 = momentRecordsBlock023Chars := by rfl

theorem moment_records_block_023_split :
    momentRest01 48208 = momentRecordsBlock023Chars ++ momentRest01 50292 := by
  calc
    momentRest01 48208 =
        (momentRest01 48208).take 2084 ++ (momentRest01 48208).drop 2084 :=
      (List.take_append_drop 2084 (momentRest01 48208)).symm
    _ = momentRecordsBlock023Chars ++ (momentRest01 48208).drop 2084 :=
      congrArg (fun p => p ++ (momentRest01 48208).drop 2084) moment_records_block_023_prefix
    _ = momentRecordsBlock023Chars ++ momentRest01 50292 :=
      congrArg (fun rest => momentRecordsBlock023Chars ++ rest) (momentRest01_drop 48208 2084)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_023_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_023 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 89)
      (SourceJson.white (momentRest01 48208)) acc =
      SourceJson.array (fuel + 85) (SourceJson.white (momentRest01 50292)) (momentRecordsBlock023Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 89) (SourceJson.white s) acc)
      moment_records_block_023_split).trans (array_moment_records_block_023 fuel (momentRest01 50292) acc)

theorem moment_records_through_block_023 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 85) (SourceJson.white (momentRest01 50292)) momentRecordsAcc096 := by
  exact (moment_records_through_block_022 fuel).trans (array_moment_records_original_block_023 fuel momentRecordsAcc092)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_023_complete"
  err.flush

#print axioms array_moment_records_chunk_092
#print axioms array_moment_records_chunk_093
#print axioms array_moment_records_chunk_094
#print axioms array_moment_records_chunk_095
#print axioms array_moment_records_block_023
#print axioms moment_records_block_023_prefix
#print axioms moment_records_block_023_split
#print axioms array_moment_records_original_block_023
#print axioms moment_records_through_block_023

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
