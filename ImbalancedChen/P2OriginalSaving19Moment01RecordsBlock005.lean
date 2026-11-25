import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock004

/-! Original moment records block 5. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk020Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '7', '2', '2', '4', '5', '9', '7', '2', '2', '1', '4', '2', '9', '4', '7', '2', '9', '7', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '3', '0', '7', '9', '0', '5', '8', '5', '2', '5', '8', '9', '7', '1', '5', '8', '1', '5', '4', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '2', '0', '1', '7', '4', '5', '8', '5', '1', '5', '5', '2', '9', '9', '1', '3', '9', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '2', '3', '8', '7', '6', '7', '0', '3', '3', '3', '7', '7', '7', '1', '8', '8', '0', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '0', '2', '0', '6', '9', '2', '2', '6', '5', '5', '3', '7', '9', '2', '4', '4', '4', '5', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '8', '6', '5', '5', '9', '6', '5', '9', '0', '6', '0', '4', '8', '4', '3', '6', '2', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '6', '0', '8', '7', '3', '7', '4', '3', '0', '1', '1', '1', '8', '2', '7', '9', '1', '7', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '6', '7', '8', '5', '2', '2', '7', '6', '7', '7', '4', '8', '9', '7', '7', '1', '3', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '3', '0', '3', '5', '2', '7', '3', '4', '8', '5', '4', '5', '6', '6', '0', '7', '9', '1', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '2', '9', '9', '7', '9', '2', '5', '5', '5', '9', '0', '8', '5', '5', '5', '8', '0', '7', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '0', '5', '4', '2', '0', '4', '4', '9', '9', '8', '2', '7', '4', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '1', '1', '4', '9', '2', '6', '8', '5', '2', '2', '1', '7', '6', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk020Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['2', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '4', '7', '2', '2', '4', '5', '9', '7', '2', '2', '1', '4', '2', '9', '4', '7', '2', '9', '7', '1', '7']), .str (String.ofList ['1', '5', '3', '0', '7', '9', '0', '5', '8', '5', '2', '5', '8', '9', '7', '1', '5', '8', '1', '5', '4', '7']), .str (String.ofList ['2', '9', '2', '0', '1', '7', '4', '5', '8', '5', '1', '5', '5', '2', '9', '9', '1', '3', '9', '0', '8']), .str (String.ofList ['4', '9', '2', '3', '8', '7', '6', '7', '0', '3', '3', '3', '7', '7', '7', '1', '8', '8', '0', '7', '2']), .str (String.ofList ['7', '0', '2', '0', '6', '9', '2', '2', '6', '5', '5', '3', '7', '9', '2', '4', '4', '4', '5', '6', '4']), .str (String.ofList ['2', '0', '8', '8', '6', '5', '5', '9', '6', '5', '9', '0', '6', '0', '4', '8', '4', '3', '6', '2', '9', '1']), .str (String.ofList ['1', '6', '6', '0', '8', '7', '3', '7', '4', '3', '0', '1', '1', '1', '8', '2', '7', '9', '1', '7', '7', '4']), .str (String.ofList ['1', '0', '3', '6', '7', '8', '5', '2', '2', '7', '6', '7', '7', '4', '8', '9', '7', '7', '1', '3', '6', '3']), .str (String.ofList ['5', '4', '3', '0', '3', '5', '2', '7', '3', '4', '8', '5', '4', '5', '6', '6', '0', '7', '9', '1', '1']), .str (String.ofList ['5', '4', '2', '9', '9', '7', '9', '2', '5', '5', '5', '9', '0', '8', '5', '5', '5', '8', '0', '7', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['7', '0', '5', '4', '2', '0', '4', '4', '9', '9', '8', '2', '7', '4', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['7', '1', '1', '4', '9', '2', '6', '8', '5', '2', '2', '1', '7', '6', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_020_before_generic"
  err.flush

theorem array_moment_records_chunk_020 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 161)
      (SourceJson.white (momentRecordsChunk020Chars ++ tail)) acc =
      SourceJson.array (fuel + 160) (SourceJson.white tail) (momentRecordsChunk020Push acc) := by rfl

noncomputable def momentRecordsAcc021 : List SourceJson := momentRecordsChunk020Push momentRecordsAcc020

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_020_generic_complete"
  err.flush

noncomputable def momentRecordsChunk021Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '0', '6', '4', '0', '7', '9', '1', '8', '8', '8', '9', '0', '4', '6', '0', '0', '6', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '5', '9', '9', '3', '6', '6', '7', '2', '8', '1', '0', '6', '0', '7', '0', '0', '0', '4', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '6', '2', '0', '7', '7', '8', '1', '3', '3', '1', '0', '4', '1', '6', '6', '9', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '8', '0', '4', '4', '6', '8', '3', '6', '2', '0', '5', '6', '7', '4', '2', '4', '9', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '0', '1', '0', '6', '7', '1', '0', '4', '3', '6', '1', '9', '5', '1', '8', '7', '5', '8', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '1', '7', '1', '2', '6', '9', '8', '6', '4', '8', '0', '0', '1', '6', '0', '1', '6', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '2', '4', '4', '7', '0', '8', '9', '4', '3', '1', '5', '7', '0', '1', '6', '3', '5', '2', '0', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '0', '7', '9', '9', '2', '2', '7', '2', '9', '4', '5', '1', '0', '7', '5', '6', '2', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '6', '8', '5', '3', '1', '8', '8', '2', '4', '5', '3', '4', '1', '5', '9', '9', '3', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '9', '2', '8', '1', '6', '5', '8', '4', '3', '7', '9', '0', '6', '3', '3', '8', '9', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '7', '9', '8', '1', '1', '2', '3', '9', '5', '4', '4', '2', '0', '1', '4', '2', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '8', '6', '0', '9', '1', '0', '5', '6', '5', '8', '2', '2', '8', '3', '6', '0', '8', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk021Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['2', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '5', '0', '6', '4', '0', '7', '9', '1', '8', '8', '8', '9', '0', '4', '6', '0', '0', '6', '6', '5']), .str (String.ofList ['1', '4', '4', '5', '9', '9', '3', '6', '6', '7', '2', '8', '1', '0', '6', '0', '7', '0', '0', '0', '4', '7']), .str (String.ofList ['2', '7', '7', '6', '2', '0', '7', '7', '8', '1', '3', '3', '1', '0', '4', '1', '6', '6', '9', '9', '0']), .str (String.ofList ['3', '7', '8', '0', '4', '4', '6', '8', '3', '6', '2', '0', '5', '6', '7', '4', '2', '4', '9', '8', '2']), .str (String.ofList ['7', '0', '1', '0', '6', '7', '1', '0', '4', '3', '6', '1', '9', '5', '1', '8', '7', '5', '8', '1', '3']), .str (String.ofList ['1', '7', '6', '1', '7', '1', '2', '6', '9', '8', '6', '4', '8', '0', '0', '1', '6', '0', '1', '6', '3', '6']), .str (String.ofList ['1', '6', '2', '4', '4', '7', '0', '8', '9', '4', '3', '1', '5', '7', '0', '1', '6', '3', '5', '2', '0', '3']), .str (String.ofList ['1', '0', '3', '0', '7', '9', '9', '2', '2', '7', '2', '9', '4', '5', '1', '0', '7', '5', '6', '2', '5', '6']), .str (String.ofList ['6', '0', '6', '8', '5', '3', '1', '8', '8', '2', '4', '5', '3', '4', '1', '5', '9', '9', '3', '5', '9']), .str (String.ofList ['5', '1', '9', '2', '8', '1', '6', '5', '8', '4', '3', '7', '9', '0', '6', '3', '3', '8', '9', '6', '4'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['7', '7', '9', '8', '1', '1', '2', '3', '9', '5', '4', '4', '2', '0', '1', '4', '2', '9', '6'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['7', '8', '6', '0', '9', '1', '0', '5', '6', '5', '8', '2', '2', '8', '3', '6', '0', '8', '6']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_021_before_generic"
  err.flush

theorem array_moment_records_chunk_021 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 160)
      (SourceJson.white (momentRecordsChunk021Chars ++ tail)) acc =
      SourceJson.array (fuel + 159) (SourceJson.white tail) (momentRecordsChunk021Push acc) := by rfl

noncomputable def momentRecordsAcc022 : List SourceJson := momentRecordsChunk021Push momentRecordsAcc021

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_021_generic_complete"
  err.flush

noncomputable def momentRecordsChunk022Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '3', '1', '7', '7', '7', '3', '4', '7', '7', '3', '6', '3', '9', '5', '8', '1', '3', '7', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '6', '5', '1', '5', '8', '5', '8', '3', '2', '2', '2', '5', '4', '0', '7', '6', '8', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '8', '1', '0', '3', '7', '1', '3', '1', '2', '3', '0', '3', '2', '9', '6', '2', '6', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '3', '9', '7', '4', '6', '9', '4', '7', '6', '2', '9', '0', '0', '9', '8', '4', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '8', '4', '2', '7', '9', '6', '2', '9', '5', '3', '3', '2', '1', '9', '4', '5', '9', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '2', '1', '7', '5', '2', '6', '9', '3', '2', '5', '5', '1', '7', '7', '0', '8', '6', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '5', '3', '1', '7', '1', '8', '7', '9', '8', '9', '3', '4', '9', '5', '5', '3', '5', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '1', '8', '3', '4', '4', '3', '3', '8', '8', '7', '7', '1', '1', '1', '8', '3', '5', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '8', '9', '7', '9', '8', '9', '2', '5', '5', '3', '3', '1', '7', '6', '8', '7', '3', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '2', '2', '1', '4', '1', '1', '5', '8', '9', '1', '5', '4', '3', '9', '5', '4', '2', '9', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '5', '1', '1', '0', '6', '5', '0', '4', '1', '4', '3', '1', '6', '9', '4', '0', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '6', '0', '5', '5', '9', '3', '7', '7', '2', '3', '4', '7', '3', '5', '7', '9', '8', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk022Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['2', '2'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '3', '3', '1', '7', '7', '7', '3', '4', '7', '7', '3', '6', '3', '9', '5', '8', '1', '3', '7', '9']), .str (String.ofList ['1', '3', '9', '6', '5', '1', '5', '8', '5', '8', '3', '2', '2', '2', '5', '4', '0', '7', '6', '8', '3', '7']), .str (String.ofList ['2', '6', '8', '1', '0', '3', '7', '1', '3', '1', '2', '3', '0', '3', '2', '9', '6', '2', '6', '2', '1']), .str (String.ofList ['3', '9', '0', '3', '9', '7', '4', '6', '9', '4', '7', '6', '2', '9', '0', '0', '9', '8', '4', '0', '9']), .str (String.ofList ['7', '2', '8', '4', '2', '7', '9', '6', '2', '9', '5', '3', '3', '2', '1', '9', '4', '5', '9', '3', '7']), .str (String.ofList ['1', '7', '6', '2', '1', '7', '5', '2', '6', '9', '3', '2', '5', '5', '1', '7', '7', '0', '8', '6', '7', '5']), .str (String.ofList ['1', '5', '6', '5', '3', '1', '7', '1', '8', '7', '9', '8', '9', '3', '4', '9', '5', '5', '3', '5', '2', '1']), .str (String.ofList ['1', '0', '9', '1', '8', '3', '4', '4', '3', '3', '8', '8', '7', '7', '1', '1', '1', '8', '3', '5', '8', '8']), .str (String.ofList ['8', '0', '8', '9', '7', '9', '8', '9', '2', '5', '5', '3', '3', '1', '7', '6', '8', '7', '3', '7', '0']), .str (String.ofList ['5', '4', '2', '2', '1', '4', '1', '1', '5', '8', '9', '1', '5', '4', '3', '9', '5', '4', '2', '9', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '1', '5', '1', '1', '0', '6', '5', '0', '4', '1', '4', '3', '1', '6', '9', '4', '0', '1', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '1', '6', '0', '5', '5', '9', '3', '7', '7', '2', '3', '4', '7', '3', '5', '7', '9', '8', '6']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_022_before_generic"
  err.flush

theorem array_moment_records_chunk_022 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 159)
      (SourceJson.white (momentRecordsChunk022Chars ++ tail)) acc =
      SourceJson.array (fuel + 158) (SourceJson.white tail) (momentRecordsChunk022Push acc) := by rfl

noncomputable def momentRecordsAcc023 : List SourceJson := momentRecordsChunk022Push momentRecordsAcc022

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_022_generic_complete"
  err.flush

noncomputable def momentRecordsChunk023Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '7', '8', '2', '4', '7', '7', '0', '3', '5', '1', '9', '2', '7', '2', '5', '9', '6', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '3', '4', '9', '7', '1', '6', '9', '0', '6', '2', '4', '2', '6', '8', '1', '5', '5', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '8', '1', '0', '3', '8', '4', '2', '9', '1', '9', '2', '2', '6', '3', '9', '2', '6', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '2', '9', '5', '5', '1', '6', '1', '2', '3', '2', '8', '1', '5', '5', '5', '5', '3', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '8', '4', '2', '5', '3', '3', '2', '4', '0', '2', '2', '3', '9', '2', '4', '7', '2', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '0', '5', '1', '2', '1', '3', '0', '8', '6', '8', '3', '0', '3', '8', '4', '2', '4', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '6', '6', '4', '9', '3', '1', '3', '1', '3', '0', '6', '7', '1', '5', '7', '4', '2', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '8', '8', '9', '2', '0', '5', '5', '8', '3', '8', '6', '8', '9', '5', '5', '9', '9', '9', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '1', '2', '4', '0', '3', '0', '9', '7', '2', '0', '1', '0', '7', '3', '6', '3', '3', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '9', '3', '9', '5', '5', '2', '2', '7', '4', '1', '7', '8', '0', '3', '6', '6', '8', '0', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '6', '1', '8', '7', '6', '1', '3', '6', '7', '2', '6', '7', '2', '8', '8', '5', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '7', '7', '9', '1', '1', '8', '5', '8', '8', '3', '5', '5', '0', '4', '9', '4', '1', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk023Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['2', '3'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '2', '7', '8', '2', '4', '7', '7', '0', '3', '5', '1', '9', '2', '7', '2', '5', '9', '6', '1', '0']), .str (String.ofList ['1', '4', '1', '3', '4', '9', '7', '1', '6', '9', '0', '6', '2', '4', '2', '6', '8', '1', '5', '5', '5', '2']), .str (String.ofList ['2', '6', '8', '1', '0', '3', '8', '4', '2', '9', '1', '9', '2', '2', '6', '3', '9', '2', '6', '3', '9']), .str (String.ofList ['3', '7', '2', '9', '5', '5', '1', '6', '1', '2', '3', '2', '8', '1', '5', '5', '5', '5', '3', '1', '3']), .str (String.ofList ['7', '6', '8', '4', '2', '5', '3', '3', '2', '4', '0', '2', '2', '3', '9', '2', '4', '7', '2', '4', '2']), .str (String.ofList ['1', '8', '3', '0', '5', '1', '2', '1', '3', '0', '8', '6', '8', '3', '0', '3', '8', '4', '2', '4', '3', '8']), .str (String.ofList ['1', '5', '6', '6', '6', '4', '9', '3', '1', '3', '1', '3', '0', '6', '7', '1', '5', '7', '4', '2', '1', '6']), .str (String.ofList ['1', '1', '3', '8', '8', '9', '2', '0', '5', '5', '8', '3', '8', '6', '8', '9', '5', '5', '9', '9', '9', '9']), .str (String.ofList ['1', '0', '3', '1', '2', '4', '0', '3', '0', '9', '7', '2', '0', '1', '0', '7', '3', '6', '3', '3', '4', '9']), .str (String.ofList ['6', '4', '9', '3', '9', '5', '5', '2', '2', '7', '4', '1', '7', '8', '0', '3', '6', '6', '8', '0', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '8', '6', '1', '8', '7', '6', '1', '3', '6', '7', '2', '6', '7', '2', '8', '8', '5', '3', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '8', '7', '7', '9', '1', '1', '8', '5', '8', '8', '3', '5', '5', '0', '4', '9', '4', '1', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_023_before_generic"
  err.flush

theorem array_moment_records_chunk_023 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 158)
      (SourceJson.white (momentRecordsChunk023Chars ++ tail)) acc =
      SourceJson.array (fuel + 157) (SourceJson.white tail) (momentRecordsChunk023Push acc) := by rfl

noncomputable def momentRecordsAcc024 : List SourceJson := momentRecordsChunk023Push momentRecordsAcc023

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_023_generic_complete"
  err.flush

noncomputable def momentRecordsBlock005Chars : List Char := momentRecordsChunk020Chars ++ momentRecordsChunk021Chars ++ momentRecordsChunk022Chars ++ momentRecordsChunk023Chars
noncomputable def momentRecordsBlock005Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk023Push (momentRecordsChunk022Push (momentRecordsChunk021Push (momentRecordsChunk020Push (acc))))

theorem array_moment_records_block_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 161)
      (SourceJson.white (momentRecordsBlock005Chars ++ tail)) acc =
      SourceJson.array (fuel + 157) (SourceJson.white tail) (momentRecordsBlock005Push acc) := by
  have hinput : momentRecordsBlock005Chars ++ tail = momentRecordsChunk020Chars ++ (momentRecordsChunk021Chars ++ (momentRecordsChunk022Chars ++ (momentRecordsChunk023Chars ++ (tail)))) := by
    simp only [momentRecordsBlock005Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 161) (SourceJson.white (momentRecordsBlock005Chars ++ tail)) acc =
        SourceJson.array (fuel + 161) (SourceJson.white (momentRecordsChunk020Chars ++ (momentRecordsChunk021Chars ++ (momentRecordsChunk022Chars ++ (momentRecordsChunk023Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 161) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 160) (SourceJson.white (momentRecordsChunk021Chars ++ (momentRecordsChunk022Chars ++ (momentRecordsChunk023Chars ++ (tail))))) (momentRecordsChunk020Push (acc)) := array_moment_records_chunk_020 fuel (momentRecordsChunk021Chars ++ (momentRecordsChunk022Chars ++ (momentRecordsChunk023Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 159) (SourceJson.white (momentRecordsChunk022Chars ++ (momentRecordsChunk023Chars ++ (tail)))) (momentRecordsChunk021Push (momentRecordsChunk020Push (acc))) := array_moment_records_chunk_021 fuel (momentRecordsChunk022Chars ++ (momentRecordsChunk023Chars ++ (tail))) (momentRecordsChunk020Push (acc))
    _ = SourceJson.array (fuel + 158) (SourceJson.white (momentRecordsChunk023Chars ++ (tail))) (momentRecordsChunk022Push (momentRecordsChunk021Push (momentRecordsChunk020Push (acc)))) := array_moment_records_chunk_022 fuel (momentRecordsChunk023Chars ++ (tail)) (momentRecordsChunk021Push (momentRecordsChunk020Push (acc)))
    _ = SourceJson.array (fuel + 157) (SourceJson.white tail) (momentRecordsBlock005Push acc) := array_moment_records_chunk_023 fuel (tail) (momentRecordsChunk022Push (momentRecordsChunk021Push (momentRecordsChunk020Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_005_before_raw_binding"
  err.flush

theorem moment_records_block_005_prefix :
    (momentRest01 10792).take 2097 = momentRecordsBlock005Chars := by rfl

theorem moment_records_block_005_split :
    momentRest01 10792 = momentRecordsBlock005Chars ++ momentRest01 12889 := by
  calc
    momentRest01 10792 =
        (momentRest01 10792).take 2097 ++ (momentRest01 10792).drop 2097 :=
      (List.take_append_drop 2097 (momentRest01 10792)).symm
    _ = momentRecordsBlock005Chars ++ (momentRest01 10792).drop 2097 :=
      congrArg (fun p => p ++ (momentRest01 10792).drop 2097) moment_records_block_005_prefix
    _ = momentRecordsBlock005Chars ++ momentRest01 12889 :=
      congrArg (fun rest => momentRecordsBlock005Chars ++ rest) (momentRest01_drop 10792 2097)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_005_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_005 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 161)
      (SourceJson.white (momentRest01 10792)) acc =
      SourceJson.array (fuel + 157) (SourceJson.white (momentRest01 12889)) (momentRecordsBlock005Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 161) (SourceJson.white s) acc)
      moment_records_block_005_split).trans (array_moment_records_block_005 fuel (momentRest01 12889) acc)

theorem moment_records_through_block_005 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 157) (SourceJson.white (momentRest01 12889)) momentRecordsAcc024 := by
  exact (moment_records_through_block_004 fuel).trans (array_moment_records_original_block_005 fuel momentRecordsAcc020)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_005_complete"
  err.flush

#print axioms array_moment_records_chunk_020
#print axioms array_moment_records_chunk_021
#print axioms array_moment_records_chunk_022
#print axioms array_moment_records_chunk_023
#print axioms array_moment_records_block_005
#print axioms moment_records_block_005_prefix
#print axioms moment_records_block_005_split
#print axioms array_moment_records_original_block_005
#print axioms moment_records_through_block_005

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
