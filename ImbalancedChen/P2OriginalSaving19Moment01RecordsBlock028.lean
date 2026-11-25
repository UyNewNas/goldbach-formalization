import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock027

/-! Original moment records block 28. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk112Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '7', '2', '0', '0', '5', '7', '9', '2', '0', '6', '2', '2', '3', '7', '9', '6', '2', '4', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '9', '4', '5', '4', '8', '8', '9', '0', '5', '9', '0', '6', '9', '8', '2', '0', '1', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '7', '5', '2', '2', '6', '6', '1', '5', '4', '5', '7', '7', '0', '8', '6', '8', '7', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '5', '7', '6', '9', '2', '5', '6', '9', '3', '3', '0', '0', '3', '1', '5', '7', '5', '8', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '4', '8', '6', '0', '9', '9', '1', '8', '0', '2', '0', '1', '1', '3', '7', '1', '5', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '9', '5', '3', '8', '5', '4', '4', '9', '6', '1', '4', '9', '0', '6', '0', '9', '6', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '0', '1', '9', '4', '6', '1', '1', '2', '5', '4', '4', '9', '6', '5', '6', '8', '6', '8', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '2', '2', '5', '4', '4', '3', '0', '6', '0', '1', '4', '4', '7', '9', '4', '1', '6', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '4', '2', '2', '3', '7', '2', '2', '3', '9', '1', '0', '1', '7', '9', '1', '6', '5', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '4', '3', '1', '5', '3', '8', '0', '4', '7', '7', '8', '4', '9', '3', '0', '7', '1', '4', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '4', '9', '5', '7', '9', '0', '6', '8', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '5', '5', '4', '7', '1', '1', '7', '6', '1', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk112Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '1', '2'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '9', '7', '2', '0', '0', '5', '7', '9', '2', '0', '6', '2', '2', '3', '7', '9', '6', '2', '4', '4', '6']), .str (String.ofList ['1', '9', '2', '9', '4', '5', '4', '8', '8', '9', '0', '5', '9', '0', '6', '9', '8', '2', '0', '1', '5', '3']), .str (String.ofList ['1', '5', '7', '5', '2', '2', '6', '6', '1', '5', '4', '5', '7', '7', '0', '8', '6', '8', '7', '1', '8']), .str (String.ofList ['8', '5', '7', '6', '9', '2', '5', '6', '9', '3', '3', '0', '0', '3', '1', '5', '7', '5', '8', '7', '3']), .str (String.ofList ['1', '3', '2', '4', '8', '6', '0', '9', '9', '1', '8', '0', '2', '0', '1', '1', '3', '7', '1', '5', '1', '4']), .str (String.ofList ['1', '7', '0', '9', '5', '3', '8', '5', '4', '4', '9', '6', '1', '4', '9', '0', '6', '0', '9', '6', '0', '4']), .str (String.ofList ['1', '3', '9', '0', '1', '9', '4', '6', '1', '1', '2', '5', '4', '4', '9', '6', '5', '6', '8', '6', '8', '5']), .str (String.ofList ['1', '2', '6', '2', '2', '5', '4', '4', '3', '0', '6', '0', '1', '4', '4', '7', '9', '4', '1', '6', '4', '5']), .str (String.ofList ['1', '1', '4', '4', '2', '2', '3', '7', '2', '2', '3', '9', '1', '0', '1', '7', '9', '1', '6', '5', '9', '2']), .str (String.ofList ['1', '1', '4', '4', '3', '1', '5', '3', '8', '0', '4', '7', '7', '8', '4', '9', '3', '0', '7', '1', '4', '7'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '4', '9', '5', '7', '9', '0', '6', '8', '3', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '5', '5', '4', '7', '1', '1', '7', '6', '1', '0']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_112_before_generic"
  err.flush

theorem array_moment_records_chunk_112 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 69)
      (SourceJson.white (momentRecordsChunk112Chars ++ tail)) acc =
      SourceJson.array (fuel + 68) (SourceJson.white tail) (momentRecordsChunk112Push acc) := by rfl

noncomputable def momentRecordsAcc113 : List SourceJson := momentRecordsChunk112Push momentRecordsAcc112

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_112_generic_complete"
  err.flush

noncomputable def momentRecordsChunk113Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '0', '7', '9', '0', '1', '3', '0', '1', '2', '2', '0', '2', '4', '8', '8', '5', '0', '3', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '5', '7', '5', '1', '3', '0', '9', '8', '8', '0', '3', '5', '0', '4', '0', '8', '8', '0', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '5', '0', '1', '6', '9', '2', '1', '4', '0', '9', '8', '0', '6', '0', '4', '5', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '5', '9', '8', '6', '2', '7', '1', '8', '9', '8', '8', '1', '1', '5', '7', '1', '2', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '6', '9', '4', '5', '2', '0', '6', '1', '6', '9', '0', '6', '4', '3', '7', '2', '6', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '4', '6', '5', '3', '9', '9', '2', '5', '3', '1', '9', '7', '9', '0', '4', '6', '4', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '0', '7', '9', '0', '2', '6', '4', '0', '9', '4', '7', '8', '8', '1', '3', '9', '9', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '8', '9', '2', '1', '6', '3', '3', '0', '6', '9', '9', '2', '7', '3', '2', '3', '2', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '0', '4', '6', '0', '8', '0', '6', '5', '2', '7', '9', '7', '9', '3', '5', '6', '9', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '8', '6', '6', '0', '1', '4', '2', '9', '4', '2', '4', '7', '5', '9', '2', '2', '3', '0', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '3', '4', '5', '8', '5', '4', '4', '6', '5', '1', '9', '1', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '4', '5', '3', '2', '2', '8', '1', '6', '8', '7', '5', '0', '3', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk113Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '1', '3'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '2', '0', '7', '9', '0', '1', '3', '0', '1', '2', '2', '0', '2', '4', '8', '8', '5', '0', '3', '2']), .str (String.ofList ['1', '2', '8', '5', '7', '5', '1', '3', '0', '9', '8', '8', '0', '3', '5', '0', '4', '0', '8', '8', '0', '3']), .str (String.ofList ['1', '4', '4', '5', '0', '1', '6', '9', '2', '1', '4', '0', '9', '8', '0', '6', '0', '4', '5', '7', '3']), .str (String.ofList ['7', '1', '5', '9', '8', '6', '2', '7', '1', '8', '9', '8', '8', '1', '1', '5', '7', '1', '2', '8', '3']), .str (String.ofList ['8', '0', '6', '9', '4', '5', '2', '0', '6', '1', '6', '9', '0', '6', '4', '3', '7', '2', '6', '9', '0']), .str (String.ofList ['1', '4', '2', '4', '6', '5', '3', '9', '9', '2', '5', '3', '1', '9', '7', '9', '0', '4', '6', '4', '9', '0']), .str (String.ofList ['1', '0', '9', '0', '7', '9', '0', '2', '6', '4', '0', '9', '4', '7', '8', '8', '1', '3', '9', '9', '3', '4']), .str (String.ofList ['9', '8', '8', '9', '2', '1', '6', '3', '3', '0', '6', '9', '9', '2', '7', '3', '2', '3', '2', '4', '3']), .str (String.ofList ['9', '5', '0', '4', '6', '0', '8', '0', '6', '5', '2', '7', '9', '7', '9', '3', '5', '6', '9', '4', '5']), .str (String.ofList ['9', '5', '8', '6', '6', '0', '1', '4', '2', '9', '4', '2', '4', '7', '5', '9', '2', '2', '3', '0', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '3', '3', '4', '5', '8', '5', '4', '4', '6', '5', '1', '9', '1', '8', '7'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '3', '4', '5', '3', '2', '2', '8', '1', '6', '8', '7', '5', '0', '3', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_113_before_generic"
  err.flush

theorem array_moment_records_chunk_113 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 68)
      (SourceJson.white (momentRecordsChunk113Chars ++ tail)) acc =
      SourceJson.array (fuel + 67) (SourceJson.white tail) (momentRecordsChunk113Push acc) := by rfl

noncomputable def momentRecordsAcc114 : List SourceJson := momentRecordsChunk113Push momentRecordsAcc113

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_113_generic_complete"
  err.flush

noncomputable def momentRecordsChunk114Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '0', '2', '8', '5', '1', '2', '8', '8', '6', '2', '0', '2', '1', '3', '1', '4', '3', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '0', '2', '0', '9', '8', '2', '6', '0', '5', '7', '6', '3', '2', '5', '4', '4', '1', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '4', '7', '8', '3', '5', '4', '3', '5', '3', '7', '7', '1', '3', '8', '9', '7', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '9', '2', '2', '4', '5', '0', '8', '5', '6', '1', '1', '4', '5', '9', '3', '9', '3', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '1', '4', '3', '5', '5', '8', '8', '3', '2', '4', '8', '5', '7', '9', '2', '8', '9', '3', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '3', '4', '0', '4', '6', '6', '1', '1', '4', '8', '2', '1', '2', '2', '0', '0', '2', '3', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '6', '1', '3', '4', '8', '5', '2', '2', '7', '2', '9', '5', '8', '8', '2', '1', '6', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '4', '4', '1', '7', '3', '3', '7', '1', '4', '9', '9', '1', '2', '4', '0', '4', '7', '7', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '5', '8', '7', '8', '6', '2', '7', '3', '3', '0', '2', '6', '0', '7', '2', '6', '3', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '5', '9', '5', '4', '8', '3', '0', '1', '8', '5', '1', '9', '3', '0', '6', '3', '1', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '2', '2', '3', '7', '2', '2', '9', '6', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '2', '6', '6', '5', '6', '9', '0', '5', '9', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk114Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '1', '4'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '8', '0', '2', '8', '5', '1', '2', '8', '8', '6', '2', '0', '2', '1', '3', '1', '4', '3', '7', '2']), .str (String.ofList ['1', '3', '5', '0', '2', '0', '9', '8', '2', '6', '0', '5', '7', '6', '3', '2', '5', '4', '4', '1', '8', '3']), .str (String.ofList ['1', '3', '8', '4', '7', '8', '3', '5', '4', '3', '5', '3', '7', '7', '1', '3', '8', '9', '7', '1', '4']), .str (String.ofList ['7', '7', '9', '2', '2', '4', '5', '0', '8', '5', '6', '1', '1', '4', '5', '9', '3', '9', '3', '4', '9']), .str (String.ofList ['7', '9', '1', '4', '3', '5', '5', '8', '8', '3', '2', '4', '8', '5', '7', '9', '2', '8', '9', '3', '2']), .str (String.ofList ['1', '4', '0', '3', '4', '0', '4', '6', '6', '1', '1', '4', '8', '2', '1', '2', '2', '0', '0', '2', '3', '3']), .str (String.ofList ['1', '1', '1', '6', '1', '3', '4', '8', '5', '2', '2', '7', '2', '9', '5', '8', '8', '2', '1', '6', '9', '5']), .str (String.ofList ['1', '0', '2', '4', '4', '1', '7', '3', '3', '7', '1', '4', '9', '9', '1', '2', '4', '0', '4', '7', '7', '7']), .str (String.ofList ['9', '4', '5', '8', '7', '8', '6', '2', '7', '3', '3', '0', '2', '6', '0', '7', '2', '6', '3', '5', '9']), .str (String.ofList ['9', '4', '5', '9', '5', '4', '8', '3', '0', '1', '8', '5', '1', '9', '3', '0', '6', '3', '1', '0', '0'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '2', '2', '3', '7', '2', '2', '9', '6', '5', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '2', '6', '6', '5', '6', '9', '0', '5', '9', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_114_before_generic"
  err.flush

theorem array_moment_records_chunk_114 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 67)
      (SourceJson.white (momentRecordsChunk114Chars ++ tail)) acc =
      SourceJson.array (fuel + 66) (SourceJson.white tail) (momentRecordsChunk114Push acc) := by rfl

noncomputable def momentRecordsAcc115 : List SourceJson := momentRecordsChunk114Push momentRecordsAcc114

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_114_generic_complete"
  err.flush

noncomputable def momentRecordsChunk115Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '6', '4', '2', '6', '9', '1', '9', '4', '6', '0', '0', '1', '7', '2', '0', '9', '6', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '9', '3', '1', '4', '7', '9', '2', '7', '7', '7', '3', '8', '3', '1', '8', '7', '2', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '7', '8', '3', '3', '9', '3', '0', '9', '3', '3', '0', '8', '3', '5', '5', '5', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '0', '7', '5', '9', '5', '2', '3', '3', '6', '5', '2', '7', '4', '4', '5', '3', '3', '9', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '4', '9', '1', '4', '4', '0', '0', '9', '0', '5', '5', '4', '0', '8', '9', '9', '3', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '7', '1', '9', '1', '2', '6', '3', '1', '0', '9', '1', '5', '5', '5', '1', '3', '3', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '4', '9', '3', '8', '1', '4', '9', '2', '0', '6', '4', '6', '7', '2', '0', '3', '3', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '2', '7', '1', '7', '7', '6', '5', '0', '8', '9', '6', '8', '0', '1', '8', '4', '5', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '8', '8', '3', '5', '8', '3', '6', '4', '7', '1', '5', '5', '1', '9', '6', '2', '6', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '4', '1', '0', '7', '0', '8', '8', '3', '0', '9', '6', '0', '5', '0', '9', '7', '1', '9', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '5', '2', '9', '4', '2', '8', '6', '5', '9', '4', '4', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '6', '3', '1', '6', '9', '1', '6', '2', '9', '0', '3', '7', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk115Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '1', '5'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '4', '0', '6', '4', '2', '6', '9', '1', '9', '4', '6', '0', '0', '1', '7', '2', '0', '9', '6', '1', '4']), .str (String.ofList ['1', '3', '5', '9', '3', '1', '4', '7', '9', '2', '7', '7', '7', '3', '8', '3', '1', '8', '7', '2', '4', '1']), .str (String.ofList ['1', '3', '7', '7', '8', '3', '3', '9', '3', '0', '9', '3', '3', '0', '8', '3', '5', '5', '5', '3', '7']), .str (String.ofList ['7', '5', '0', '7', '5', '9', '5', '2', '3', '3', '6', '5', '2', '7', '4', '4', '5', '3', '3', '9', '4']), .str (String.ofList ['7', '9', '4', '9', '1', '4', '4', '0', '0', '9', '0', '5', '5', '4', '0', '8', '9', '9', '3', '6', '9']), .str (String.ofList ['1', '3', '5', '7', '1', '9', '1', '2', '6', '3', '1', '0', '9', '1', '5', '5', '5', '1', '3', '3', '6', '5']), .str (String.ofList ['1', '1', '1', '4', '9', '3', '8', '1', '4', '9', '2', '0', '6', '4', '6', '7', '2', '0', '3', '3', '1', '0']), .str (String.ofList ['1', '0', '2', '2', '7', '1', '7', '7', '6', '5', '0', '8', '9', '6', '8', '0', '1', '8', '4', '5', '9', '6']), .str (String.ofList ['9', '4', '8', '8', '3', '5', '8', '3', '6', '4', '7', '1', '5', '5', '1', '9', '6', '2', '6', '4', '6']), .str (String.ofList ['9', '3', '4', '1', '0', '7', '0', '8', '8', '3', '0', '9', '6', '0', '5', '0', '9', '7', '1', '9', '7'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '2', '5', '2', '9', '4', '2', '8', '6', '5', '9', '4', '4', '9', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '2', '6', '3', '1', '6', '9', '1', '6', '2', '9', '0', '3', '7', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_115_before_generic"
  err.flush

theorem array_moment_records_chunk_115 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 66)
      (SourceJson.white (momentRecordsChunk115Chars ++ tail)) acc =
      SourceJson.array (fuel + 65) (SourceJson.white tail) (momentRecordsChunk115Push acc) := by rfl

noncomputable def momentRecordsAcc116 : List SourceJson := momentRecordsChunk115Push momentRecordsAcc115

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_115_generic_complete"
  err.flush

noncomputable def momentRecordsBlock028Chars : List Char := momentRecordsChunk112Chars ++ momentRecordsChunk113Chars ++ momentRecordsChunk114Chars ++ momentRecordsChunk115Chars
noncomputable def momentRecordsBlock028Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk115Push (momentRecordsChunk114Push (momentRecordsChunk113Push (momentRecordsChunk112Push (acc))))

theorem array_moment_records_block_028 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 69)
      (SourceJson.white (momentRecordsBlock028Chars ++ tail)) acc =
      SourceJson.array (fuel + 65) (SourceJson.white tail) (momentRecordsBlock028Push acc) := by
  have hinput : momentRecordsBlock028Chars ++ tail = momentRecordsChunk112Chars ++ (momentRecordsChunk113Chars ++ (momentRecordsChunk114Chars ++ (momentRecordsChunk115Chars ++ (tail)))) := by
    simp only [momentRecordsBlock028Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 69) (SourceJson.white (momentRecordsBlock028Chars ++ tail)) acc =
        SourceJson.array (fuel + 69) (SourceJson.white (momentRecordsChunk112Chars ++ (momentRecordsChunk113Chars ++ (momentRecordsChunk114Chars ++ (momentRecordsChunk115Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 69) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 68) (SourceJson.white (momentRecordsChunk113Chars ++ (momentRecordsChunk114Chars ++ (momentRecordsChunk115Chars ++ (tail))))) (momentRecordsChunk112Push (acc)) := array_moment_records_chunk_112 fuel (momentRecordsChunk113Chars ++ (momentRecordsChunk114Chars ++ (momentRecordsChunk115Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 67) (SourceJson.white (momentRecordsChunk114Chars ++ (momentRecordsChunk115Chars ++ (tail)))) (momentRecordsChunk113Push (momentRecordsChunk112Push (acc))) := array_moment_records_chunk_113 fuel (momentRecordsChunk114Chars ++ (momentRecordsChunk115Chars ++ (tail))) (momentRecordsChunk112Push (acc))
    _ = SourceJson.array (fuel + 66) (SourceJson.white (momentRecordsChunk115Chars ++ (tail))) (momentRecordsChunk114Push (momentRecordsChunk113Push (momentRecordsChunk112Push (acc)))) := array_moment_records_chunk_114 fuel (momentRecordsChunk115Chars ++ (tail)) (momentRecordsChunk113Push (momentRecordsChunk112Push (acc)))
    _ = SourceJson.array (fuel + 65) (SourceJson.white tail) (momentRecordsBlock028Push acc) := array_moment_records_chunk_115 fuel (tail) (momentRecordsChunk114Push (momentRecordsChunk113Push (momentRecordsChunk112Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_028_before_raw_binding"
  err.flush

theorem moment_records_block_028_prefix :
    (momentRest01 58612).take 2060 = momentRecordsBlock028Chars := by rfl

theorem moment_records_block_028_split :
    momentRest01 58612 = momentRecordsBlock028Chars ++ momentRest01 60672 := by
  calc
    momentRest01 58612 =
        (momentRest01 58612).take 2060 ++ (momentRest01 58612).drop 2060 :=
      (List.take_append_drop 2060 (momentRest01 58612)).symm
    _ = momentRecordsBlock028Chars ++ (momentRest01 58612).drop 2060 :=
      congrArg (fun p => p ++ (momentRest01 58612).drop 2060) moment_records_block_028_prefix
    _ = momentRecordsBlock028Chars ++ momentRest01 60672 :=
      congrArg (fun rest => momentRecordsBlock028Chars ++ rest) (momentRest01_drop 58612 2060)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_028_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_028 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 69)
      (SourceJson.white (momentRest01 58612)) acc =
      SourceJson.array (fuel + 65) (SourceJson.white (momentRest01 60672)) (momentRecordsBlock028Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 69) (SourceJson.white s) acc)
      moment_records_block_028_split).trans (array_moment_records_block_028 fuel (momentRest01 60672) acc)

theorem moment_records_through_block_028 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 65) (SourceJson.white (momentRest01 60672)) momentRecordsAcc116 := by
  exact (moment_records_through_block_027 fuel).trans (array_moment_records_original_block_028 fuel momentRecordsAcc112)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_028_complete"
  err.flush

#print axioms array_moment_records_chunk_112
#print axioms array_moment_records_chunk_113
#print axioms array_moment_records_chunk_114
#print axioms array_moment_records_chunk_115
#print axioms array_moment_records_block_028
#print axioms moment_records_block_028_prefix
#print axioms moment_records_block_028_split
#print axioms array_moment_records_original_block_028
#print axioms moment_records_through_block_028

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
