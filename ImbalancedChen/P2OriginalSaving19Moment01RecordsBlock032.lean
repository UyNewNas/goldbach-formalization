import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock031

/-! Original moment records block 32. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk128Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '0', '3', '2', '3', '3', '4', '3', '2', '5', '9', '6', '2', '1', '8', '1', '2', '5', '8', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '9', '7', '3', '3', '5', '9', '2', '3', '4', '2', '3', '3', '6', '1', '8', '9', '5', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '9', '6', '3', '5', '3', '1', '5', '6', '4', '2', '4', '1', '3', '1', '2', '8', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '0', '0', '9', '1', '2', '4', '3', '4', '9', '1', '0', '4', '9', '4', '9', '9', '4', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '3', '2', '5', '9', '9', '3', '5', '0', '1', '7', '4', '7', '8', '0', '5', '7', '2', '4', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '4', '6', '8', '5', '6', '7', '4', '3', '3', '2', '7', '8', '7', '4', '4', '9', '4', '3', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '7', '7', '4', '4', '8', '7', '4', '4', '2', '1', '2', '3', '1', '7', '3', '5', '6', '1', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '0', '5', '9', '5', '3', '1', '8', '4', '4', '9', '3', '7', '9', '1', '4', '5', '1', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '9', '8', '0', '3', '6', '3', '2', '8', '9', '9', '3', '3', '7', '9', '8', '1', '2', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '9', '8', '5', '9', '1', '3', '5', '5', '8', '4', '1', '5', '9', '0', '2', '6', '9', '2', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '0', '5', '1', '4', '2', '4', '9', '1', '6', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '4', '5', '0', '8', '2', '8', '8', '3', '7', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk128Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '2', '8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '1', '0', '3', '2', '3', '3', '4', '3', '2', '5', '9', '6', '2', '1', '8', '1', '2', '5', '8', '0', '9']), .str (String.ofList ['2', '0', '6', '9', '7', '3', '3', '5', '9', '2', '3', '4', '2', '3', '3', '6', '1', '8', '9', '5', '0', '7']), .str (String.ofList ['2', '4', '9', '9', '6', '3', '5', '3', '1', '5', '6', '4', '2', '4', '1', '3', '1', '2', '8', '6', '1']), .str (String.ofList ['1', '0', '0', '0', '0', '9', '1', '2', '4', '3', '4', '9', '1', '0', '4', '9', '4', '9', '9', '4', '4', '1']), .str (String.ofList ['1', '1', '9', '3', '2', '5', '9', '9', '3', '5', '0', '1', '7', '4', '7', '8', '0', '5', '7', '2', '4', '7']), .str (String.ofList ['2', '5', '4', '6', '8', '5', '6', '7', '4', '3', '3', '2', '7', '8', '7', '4', '4', '9', '4', '3', '3', '5']), .str (String.ofList ['1', '7', '7', '7', '4', '4', '8', '7', '4', '4', '2', '1', '2', '3', '1', '7', '3', '5', '6', '1', '5', '6']), .str (String.ofList ['1', '6', '1', '0', '5', '9', '5', '3', '1', '8', '4', '4', '9', '3', '7', '9', '1', '4', '5', '1', '6', '7']), .str (String.ofList ['1', '4', '4', '9', '8', '0', '3', '6', '3', '2', '8', '9', '9', '3', '3', '7', '9', '8', '1', '2', '4', '2']), .str (String.ofList ['1', '4', '4', '9', '8', '5', '9', '1', '3', '5', '5', '8', '4', '1', '5', '9', '0', '2', '6', '9', '2', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '1', '0', '5', '1', '4', '2', '4', '9', '1', '6', '5'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '1', '4', '5', '0', '8', '2', '8', '8', '3', '7', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_128_before_generic"
  err.flush

theorem array_moment_records_chunk_128 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 53)
      (SourceJson.white (momentRecordsChunk128Chars ++ tail)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white tail) (momentRecordsChunk128Push acc) := by rfl

noncomputable def momentRecordsAcc129 : List SourceJson := momentRecordsChunk128Push momentRecordsAcc128

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_128_generic_complete"
  err.flush

noncomputable def momentRecordsChunk129Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '1', '7', '6', '7', '6', '4', '3', '0', '7', '9', '2', '1', '1', '8', '7', '4', '4', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '7', '3', '7', '1', '2', '2', '0', '1', '6', '4', '8', '2', '0', '2', '7', '3', '2', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '3', '6', '9', '6', '2', '5', '8', '6', '9', '3', '3', '8', '6', '7', '4', '0', '7', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '4', '9', '5', '3', '1', '1', '2', '9', '0', '8', '8', '6', '1', '5', '8', '8', '8', '6', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '1', '4', '3', '6', '9', '1', '3', '1', '2', '1', '8', '1', '4', '6', '0', '5', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '7', '7', '7', '3', '0', '3', '4', '5', '0', '1', '2', '6', '9', '7', '1', '4', '5', '1', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '0', '9', '0', '8', '2', '5', '3', '1', '0', '9', '8', '9', '3', '5', '2', '4', '4', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '6', '1', '9', '2', '1', '8', '6', '6', '6', '9', '9', '3', '1', '8', '2', '5', '0', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '0', '7', '0', '9', '8', '7', '4', '2', '8', '7', '5', '7', '2', '6', '7', '3', '3', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '0', '7', '6', '6', '8', '6', '0', '9', '0', '6', '4', '5', '5', '8', '4', '7', '5', '5', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '9', '0', '0', '0', '2', '3', '9', '7', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '9', '4', '1', '2', '1', '4', '3', '6', '9', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk129Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '2', '9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '5', '1', '1', '7', '6', '7', '6', '4', '3', '0', '7', '9', '2', '1', '1', '8', '7', '4', '4', '6', '3']), .str (String.ofList ['1', '4', '9', '7', '3', '7', '1', '2', '2', '0', '1', '6', '4', '8', '2', '0', '2', '7', '3', '2', '3', '7']), .str (String.ofList ['1', '6', '9', '3', '6', '9', '6', '2', '5', '8', '6', '9', '3', '3', '8', '6', '7', '4', '0', '7', '9']), .str (String.ofList ['9', '2', '4', '9', '5', '3', '1', '1', '2', '9', '0', '8', '8', '6', '1', '5', '8', '8', '8', '6', '6']), .str (String.ofList ['1', '2', '1', '1', '4', '3', '6', '9', '1', '3', '1', '2', '1', '8', '1', '4', '6', '0', '5', '4', '4', '8']), .str (String.ofList ['1', '8', '7', '7', '7', '3', '0', '3', '4', '5', '0', '1', '2', '6', '9', '7', '1', '4', '5', '1', '4', '1']), .str (String.ofList ['1', '5', '4', '0', '9', '0', '8', '2', '5', '3', '1', '0', '9', '8', '9', '3', '5', '2', '4', '4', '9', '8']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '2', '1', '8', '6', '6', '6', '9', '9', '3', '1', '8', '2', '5', '0', '8', '2']), .str (String.ofList ['1', '2', '8', '0', '7', '0', '9', '8', '7', '4', '2', '8', '7', '5', '7', '2', '6', '7', '3', '3', '2', '8']), .str (String.ofList ['1', '2', '8', '0', '7', '6', '6', '8', '6', '0', '9', '0', '6', '4', '5', '5', '8', '4', '7', '5', '5', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '9', '0', '0', '0', '2', '3', '9', '7', '4', '6'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '9', '4', '1', '2', '1', '4', '3', '6', '9', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_129_before_generic"
  err.flush

theorem array_moment_records_chunk_129 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52)
      (SourceJson.white (momentRecordsChunk129Chars ++ tail)) acc =
      SourceJson.array (fuel + 51) (SourceJson.white tail) (momentRecordsChunk129Push acc) := by rfl

noncomputable def momentRecordsAcc130 : List SourceJson := momentRecordsChunk129Push momentRecordsAcc129

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_129_generic_complete"
  err.flush

noncomputable def momentRecordsChunk130Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '8', '5', '9', '9', '8', '8', '4', '7', '4', '4', '3', '9', '5', '9', '1', '3', '0', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '6', '5', '4', '3', '7', '1', '3', '1', '3', '3', '6', '2', '8', '5', '2', '1', '8', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '8', '7', '0', '8', '0', '7', '6', '1', '5', '2', '5', '6', '6', '8', '7', '4', '2', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '4', '1', '5', '1', '2', '6', '9', '5', '8', '7', '6', '1', '8', '0', '4', '2', '6', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '8', '6', '1', '1', '5', '6', '7', '1', '9', '7', '3', '9', '4', '1', '3', '6', '2', '9', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '2', '0', '7', '9', '6', '0', '6', '6', '6', '1', '8', '7', '6', '0', '2', '7', '9', '9', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '3', '6', '2', '8', '7', '7', '9', '5', '7', '7', '5', '6', '9', '0', '9', '2', '3', '7', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '0', '0', '8', '8', '0', '1', '9', '4', '3', '3', '2', '5', '6', '2', '1', '2', '4', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '8', '0', '0', '4', '2', '0', '3', '0', '4', '2', '5', '1', '9', '6', '8', '6', '5', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '8', '0', '3', '1', '0', '5', '9', '5', '7', '3', '9', '5', '8', '9', '7', '4', '6', '6', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '8', '6', '5', '8', '5', '3', '2', '0', '8', '6', '1', '7', '1', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '9', '6', '1', '7', '1', '4', '7', '2', '2', '4', '4', '4', '3', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk130Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '3', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['6', '0', '8', '5', '9', '9', '8', '8', '4', '7', '4', '4', '3', '9', '5', '9', '1', '3', '0', '1', '8']), .str (String.ofList ['6', '4', '6', '5', '4', '3', '7', '1', '3', '1', '3', '3', '6', '2', '8', '5', '2', '1', '8', '8', '7']), .str (String.ofList ['3', '8', '8', '7', '0', '8', '0', '7', '6', '1', '5', '2', '5', '6', '6', '8', '7', '4', '2', '9', '8']), .str (String.ofList ['6', '8', '4', '1', '5', '1', '2', '6', '9', '5', '8', '7', '6', '1', '8', '0', '4', '2', '6', '5', '7']), .str (String.ofList ['1', '2', '1', '8', '6', '1', '1', '5', '6', '7', '1', '9', '7', '3', '9', '4', '1', '3', '6', '2', '9', '7']), .str (String.ofList ['3', '0', '2', '0', '7', '9', '6', '0', '6', '6', '6', '1', '8', '7', '6', '0', '2', '7', '9', '9', '1', '8']), .str (String.ofList ['2', '2', '3', '6', '2', '8', '7', '7', '9', '5', '7', '7', '5', '6', '9', '0', '9', '2', '3', '7', '2', '0']), .str (String.ofList ['1', '1', '1', '0', '0', '8', '8', '0', '1', '9', '4', '3', '3', '2', '5', '6', '2', '1', '2', '4', '9', '2']), .str (String.ofList ['8', '8', '8', '0', '0', '4', '2', '0', '3', '0', '4', '2', '5', '1', '9', '6', '8', '6', '5', '3', '7']), .str (String.ofList ['8', '8', '8', '0', '3', '1', '0', '5', '9', '5', '7', '3', '9', '5', '8', '9', '7', '4', '6', '6', '7'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '8', '6', '5', '8', '5', '3', '2', '0', '8', '6', '1', '7', '1', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '9', '6', '1', '7', '1', '4', '7', '2', '2', '4', '4', '4', '3', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_130_before_generic"
  err.flush

theorem array_moment_records_chunk_130 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 51)
      (SourceJson.white (momentRecordsChunk130Chars ++ tail)) acc =
      SourceJson.array (fuel + 50) (SourceJson.white tail) (momentRecordsChunk130Push acc) := by rfl

noncomputable def momentRecordsAcc131 : List SourceJson := momentRecordsChunk130Push momentRecordsAcc130

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_130_generic_complete"
  err.flush

noncomputable def momentRecordsChunk131Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '7', '5', '2', '2', '4', '8', '0', '9', '1', '8', '6', '9', '5', '7', '8', '4', '1', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '6', '1', '3', '9', '6', '8', '7', '6', '5', '8', '9', '1', '1', '6', '1', '1', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '7', '7', '9', '2', '8', '9', '7', '8', '3', '7', '3', '1', '3', '2', '1', '7', '5', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '0', '8', '6', '5', '4', '9', '8', '3', '8', '9', '2', '0', '9', '8', '5', '6', '7', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '2', '6', '9', '5', '8', '8', '2', '4', '5', '0', '4', '2', '6', '2', '5', '1', '7', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '1', '9', '6', '9', '0', '1', '1', '8', '9', '2', '1', '6', '4', '5', '3', '0', '9', '8', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '4', '2', '6', '4', '6', '3', '9', '1', '4', '0', '1', '4', '1', '8', '0', '7', '1', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '3', '9', '4', '6', '4', '7', '4', '8', '6', '0', '3', '4', '5', '9', '8', '8', '8', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '4', '4', '0', '1', '6', '0', '4', '8', '3', '7', '1', '1', '0', '3', '3', '5', '6', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '4', '4', '3', '7', '0', '5', '0', '0', '7', '7', '3', '9', '2', '3', '2', '4', '6', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '7', '1', '4', '3', '5', '2', '9', '6', '1', '7', '5', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '9', '3', '8', '9', '6', '5', '7', '0', '2', '1', '1', '5', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk131Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '3', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '0', '1', '7', '5', '2', '2', '4', '8', '0', '9', '1', '8', '6', '9', '5', '7', '8', '4', '1', '1', '6']), .str (String.ofList ['1', '0', '8', '2', '6', '1', '3', '9', '6', '8', '7', '6', '5', '8', '9', '1', '1', '6', '1', '1', '3', '9']), .str (String.ofList ['3', '7', '7', '7', '9', '2', '8', '9', '7', '8', '3', '7', '3', '1', '3', '2', '1', '7', '5', '4', '2']), .str (String.ofList ['7', '7', '0', '8', '6', '5', '4', '9', '8', '3', '8', '9', '2', '0', '9', '8', '5', '6', '7', '7', '1']), .str (String.ofList ['1', '2', '9', '2', '6', '9', '5', '8', '8', '2', '4', '5', '0', '4', '2', '6', '2', '5', '1', '7', '9', '0']), .str (String.ofList ['2', '9', '1', '9', '6', '9', '0', '1', '1', '8', '9', '2', '1', '6', '4', '5', '3', '0', '9', '8', '2', '7']), .str (String.ofList ['1', '6', '4', '4', '2', '6', '4', '6', '3', '9', '1', '4', '0', '1', '4', '1', '8', '0', '7', '1', '6', '7']), .str (String.ofList ['1', '3', '0', '3', '9', '4', '6', '4', '7', '4', '8', '6', '0', '3', '4', '5', '9', '8', '8', '8', '9', '3']), .str (String.ofList ['1', '3', '1', '4', '4', '0', '1', '6', '0', '4', '8', '3', '7', '1', '1', '0', '3', '3', '5', '6', '5', '7']), .str (String.ofList ['1', '3', '1', '4', '4', '3', '7', '0', '5', '0', '0', '7', '7', '3', '9', '2', '3', '2', '4', '6', '0', '0'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '0', '7', '1', '4', '3', '5', '2', '9', '6', '1', '7', '5', '2', '5'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '0', '9', '3', '8', '9', '6', '5', '7', '0', '2', '1', '1', '5', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_131_before_generic"
  err.flush

theorem array_moment_records_chunk_131 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 50)
      (SourceJson.white (momentRecordsChunk131Chars ++ tail)) acc =
      SourceJson.array (fuel + 49) (SourceJson.white tail) (momentRecordsChunk131Push acc) := by rfl

noncomputable def momentRecordsAcc132 : List SourceJson := momentRecordsChunk131Push momentRecordsAcc131

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_131_generic_complete"
  err.flush

noncomputable def momentRecordsBlock032Chars : List Char := momentRecordsChunk128Chars ++ momentRecordsChunk129Chars ++ momentRecordsChunk130Chars ++ momentRecordsChunk131Chars
noncomputable def momentRecordsBlock032Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk131Push (momentRecordsChunk130Push (momentRecordsChunk129Push (momentRecordsChunk128Push (acc))))

theorem array_moment_records_block_032 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 53)
      (SourceJson.white (momentRecordsBlock032Chars ++ tail)) acc =
      SourceJson.array (fuel + 49) (SourceJson.white tail) (momentRecordsBlock032Push acc) := by
  have hinput : momentRecordsBlock032Chars ++ tail = momentRecordsChunk128Chars ++ (momentRecordsChunk129Chars ++ (momentRecordsChunk130Chars ++ (momentRecordsChunk131Chars ++ (tail)))) := by
    simp only [momentRecordsBlock032Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 53) (SourceJson.white (momentRecordsBlock032Chars ++ tail)) acc =
        SourceJson.array (fuel + 53) (SourceJson.white (momentRecordsChunk128Chars ++ (momentRecordsChunk129Chars ++ (momentRecordsChunk130Chars ++ (momentRecordsChunk131Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 53) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 52) (SourceJson.white (momentRecordsChunk129Chars ++ (momentRecordsChunk130Chars ++ (momentRecordsChunk131Chars ++ (tail))))) (momentRecordsChunk128Push (acc)) := array_moment_records_chunk_128 fuel (momentRecordsChunk129Chars ++ (momentRecordsChunk130Chars ++ (momentRecordsChunk131Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 51) (SourceJson.white (momentRecordsChunk130Chars ++ (momentRecordsChunk131Chars ++ (tail)))) (momentRecordsChunk129Push (momentRecordsChunk128Push (acc))) := array_moment_records_chunk_129 fuel (momentRecordsChunk130Chars ++ (momentRecordsChunk131Chars ++ (tail))) (momentRecordsChunk128Push (acc))
    _ = SourceJson.array (fuel + 50) (SourceJson.white (momentRecordsChunk131Chars ++ (tail))) (momentRecordsChunk130Push (momentRecordsChunk129Push (momentRecordsChunk128Push (acc)))) := array_moment_records_chunk_130 fuel (momentRecordsChunk131Chars ++ (tail)) (momentRecordsChunk129Push (momentRecordsChunk128Push (acc)))
    _ = SourceJson.array (fuel + 49) (SourceJson.white tail) (momentRecordsBlock032Push acc) := array_moment_records_chunk_131 fuel (tail) (momentRecordsChunk130Push (momentRecordsChunk129Push (momentRecordsChunk128Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_032_before_raw_binding"
  err.flush

theorem moment_records_block_032_prefix :
    (momentRest01 66876).take 2067 = momentRecordsBlock032Chars := by rfl

theorem moment_records_block_032_split :
    momentRest01 66876 = momentRecordsBlock032Chars ++ momentRest01 68943 := by
  calc
    momentRest01 66876 =
        (momentRest01 66876).take 2067 ++ (momentRest01 66876).drop 2067 :=
      (List.take_append_drop 2067 (momentRest01 66876)).symm
    _ = momentRecordsBlock032Chars ++ (momentRest01 66876).drop 2067 :=
      congrArg (fun p => p ++ (momentRest01 66876).drop 2067) moment_records_block_032_prefix
    _ = momentRecordsBlock032Chars ++ momentRest01 68943 :=
      congrArg (fun rest => momentRecordsBlock032Chars ++ rest) (momentRest01_drop 66876 2067)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_032_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_032 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 53)
      (SourceJson.white (momentRest01 66876)) acc =
      SourceJson.array (fuel + 49) (SourceJson.white (momentRest01 68943)) (momentRecordsBlock032Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 53) (SourceJson.white s) acc)
      moment_records_block_032_split).trans (array_moment_records_block_032 fuel (momentRest01 68943) acc)

theorem moment_records_through_block_032 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 49) (SourceJson.white (momentRest01 68943)) momentRecordsAcc132 := by
  exact (moment_records_through_block_031 fuel).trans (array_moment_records_original_block_032 fuel momentRecordsAcc128)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_032_complete"
  err.flush

#print axioms array_moment_records_chunk_128
#print axioms array_moment_records_chunk_129
#print axioms array_moment_records_chunk_130
#print axioms array_moment_records_chunk_131
#print axioms array_moment_records_block_032
#print axioms moment_records_block_032_prefix
#print axioms moment_records_block_032_split
#print axioms array_moment_records_original_block_032
#print axioms moment_records_through_block_032

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
