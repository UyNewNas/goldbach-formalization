import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock006

/-! Original moment records block 7. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk028Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '8', '9', '5', '7', '5', '8', '1', '1', '1', '4', '7', '7', '2', '0', '6', '7', '8', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '6', '5', '9', '2', '3', '0', '4', '7', '0', '8', '2', '0', '7', '5', '1', '1', '0', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '2', '0', '0', '8', '0', '8', '7', '8', '8', '1', '8', '0', '2', '7', '1', '0', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '3', '2', '3', '4', '1', '4', '1', '5', '9', '7', '6', '7', '2', '3', '9', '6', '9', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '5', '1', '9', '0', '0', '3', '5', '5', '6', '8', '0', '0', '1', '6', '3', '1', '2', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '3', '7', '2', '5', '0', '4', '9', '0', '0', '9', '6', '7', '0', '2', '8', '8', '8', '7', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '6', '0', '9', '5', '2', '2', '6', '0', '6', '0', '5', '7', '4', '4', '6', '7', '2', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '9', '4', '4', '4', '2', '6', '9', '3', '8', '4', '5', '1', '1', '0', '6', '5', '2', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '9', '4', '9', '8', '9', '0', '4', '8', '0', '7', '5', '9', '8', '2', '6', '8', '6', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '6', '5', '8', '1', '9', '7', '3', '2', '5', '6', '0', '2', '8', '4', '0', '8', '2', '2', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '6', '1', '5', '0', '3', '7', '8', '2', '1', '7', '2', '8', '9', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '6', '9', '0', '3', '8', '3', '1', '4', '0', '2', '3', '0', '3', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk028Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['2', '8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '4', '5', '8', '9', '5', '7', '5', '8', '1', '1', '1', '4', '7', '7', '2', '0', '6', '7', '8', '0', '7']), .str (String.ofList ['1', '5', '9', '6', '5', '9', '2', '3', '0', '4', '7', '0', '8', '2', '0', '7', '5', '1', '1', '0', '5', '9']), .str (String.ofList ['2', '6', '4', '2', '0', '0', '8', '0', '8', '7', '8', '8', '1', '8', '0', '2', '7', '1', '0', '2', '8']), .str (String.ofList ['3', '7', '3', '2', '3', '4', '1', '4', '1', '5', '9', '7', '6', '7', '2', '3', '9', '6', '9', '3', '8']), .str (String.ofList ['6', '6', '5', '1', '9', '0', '0', '3', '5', '5', '6', '8', '0', '0', '1', '6', '3', '1', '2', '2', '4']), .str (String.ofList ['1', '7', '3', '7', '2', '5', '0', '4', '9', '0', '0', '9', '6', '7', '0', '2', '8', '8', '8', '7', '2', '5']), .str (String.ofList ['1', '0', '3', '6', '0', '9', '5', '2', '2', '6', '0', '6', '0', '5', '7', '4', '4', '6', '7', '2', '1', '5']), .str (String.ofList ['1', '1', '7', '9', '4', '4', '4', '2', '6', '9', '3', '8', '4', '5', '1', '1', '0', '6', '5', '2', '5', '0']), .str (String.ofList ['1', '1', '7', '9', '4', '9', '8', '9', '0', '4', '8', '0', '7', '5', '9', '8', '2', '6', '8', '6', '7', '1']), .str (String.ofList ['1', '0', '3', '6', '5', '8', '1', '9', '7', '3', '2', '5', '6', '0', '2', '8', '4', '0', '8', '2', '2', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '6', '1', '5', '0', '3', '7', '8', '2', '1', '7', '2', '8', '9', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '6', '9', '0', '3', '8', '3', '1', '4', '0', '2', '3', '0', '3', '6']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_028_before_generic"
  err.flush

theorem array_moment_records_chunk_028 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 153)
      (SourceJson.white (momentRecordsChunk028Chars ++ tail)) acc =
      SourceJson.array (fuel + 152) (SourceJson.white tail) (momentRecordsChunk028Push acc) := by rfl

noncomputable def momentRecordsAcc029 : List SourceJson := momentRecordsChunk028Push momentRecordsAcc028

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_028_generic_complete"
  err.flush

noncomputable def momentRecordsChunk029Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '4', '8', '8', '2', '3', '3', '2', '6', '9', '8', '4', '5', '8', '6', '1', '6', '6', '4', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '0', '1', '8', '4', '2', '7', '4', '9', '6', '9', '7', '3', '3', '7', '5', '6', '5', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '8', '5', '2', '2', '3', '0', '3', '1', '8', '6', '4', '7', '8', '8', '6', '2', '3', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '7', '0', '1', '6', '0', '2', '2', '6', '1', '6', '8', '4', '3', '5', '4', '3', '6', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '8', '6', '9', '5', '3', '2', '9', '4', '5', '0', '0', '3', '1', '1', '7', '9', '5', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '0', '2', '6', '2', '7', '1', '6', '4', '5', '1', '3', '4', '4', '9', '0', '5', '6', '2', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '2', '3', '3', '2', '7', '0', '1', '9', '8', '3', '5', '3', '4', '8', '3', '7', '5', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '0', '1', '3', '7', '4', '7', '9', '2', '8', '6', '5', '0', '3', '9', '7', '8', '3', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '0', '1', '9', '0', '0', '5', '6', '4', '7', '9', '6', '0', '5', '7', '2', '7', '1', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '4', '1', '3', '9', '9', '4', '9', '0', '9', '2', '3', '9', '5', '3', '9', '6', '5', '4', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '6', '8', '3', '9', '8', '9', '9', '1', '2', '8', '4', '4', '2', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '7', '8', '1', '7', '2', '4', '8', '4', '5', '2', '3', '3', '6', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk029Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['2', '9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '5', '4', '8', '8', '2', '3', '3', '2', '6', '9', '8', '4', '5', '8', '6', '1', '6', '6', '4', '0']), .str (String.ofList ['1', '4', '6', '0', '1', '8', '4', '2', '7', '4', '9', '6', '9', '7', '3', '3', '7', '5', '6', '5', '5', '9']), .str (String.ofList ['2', '6', '8', '5', '2', '2', '3', '0', '3', '1', '8', '6', '4', '7', '8', '8', '6', '2', '3', '9', '3']), .str (String.ofList ['3', '7', '7', '0', '1', '6', '0', '2', '2', '6', '1', '6', '8', '4', '3', '5', '4', '3', '6', '7', '0']), .str (String.ofList ['7', '6', '8', '6', '9', '5', '3', '2', '9', '4', '5', '0', '0', '3', '1', '1', '7', '9', '5', '7', '4']), .str (String.ofList ['1', '8', '0', '2', '6', '2', '7', '1', '6', '4', '5', '1', '3', '4', '4', '9', '0', '5', '6', '2', '8', '3']), .str (String.ofList ['1', '6', '8', '2', '3', '3', '2', '7', '0', '1', '9', '8', '3', '5', '3', '4', '8', '3', '7', '5', '5', '7']), .str (String.ofList ['1', '2', '6', '0', '1', '3', '7', '4', '7', '9', '2', '8', '6', '5', '0', '3', '9', '7', '8', '3', '4', '6']), .str (String.ofList ['1', '2', '6', '0', '1', '9', '0', '0', '5', '6', '4', '7', '9', '6', '0', '5', '7', '2', '7', '1', '5', '0']), .str (String.ofList ['7', '7', '4', '1', '3', '9', '9', '4', '9', '0', '9', '2', '3', '9', '5', '3', '9', '6', '5', '4', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '6', '8', '3', '9', '8', '9', '9', '1', '2', '8', '4', '4', '2', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '7', '8', '1', '7', '2', '4', '8', '4', '5', '2', '3', '3', '6', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_029_before_generic"
  err.flush

theorem array_moment_records_chunk_029 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 152)
      (SourceJson.white (momentRecordsChunk029Chars ++ tail)) acc =
      SourceJson.array (fuel + 151) (SourceJson.white tail) (momentRecordsChunk029Push acc) := by rfl

noncomputable def momentRecordsAcc030 : List SourceJson := momentRecordsChunk029Push momentRecordsAcc029

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_029_generic_complete"
  err.flush

noncomputable def momentRecordsChunk030Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '5', '1', '3', '9', '0', '0', '4', '9', '4', '0', '6', '8', '3', '8', '3', '6', '5', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '5', '7', '3', '9', '3', '3', '9', '5', '1', '4', '8', '5', '3', '6', '1', '5', '1', '5', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '6', '6', '8', '0', '6', '6', '9', '5', '4', '6', '0', '5', '9', '9', '4', '0', '5', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '7', '0', '0', '1', '0', '9', '5', '5', '2', '6', '1', '7', '5', '0', '2', '2', '1', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '1', '8', '7', '1', '6', '0', '4', '8', '7', '5', '2', '0', '6', '6', '0', '4', '9', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '1', '5', '0', '4', '4', '1', '0', '7', '0', '7', '5', '4', '7', '3', '9', '9', '4', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '1', '6', '8', '5', '0', '8', '0', '2', '3', '5', '6', '2', '0', '2', '5', '2', '8', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '0', '2', '5', '1', '9', '1', '9', '9', '3', '5', '3', '2', '2', '5', '4', '5', '2', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '0', '6', '1', '6', '9', '1', '1', '3', '3', '8', '3', '1', '4', '5', '9', '5', '3', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '0', '6', '2', '0', '9', '7', '0', '7', '4', '9', '4', '6', '1', '5', '0', '6', '6', '7', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '6', '2', '5', '6', '1', '9', '3', '4', '5', '4', '9', '3', '3', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '7', '1', '9', '8', '9', '3', '8', '7', '4', '3', '5', '6', '5', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk030Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['3', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '7', '8', '5', '1', '3', '9', '0', '0', '4', '9', '4', '0', '6', '8', '3', '8', '3', '6', '5', '2', '1']), .str (String.ofList ['1', '8', '5', '7', '3', '9', '3', '3', '9', '5', '1', '4', '8', '5', '3', '6', '1', '5', '1', '5', '2', '0']), .str (String.ofList ['2', '8', '6', '6', '8', '0', '6', '6', '9', '5', '4', '6', '0', '5', '9', '9', '4', '0', '5', '7', '5']), .str (String.ofList ['5', '1', '7', '0', '0', '1', '0', '9', '5', '5', '2', '6', '1', '7', '5', '0', '2', '2', '1', '7', '1']), .str (String.ofList ['7', '5', '1', '8', '7', '1', '6', '0', '4', '8', '7', '5', '2', '0', '6', '6', '0', '4', '9', '3', '8']), .str (String.ofList ['2', '0', '5', '1', '5', '0', '4', '4', '1', '0', '7', '0', '7', '5', '4', '7', '3', '9', '9', '4', '8', '2']), .str (String.ofList ['1', '8', '1', '1', '6', '8', '5', '0', '8', '0', '2', '3', '5', '6', '2', '0', '2', '5', '2', '8', '6', '0']), .str (String.ofList ['9', '0', '0', '2', '5', '1', '9', '1', '9', '9', '3', '5', '3', '2', '2', '5', '4', '5', '2', '1', '3']), .str (String.ofList ['9', '1', '0', '6', '1', '6', '9', '1', '1', '3', '3', '8', '3', '1', '4', '5', '9', '5', '3', '4', '5']), .str (String.ofList ['9', '1', '0', '6', '2', '0', '9', '7', '0', '7', '4', '9', '4', '6', '1', '5', '0', '6', '6', '7', '7'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '6', '2', '5', '6', '1', '9', '3', '4', '5', '4', '9', '3', '3', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '7', '1', '9', '8', '9', '3', '8', '7', '4', '3', '5', '6', '5', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_030_before_generic"
  err.flush

theorem array_moment_records_chunk_030 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 151)
      (SourceJson.white (momentRecordsChunk030Chars ++ tail)) acc =
      SourceJson.array (fuel + 150) (SourceJson.white tail) (momentRecordsChunk030Push acc) := by rfl

noncomputable def momentRecordsAcc031 : List SourceJson := momentRecordsChunk030Push momentRecordsAcc030

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_030_generic_complete"
  err.flush

noncomputable def momentRecordsChunk031Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '3', '3', '1', '2', '9', '9', '0', '4', '0', '8', '0', '9', '3', '7', '4', '4', '6', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '0', '8', '3', '4', '8', '2', '4', '7', '0', '4', '4', '7', '1', '0', '0', '4', '4', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '6', '6', '3', '8', '1', '1', '7', '2', '6', '2', '1', '5', '4', '0', '9', '0', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '8', '3', '9', '7', '6', '1', '2', '3', '6', '4', '0', '0', '8', '9', '4', '0', '5', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '6', '9', '3', '0', '8', '1', '0', '8', '6', '1', '3', '6', '5', '1', '4', '2', '0', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '4', '3', '6', '0', '2', '5', '8', '1', '2', '2', '8', '4', '9', '6', '3', '1', '2', '5', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '7', '3', '3', '4', '2', '8', '7', '9', '2', '7', '8', '9', '3', '9', '8', '2', '3', '4', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '1', '7', '4', '3', '2', '5', '7', '1', '9', '9', '2', '7', '5', '2', '1', '3', '5', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '9', '1', '5', '8', '9', '2', '3', '0', '2', '6', '3', '2', '2', '1', '5', '4', '1', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '0', '9', '1', '3', '6', '0', '3', '7', '3', '6', '5', '1', '0', '3', '8', '0', '0', '8', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '6', '4', '0', '6', '3', '8', '8', '1', '2', '1', '2', '0', '3', '6', '1', '9', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '7', '3', '8', '9', '7', '3', '5', '7', '7', '9', '8', '0', '0', '8', '9', '6', '7', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk031Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['3', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '6', '4', '3', '3', '1', '2', '9', '9', '0', '4', '0', '8', '0', '9', '3', '7', '4', '4', '6', '8', '8']), .str (String.ofList ['1', '7', '6', '0', '8', '3', '4', '8', '2', '4', '7', '0', '4', '4', '7', '1', '0', '0', '4', '4', '8', '1']), .str (String.ofList ['2', '7', '2', '6', '6', '3', '8', '1', '1', '7', '2', '6', '2', '1', '5', '4', '0', '9', '0', '7', '0']), .str (String.ofList ['4', '2', '8', '3', '9', '7', '6', '1', '2', '3', '6', '4', '0', '0', '8', '9', '4', '0', '5', '9', '5']), .str (String.ofList ['7', '5', '6', '9', '3', '0', '8', '1', '0', '8', '6', '1', '3', '6', '5', '1', '4', '2', '0', '4', '2']), .str (String.ofList ['1', '7', '4', '3', '6', '0', '2', '5', '8', '1', '2', '2', '8', '4', '9', '6', '3', '1', '2', '5', '7', '4']), .str (String.ofList ['1', '7', '7', '3', '3', '4', '2', '8', '7', '9', '2', '7', '8', '9', '3', '9', '8', '2', '3', '4', '4', '1']), .str (String.ofList ['8', '8', '1', '7', '4', '3', '2', '5', '7', '1', '9', '9', '2', '7', '5', '2', '1', '3', '5', '7', '6']), .str (String.ofList ['9', '1', '9', '1', '5', '8', '9', '2', '3', '0', '2', '6', '3', '2', '2', '1', '5', '4', '1', '0', '4']), .str (String.ofList ['9', '4', '0', '9', '1', '3', '6', '0', '3', '7', '3', '6', '5', '1', '0', '3', '8', '0', '0', '8', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '6', '4', '0', '6', '3', '8', '8', '1', '2', '1', '2', '0', '3', '6', '1', '9', '3', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '7', '3', '8', '9', '7', '3', '5', '7', '7', '9', '8', '0', '0', '8', '9', '6', '7', '6']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_031_before_generic"
  err.flush

theorem array_moment_records_chunk_031 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 150)
      (SourceJson.white (momentRecordsChunk031Chars ++ tail)) acc =
      SourceJson.array (fuel + 149) (SourceJson.white tail) (momentRecordsChunk031Push acc) := by rfl

noncomputable def momentRecordsAcc032 : List SourceJson := momentRecordsChunk031Push momentRecordsAcc031

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_031_generic_complete"
  err.flush

noncomputable def momentRecordsBlock007Chars : List Char := momentRecordsChunk028Chars ++ momentRecordsChunk029Chars ++ momentRecordsChunk030Chars ++ momentRecordsChunk031Chars
noncomputable def momentRecordsBlock007Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk031Push (momentRecordsChunk030Push (momentRecordsChunk029Push (momentRecordsChunk028Push (acc))))

theorem array_moment_records_block_007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 153)
      (SourceJson.white (momentRecordsBlock007Chars ++ tail)) acc =
      SourceJson.array (fuel + 149) (SourceJson.white tail) (momentRecordsBlock007Push acc) := by
  have hinput : momentRecordsBlock007Chars ++ tail = momentRecordsChunk028Chars ++ (momentRecordsChunk029Chars ++ (momentRecordsChunk030Chars ++ (momentRecordsChunk031Chars ++ (tail)))) := by
    simp only [momentRecordsBlock007Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 153) (SourceJson.white (momentRecordsBlock007Chars ++ tail)) acc =
        SourceJson.array (fuel + 153) (SourceJson.white (momentRecordsChunk028Chars ++ (momentRecordsChunk029Chars ++ (momentRecordsChunk030Chars ++ (momentRecordsChunk031Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 153) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 152) (SourceJson.white (momentRecordsChunk029Chars ++ (momentRecordsChunk030Chars ++ (momentRecordsChunk031Chars ++ (tail))))) (momentRecordsChunk028Push (acc)) := array_moment_records_chunk_028 fuel (momentRecordsChunk029Chars ++ (momentRecordsChunk030Chars ++ (momentRecordsChunk031Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 151) (SourceJson.white (momentRecordsChunk030Chars ++ (momentRecordsChunk031Chars ++ (tail)))) (momentRecordsChunk029Push (momentRecordsChunk028Push (acc))) := array_moment_records_chunk_029 fuel (momentRecordsChunk030Chars ++ (momentRecordsChunk031Chars ++ (tail))) (momentRecordsChunk028Push (acc))
    _ = SourceJson.array (fuel + 150) (SourceJson.white (momentRecordsChunk031Chars ++ (tail))) (momentRecordsChunk030Push (momentRecordsChunk029Push (momentRecordsChunk028Push (acc)))) := array_moment_records_chunk_030 fuel (momentRecordsChunk031Chars ++ (tail)) (momentRecordsChunk029Push (momentRecordsChunk028Push (acc)))
    _ = SourceJson.array (fuel + 149) (SourceJson.white tail) (momentRecordsBlock007Push acc) := array_moment_records_chunk_031 fuel (tail) (momentRecordsChunk030Push (momentRecordsChunk029Push (momentRecordsChunk028Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_007_before_raw_binding"
  err.flush

theorem moment_records_block_007_prefix :
    (momentRest01 14959).take 2081 = momentRecordsBlock007Chars := by rfl

theorem moment_records_block_007_split :
    momentRest01 14959 = momentRecordsBlock007Chars ++ momentRest01 17040 := by
  calc
    momentRest01 14959 =
        (momentRest01 14959).take 2081 ++ (momentRest01 14959).drop 2081 :=
      (List.take_append_drop 2081 (momentRest01 14959)).symm
    _ = momentRecordsBlock007Chars ++ (momentRest01 14959).drop 2081 :=
      congrArg (fun p => p ++ (momentRest01 14959).drop 2081) moment_records_block_007_prefix
    _ = momentRecordsBlock007Chars ++ momentRest01 17040 :=
      congrArg (fun rest => momentRecordsBlock007Chars ++ rest) (momentRest01_drop 14959 2081)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_007_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_007 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 153)
      (SourceJson.white (momentRest01 14959)) acc =
      SourceJson.array (fuel + 149) (SourceJson.white (momentRest01 17040)) (momentRecordsBlock007Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 153) (SourceJson.white s) acc)
      moment_records_block_007_split).trans (array_moment_records_block_007 fuel (momentRest01 17040) acc)

theorem moment_records_through_block_007 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 149) (SourceJson.white (momentRest01 17040)) momentRecordsAcc032 := by
  exact (moment_records_through_block_006 fuel).trans (array_moment_records_original_block_007 fuel momentRecordsAcc028)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_007_complete"
  err.flush

#print axioms array_moment_records_chunk_028
#print axioms array_moment_records_chunk_029
#print axioms array_moment_records_chunk_030
#print axioms array_moment_records_chunk_031
#print axioms array_moment_records_block_007
#print axioms moment_records_block_007_prefix
#print axioms moment_records_block_007_split
#print axioms array_moment_records_original_block_007
#print axioms moment_records_through_block_007

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
