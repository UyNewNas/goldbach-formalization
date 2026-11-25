import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock032

/-! Original moment records block 33. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk132Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '6', '7', '3', '8', '7', '7', '6', '1', '0', '5', '0', '5', '0', '5', '3', '0', '8', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '7', '2', '9', '0', '9', '5', '8', '4', '7', '6', '1', '7', '2', '5', '4', '6', '2', '6', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '5', '9', '1', '0', '2', '8', '5', '2', '9', '9', '3', '5', '7', '3', '9', '1', '9', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '6', '1', '3', '0', '1', '1', '1', '1', '3', '5', '9', '1', '1', '8', '3', '1', '2', '8', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '9', '7', '2', '8', '6', '1', '7', '8', '6', '0', '9', '4', '6', '7', '7', '1', '3', '3', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '8', '8', '3', '3', '5', '2', '7', '4', '1', '6', '9', '1', '2', '8', '3', '7', '0', '4', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '2', '7', '1', '6', '5', '3', '1', '0', '4', '5', '3', '8', '9', '4', '9', '6', '8', '9', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '6', '0', '9', '1', '3', '3', '0', '4', '5', '3', '5', '5', '7', '8', '3', '6', '5', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '9', '1', '1', '7', '6', '1', '8', '4', '0', '3', '8', '2', '6', '6', '2', '3', '6', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '9', '1', '6', '0', '0', '8', '6', '7', '4', '4', '9', '7', '4', '5', '8', '8', '0', '1', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '5', '0', '0', '6', '4', '4', '0', '4', '3', '5', '0', '3', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '5', '5', '5', '5', '4', '1', '7', '3', '9', '0', '4', '2', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk132Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '3', '2'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '7', '6', '7', '3', '8', '7', '7', '6', '1', '0', '5', '0', '5', '0', '5', '3', '0', '8', '2', '8']), .str (String.ofList ['1', '4', '7', '2', '9', '0', '9', '5', '8', '4', '7', '6', '1', '7', '2', '5', '4', '6', '2', '6', '6', '0']), .str (String.ofList ['3', '6', '5', '9', '1', '0', '2', '8', '5', '2', '9', '9', '3', '5', '7', '3', '9', '1', '9', '3', '1']), .str (String.ofList ['8', '6', '1', '3', '0', '1', '1', '1', '1', '3', '5', '9', '1', '1', '8', '3', '1', '2', '8', '7', '0']), .str (String.ofList ['1', '3', '4', '9', '7', '2', '8', '6', '1', '7', '8', '6', '0', '9', '4', '6', '7', '7', '1', '3', '3', '2']), .str (String.ofList ['2', '7', '8', '8', '8', '3', '3', '5', '2', '7', '4', '1', '6', '9', '1', '2', '8', '3', '7', '0', '4', '0']), .str (String.ofList ['1', '8', '2', '7', '1', '6', '5', '3', '1', '0', '4', '5', '3', '8', '9', '4', '9', '6', '8', '9', '1', '9']), .str (String.ofList ['1', '5', '1', '6', '0', '9', '1', '3', '3', '0', '4', '5', '3', '5', '5', '7', '8', '3', '6', '5', '1', '8']), .str (String.ofList ['1', '5', '4', '9', '1', '1', '7', '6', '1', '8', '4', '0', '3', '8', '2', '6', '6', '2', '3', '6', '4', '2']), .str (String.ofList ['1', '5', '4', '9', '1', '6', '0', '0', '8', '6', '7', '4', '4', '9', '7', '4', '5', '8', '8', '0', '1', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '5', '0', '0', '6', '4', '4', '0', '4', '3', '5', '0', '3', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '5', '5', '5', '5', '4', '1', '7', '3', '9', '0', '4', '2', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_132_before_generic"
  err.flush

theorem array_moment_records_chunk_132 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 49)
      (SourceJson.white (momentRecordsChunk132Chars ++ tail)) acc =
      SourceJson.array (fuel + 48) (SourceJson.white tail) (momentRecordsChunk132Push acc) := by rfl

noncomputable def momentRecordsAcc133 : List SourceJson := momentRecordsChunk132Push momentRecordsAcc132

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_132_generic_complete"
  err.flush

noncomputable def momentRecordsChunk133Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '7', '8', '1', '1', '5', '4', '7', '7', '8', '4', '5', '8', '7', '8', '2', '4', '3', '2', '6', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '3', '7', '7', '8', '3', '0', '0', '2', '5', '2', '4', '2', '6', '5', '7', '8', '8', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '6', '4', '5', '5', '2', '0', '4', '0', '4', '3', '5', '6', '3', '7', '5', '0', '3', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '5', '5', '1', '9', '6', '6', '3', '1', '7', '9', '9', '9', '2', '7', '4', '2', '8', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '8', '8', '0', '0', '9', '0', '4', '6', '0', '5', '7', '5', '8', '3', '8', '1', '2', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '3', '9', '8', '0', '1', '4', '8', '8', '6', '7', '0', '9', '4', '6', '6', '3', '2', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '4', '3', '7', '0', '4', '2', '7', '4', '3', '7', '3', '0', '4', '3', '7', '9', '0', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '7', '4', '4', '3', '4', '4', '2', '6', '7', '7', '8', '5', '7', '0', '0', '7', '3', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '8', '1', '9', '4', '5', '7', '1', '5', '0', '5', '3', '5', '9', '7', '1', '3', '6', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '8', '2', '4', '3', '3', '2', '4', '0', '4', '3', '5', '9', '2', '2', '6', '1', '3', '9', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '2', '8', '1', '3', '0', '9', '1', '7', '1', '6', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '4', '2', '2', '5', '5', '1', '4', '2', '2', '0', '7', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk133Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '3', '3'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '7', '7', '8', '1', '1', '5', '4', '7', '7', '8', '4', '5', '8', '7', '8', '2', '4', '3', '2', '6', '6']), .str (String.ofList ['1', '9', '0', '3', '7', '7', '8', '3', '0', '0', '2', '5', '2', '4', '2', '6', '5', '7', '8', '8', '4', '8']), .str (String.ofList ['3', '4', '6', '4', '5', '5', '2', '0', '4', '0', '4', '3', '5', '6', '3', '7', '5', '0', '3', '9', '6']), .str (String.ofList ['9', '4', '5', '5', '1', '9', '6', '6', '3', '1', '7', '9', '9', '9', '2', '7', '4', '2', '8', '8', '6']), .str (String.ofList ['1', '3', '9', '8', '8', '0', '0', '9', '0', '4', '6', '0', '5', '7', '5', '8', '3', '8', '1', '2', '9', '3']), .str (String.ofList ['2', '7', '8', '3', '9', '8', '0', '1', '4', '8', '8', '6', '7', '0', '9', '4', '6', '6', '3', '2', '2', '1']), .str (String.ofList ['2', '0', '3', '4', '3', '7', '0', '4', '2', '7', '4', '3', '7', '3', '0', '4', '3', '7', '9', '0', '8', '4']), .str (String.ofList ['1', '7', '6', '7', '4', '4', '3', '4', '4', '2', '6', '7', '7', '8', '5', '7', '0', '0', '7', '3', '0', '6']), .str (String.ofList ['1', '7', '6', '8', '1', '9', '4', '5', '7', '1', '5', '0', '5', '3', '5', '9', '7', '1', '3', '6', '1', '9']), .str (String.ofList ['1', '7', '6', '8', '2', '4', '3', '3', '2', '4', '0', '4', '3', '5', '9', '2', '2', '6', '1', '3', '9', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '2', '8', '1', '3', '0', '9', '1', '7', '1', '6', '7', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '4', '2', '2', '5', '5', '1', '4', '2', '2', '0', '7', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_133_before_generic"
  err.flush

theorem array_moment_records_chunk_133 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 48)
      (SourceJson.white (momentRecordsChunk133Chars ++ tail)) acc =
      SourceJson.array (fuel + 47) (SourceJson.white tail) (momentRecordsChunk133Push acc) := by rfl

noncomputable def momentRecordsAcc134 : List SourceJson := momentRecordsChunk133Push momentRecordsAcc133

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_133_generic_complete"
  err.flush

noncomputable def momentRecordsChunk134Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '6', '0', '3', '2', '5', '2', '3', '1', '0', '4', '2', '3', '8', '7', '0', '4', '1', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '7', '8', '6', '5', '3', '1', '3', '3', '2', '8', '5', '4', '7', '6', '5', '0', '5', '3', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '9', '8', '8', '5', '7', '6', '9', '5', '0', '8', '7', '1', '0', '7', '9', '9', '0', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '0', '7', '5', '5', '4', '1', '9', '7', '7', '9', '4', '9', '9', '9', '5', '3', '8', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '1', '5', '0', '4', '5', '8', '4', '9', '1', '4', '9', '2', '3', '4', '6', '5', '1', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '1', '1', '6', '8', '9', '9', '4', '1', '1', '5', '2', '7', '0', '0', '6', '8', '5', '9', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '5', '0', '5', '0', '0', '9', '5', '2', '5', '6', '5', '0', '3', '8', '1', '3', '5', '4', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '8', '1', '2', '3', '7', '6', '2', '8', '6', '0', '7', '2', '9', '1', '6', '6', '9', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '0', '1', '4', '6', '5', '0', '6', '8', '7', '1', '8', '0', '7', '8', '2', '9', '8', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '0', '2', '0', '1', '3', '6', '8', '3', '4', '5', '3', '6', '7', '3', '7', '2', '9', '7', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '9', '8', '3', '9', '7', '6', '5', '2', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '8', '3', '5', '6', '5', '0', '9', '7', '0', '9', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk134Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '3', '4'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '9', '2', '6', '0', '3', '2', '5', '2', '3', '1', '0', '4', '2', '3', '8', '7', '0', '4', '1', '8', '4']), .str (String.ofList ['1', '8', '7', '8', '6', '5', '3', '1', '3', '3', '2', '8', '5', '4', '7', '6', '5', '0', '5', '3', '3', '5']), .str (String.ofList ['2', '6', '9', '8', '8', '5', '7', '6', '9', '5', '0', '8', '7', '1', '0', '7', '9', '9', '0', '6', '1']), .str (String.ofList ['1', '0', '9', '0', '7', '5', '5', '4', '1', '9', '7', '7', '9', '4', '9', '9', '9', '5', '3', '8', '6', '9']), .str (String.ofList ['1', '1', '1', '1', '5', '0', '4', '5', '8', '4', '9', '1', '4', '9', '2', '3', '4', '6', '5', '1', '9', '2']), .str (String.ofList ['2', '8', '1', '1', '6', '8', '9', '9', '4', '1', '1', '5', '2', '7', '0', '0', '6', '8', '5', '9', '8', '7']), .str (String.ofList ['1', '9', '5', '0', '5', '0', '0', '9', '5', '2', '5', '6', '5', '0', '3', '8', '1', '3', '5', '4', '2', '8']), .str (String.ofList ['1', '7', '6', '8', '1', '2', '3', '7', '6', '2', '8', '6', '0', '7', '2', '9', '1', '6', '6', '9', '6', '4']), .str (String.ofList ['1', '5', '9', '0', '1', '4', '6', '5', '0', '6', '8', '7', '1', '8', '0', '7', '8', '2', '9', '8', '0', '6']), .str (String.ofList ['1', '5', '9', '0', '2', '0', '1', '3', '6', '8', '3', '4', '5', '3', '6', '7', '3', '7', '2', '9', '7', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '7', '9', '8', '3', '9', '7', '6', '5', '2', '5', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '8', '3', '5', '6', '5', '0', '9', '7', '0', '9', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_134_before_generic"
  err.flush

theorem array_moment_records_chunk_134 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 47)
      (SourceJson.white (momentRecordsChunk134Chars ++ tail)) acc =
      SourceJson.array (fuel + 46) (SourceJson.white tail) (momentRecordsChunk134Push acc) := by rfl

noncomputable def momentRecordsAcc135 : List SourceJson := momentRecordsChunk134Push momentRecordsAcc134

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_134_generic_complete"
  err.flush

noncomputable def momentRecordsChunk135Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '9', '5', '5', '6', '4', '0', '9', '3', '9', '2', '5', '3', '9', '3', '1', '3', '9', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '3', '0', '3', '4', '3', '1', '8', '0', '8', '0', '4', '1', '6', '6', '3', '2', '0', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '1', '4', '7', '9', '8', '3', '4', '6', '7', '7', '0', '2', '0', '0', '0', '9', '1', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '3', '1', '5', '7', '2', '7', '5', '6', '1', '9', '4', '6', '4', '5', '4', '5', '3', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '2', '1', '5', '9', '6', '2', '2', '3', '7', '1', '5', '3', '8', '4', '3', '3', '8', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '9', '9', '5', '3', '8', '4', '9', '1', '9', '9', '2', '7', '0', '5', '8', '9', '4', '6', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '1', '2', '2', '7', '0', '7', '8', '0', '2', '4', '7', '4', '2', '3', '1', '3', '3', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '2', '0', '2', '2', '6', '9', '8', '2', '1', '2', '7', '3', '4', '8', '9', '0', '2', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '1', '5', '4', '0', '6', '0', '6', '3', '7', '5', '0', '3', '8', '0', '4', '1', '6', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '1', '5', '9', '7', '7', '0', '1', '6', '0', '4', '6', '4', '0', '9', '3', '7', '8', '4', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '6', '8', '9', '5', '9', '4', '0', '7', '5', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '7', '5', '3', '6', '2', '8', '1', '8', '1', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk135Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '3', '5'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '4', '8', '9', '5', '5', '6', '4', '0', '9', '3', '9', '2', '5', '3', '9', '3', '1', '3', '9', '6', '0']), .str (String.ofList ['1', '4', '5', '3', '0', '3', '4', '3', '1', '8', '0', '8', '0', '4', '1', '6', '6', '3', '2', '0', '7', '6']), .str (String.ofList ['1', '8', '6', '1', '4', '7', '9', '8', '3', '4', '6', '7', '7', '0', '2', '0', '0', '0', '9', '1', '1']), .str (String.ofList ['1', '0', '3', '3', '1', '5', '7', '2', '7', '5', '6', '1', '9', '4', '6', '4', '5', '4', '5', '3', '8', '2']), .str (String.ofList ['9', '4', '2', '1', '5', '9', '6', '2', '2', '3', '7', '1', '5', '3', '8', '4', '3', '3', '8', '1', '9']), .str (String.ofList ['2', '0', '9', '9', '5', '3', '8', '4', '9', '1', '9', '9', '2', '7', '0', '5', '8', '9', '4', '6', '7', '2']), .str (String.ofList ['1', '7', '5', '1', '2', '2', '7', '0', '7', '8', '0', '2', '4', '7', '4', '2', '3', '1', '3', '3', '7', '5']), .str (String.ofList ['1', '6', '1', '2', '0', '2', '2', '6', '9', '8', '2', '1', '2', '7', '3', '4', '8', '9', '0', '2', '8', '2']), .str (String.ofList ['1', '4', '8', '1', '5', '4', '0', '6', '0', '6', '3', '7', '5', '0', '3', '8', '0', '4', '1', '6', '1', '2']), .str (String.ofList ['1', '4', '8', '1', '5', '9', '7', '7', '0', '1', '6', '0', '4', '6', '4', '0', '9', '3', '7', '8', '4', '4'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '6', '8', '9', '5', '9', '4', '0', '7', '5', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '7', '5', '3', '6', '2', '8', '1', '8', '1', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_135_before_generic"
  err.flush

theorem array_moment_records_chunk_135 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 46)
      (SourceJson.white (momentRecordsChunk135Chars ++ tail)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white tail) (momentRecordsChunk135Push acc) := by rfl

noncomputable def momentRecordsAcc136 : List SourceJson := momentRecordsChunk135Push momentRecordsAcc135

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_135_generic_complete"
  err.flush

noncomputable def momentRecordsBlock033Chars : List Char := momentRecordsChunk132Chars ++ momentRecordsChunk133Chars ++ momentRecordsChunk134Chars ++ momentRecordsChunk135Chars
noncomputable def momentRecordsBlock033Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk135Push (momentRecordsChunk134Push (momentRecordsChunk133Push (momentRecordsChunk132Push (acc))))

theorem array_moment_records_block_033 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 49)
      (SourceJson.white (momentRecordsBlock033Chars ++ tail)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white tail) (momentRecordsBlock033Push acc) := by
  have hinput : momentRecordsBlock033Chars ++ tail = momentRecordsChunk132Chars ++ (momentRecordsChunk133Chars ++ (momentRecordsChunk134Chars ++ (momentRecordsChunk135Chars ++ (tail)))) := by
    simp only [momentRecordsBlock033Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 49) (SourceJson.white (momentRecordsBlock033Chars ++ tail)) acc =
        SourceJson.array (fuel + 49) (SourceJson.white (momentRecordsChunk132Chars ++ (momentRecordsChunk133Chars ++ (momentRecordsChunk134Chars ++ (momentRecordsChunk135Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 49) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 48) (SourceJson.white (momentRecordsChunk133Chars ++ (momentRecordsChunk134Chars ++ (momentRecordsChunk135Chars ++ (tail))))) (momentRecordsChunk132Push (acc)) := array_moment_records_chunk_132 fuel (momentRecordsChunk133Chars ++ (momentRecordsChunk134Chars ++ (momentRecordsChunk135Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 47) (SourceJson.white (momentRecordsChunk134Chars ++ (momentRecordsChunk135Chars ++ (tail)))) (momentRecordsChunk133Push (momentRecordsChunk132Push (acc))) := array_moment_records_chunk_133 fuel (momentRecordsChunk134Chars ++ (momentRecordsChunk135Chars ++ (tail))) (momentRecordsChunk132Push (acc))
    _ = SourceJson.array (fuel + 46) (SourceJson.white (momentRecordsChunk135Chars ++ (tail))) (momentRecordsChunk134Push (momentRecordsChunk133Push (momentRecordsChunk132Push (acc)))) := array_moment_records_chunk_134 fuel (momentRecordsChunk135Chars ++ (tail)) (momentRecordsChunk133Push (momentRecordsChunk132Push (acc)))
    _ = SourceJson.array (fuel + 45) (SourceJson.white tail) (momentRecordsBlock033Push acc) := array_moment_records_chunk_135 fuel (tail) (momentRecordsChunk134Push (momentRecordsChunk133Push (momentRecordsChunk132Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_033_before_raw_binding"
  err.flush

theorem moment_records_block_033_prefix :
    (momentRest01 68943).take 2067 = momentRecordsBlock033Chars := by rfl

theorem moment_records_block_033_split :
    momentRest01 68943 = momentRecordsBlock033Chars ++ momentRest01 71010 := by
  calc
    momentRest01 68943 =
        (momentRest01 68943).take 2067 ++ (momentRest01 68943).drop 2067 :=
      (List.take_append_drop 2067 (momentRest01 68943)).symm
    _ = momentRecordsBlock033Chars ++ (momentRest01 68943).drop 2067 :=
      congrArg (fun p => p ++ (momentRest01 68943).drop 2067) moment_records_block_033_prefix
    _ = momentRecordsBlock033Chars ++ momentRest01 71010 :=
      congrArg (fun rest => momentRecordsBlock033Chars ++ rest) (momentRest01_drop 68943 2067)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_033_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_033 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 49)
      (SourceJson.white (momentRest01 68943)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white (momentRest01 71010)) (momentRecordsBlock033Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 49) (SourceJson.white s) acc)
      moment_records_block_033_split).trans (array_moment_records_block_033 fuel (momentRest01 71010) acc)

theorem moment_records_through_block_033 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 45) (SourceJson.white (momentRest01 71010)) momentRecordsAcc136 := by
  exact (moment_records_through_block_032 fuel).trans (array_moment_records_original_block_033 fuel momentRecordsAcc132)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_033_complete"
  err.flush

#print axioms array_moment_records_chunk_132
#print axioms array_moment_records_chunk_133
#print axioms array_moment_records_chunk_134
#print axioms array_moment_records_chunk_135
#print axioms array_moment_records_block_033
#print axioms moment_records_block_033_prefix
#print axioms moment_records_block_033_split
#print axioms array_moment_records_original_block_033
#print axioms moment_records_through_block_033

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
