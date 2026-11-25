import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock000

/-! Original moment records block 1. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk004Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '8', '3', '8', '6', '9', '3', '8', '1', '6', '7', '3', '1', '0', '4', '9', '4', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '7', '1', '3', '5', '0', '5', '5', '1', '1', '7', '7', '9', '7', '0', '4', '1', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '7', '7', '4', '8', '5', '6', '0', '1', '2', '6', '4', '4', '7', '0', '6', '0', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '4', '1', '1', '6', '8', '5', '7', '0', '8', '3', '6', '6', '4', '0', '7', '2', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '8', '3', '5', '9', '6', '9', '2', '6', '4', '1', '6', '3', '5', '9', '1', '6', '5', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '9', '0', '3', '9', '7', '8', '5', '7', '9', '2', '1', '2', '2', '0', '5', '5', '0', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '1', '8', '5', '8', '8', '9', '1', '7', '7', '9', '3', '8', '0', '9', '7', '5', '8', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '6', '5', '5', '2', '7', '9', '6', '6', '7', '8', '7', '1', '1', '9', '6', '4', '0', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '0', '1', '8', '5', '3', '6', '7', '3', '9', '1', '4', '1', '1', '0', '9', '0', '6', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '4', '5', '5', '3', '4', '8', '7', '0', '7', '0', '8', '9', '1', '2', '2', '6', '1', '9', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '8', '8', '8', '0', '4', '1', '8', '7', '3', '7', '6', '0', '7', '8', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '9', '0', '9', '1', '8', '5', '7', '1', '5', '4', '3', '7', '4', '0', '3', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk004Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['4'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '8', '1', '8', '3', '8', '6', '9', '3', '8', '1', '6', '7', '3', '1', '0', '4', '9', '4', '4', '9']), .str (String.ofList ['2', '0', '8', '7', '1', '3', '5', '0', '5', '5', '1', '1', '7', '7', '9', '7', '0', '4', '1', '3', '6']), .str (String.ofList ['1', '6', '7', '7', '7', '4', '8', '5', '6', '0', '1', '2', '6', '4', '4', '7', '0', '6', '0', '0', '8']), .str (String.ofList ['4', '9', '6', '4', '1', '1', '6', '8', '5', '7', '0', '8', '3', '6', '6', '4', '0', '7', '2', '5', '3']), .str (String.ofList ['2', '1', '8', '3', '5', '9', '6', '9', '2', '6', '4', '1', '6', '3', '5', '9', '1', '6', '5', '6', '7']), .str (String.ofList ['4', '1', '9', '0', '3', '9', '7', '8', '5', '7', '9', '2', '1', '2', '2', '0', '5', '5', '0', '7', '0']), .str (String.ofList ['4', '7', '1', '8', '5', '8', '8', '9', '1', '7', '7', '9', '3', '8', '0', '9', '7', '5', '8', '4', '8']), .str (String.ofList ['6', '0', '6', '5', '5', '2', '7', '9', '6', '6', '7', '8', '7', '1', '1', '9', '6', '4', '0', '9', '6']), .str (String.ofList ['5', '2', '0', '1', '8', '5', '3', '6', '7', '3', '9', '1', '4', '1', '1', '0', '9', '0', '6', '5', '9']), .str (String.ofList ['4', '1', '4', '5', '5', '3', '4', '8', '7', '0', '7', '0', '8', '9', '1', '2', '2', '6', '1', '9', '6'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '8', '8', '8', '0', '4', '1', '8', '7', '3', '7', '6', '0', '7', '8', '9', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '9', '0', '9', '1', '8', '5', '7', '1', '5', '4', '3', '7', '4', '0', '3', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_004_before_generic"
  err.flush

theorem array_moment_records_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 89)
      (SourceJson.white (momentRecordsChunk004Chars ++ tail)) acc =
      SourceJson.array (fuel + 88) (SourceJson.white tail) (momentRecordsChunk004Push acc) := by rfl

noncomputable def momentRecordsAcc005 : List SourceJson := momentRecordsChunk004Push momentRecordsAcc004

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_004_generic_complete"
  err.flush

noncomputable def momentRecordsChunk005Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '1', '1', '2', '7', '9', '0', '0', '9', '1', '2', '7', '6', '1', '0', '1', '2', '1', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '4', '8', '2', '8', '0', '6', '8', '2', '4', '2', '1', '3', '7', '6', '0', '0', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '9', '0', '4', '3', '9', '8', '4', '0', '1', '0', '5', '8', '3', '9', '3', '0', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '9', '1', '5', '5', '2', '2', '5', '5', '9', '5', '4', '6', '3', '0', '7', '6', '0', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '7', '6', '4', '8', '1', '6', '4', '3', '3', '0', '2', '5', '6', '6', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '4', '3', '8', '0', '7', '4', '2', '0', '0', '5', '0', '2', '8', '0', '9', '1', '3', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '0', '8', '6', '8', '3', '9', '5', '7', '2', '8', '5', '6', '2', '7', '3', '1', '1', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '3', '0', '4', '8', '7', '5', '7', '4', '8', '0', '0', '7', '8', '9', '7', '6', '4', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '8', '0', '6', '3', '3', '5', '4', '1', '0', '2', '9', '9', '3', '5', '8', '9', '6', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '8', '1', '2', '2', '2', '5', '1', '1', '0', '9', '7', '4', '6', '2', '2', '5', '0', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '0', '5', '9', '3', '1', '8', '7', '9', '1', '4', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '0', '7', '4', '2', '1', '2', '0', '9', '3', '6', '3', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk005Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '7', '1', '1', '2', '7', '9', '0', '0', '9', '1', '2', '7', '6', '1', '0', '1', '2', '1', '9', '2']), .str (String.ofList ['1', '9', '0', '4', '8', '2', '8', '0', '6', '8', '2', '4', '2', '1', '3', '7', '6', '0', '0', '4', '2']), .str (String.ofList ['1', '6', '3', '9', '0', '4', '3', '9', '8', '4', '0', '1', '0', '5', '8', '3', '9', '3', '0', '4', '9']), .str (String.ofList ['4', '9', '9', '1', '5', '5', '2', '2', '5', '5', '9', '5', '4', '6', '3', '0', '7', '6', '0', '0', '8']), .str (String.ofList ['2', '3', '4', '3', '7', '7', '6', '4', '8', '1', '6', '4', '3', '3', '0', '2', '5', '6', '6', '0', '0']), .str (String.ofList ['4', '0', '4', '3', '8', '0', '7', '4', '2', '0', '0', '5', '0', '2', '8', '0', '9', '1', '3', '6', '4']), .str (String.ofList ['5', '9', '0', '8', '6', '8', '3', '9', '5', '7', '2', '8', '5', '6', '2', '7', '3', '1', '1', '7', '3']), .str (String.ofList ['5', '6', '3', '0', '4', '8', '7', '5', '7', '4', '8', '0', '0', '7', '8', '9', '7', '6', '4', '1', '2']), .str (String.ofList ['3', '6', '8', '0', '6', '3', '3', '5', '4', '1', '0', '2', '9', '9', '3', '5', '8', '9', '6', '2', '7']), .str (String.ofList ['3', '6', '8', '1', '2', '2', '2', '5', '1', '1', '0', '9', '7', '4', '6', '2', '2', '5', '0', '6', '4'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '0', '5', '9', '3', '1', '8', '7', '9', '1', '4', '7', '6'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '0', '7', '4', '2', '1', '2', '0', '9', '3', '6', '3', '6']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_005_before_generic"
  err.flush

theorem array_moment_records_chunk_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 88)
      (SourceJson.white (momentRecordsChunk005Chars ++ tail)) acc =
      SourceJson.array (fuel + 87) (SourceJson.white tail) (momentRecordsChunk005Push acc) := by rfl

noncomputable def momentRecordsAcc006 : List SourceJson := momentRecordsChunk005Push momentRecordsAcc005

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_005_generic_complete"
  err.flush

noncomputable def momentRecordsChunk006Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '2', '4', '4', '7', '0', '1', '6', '5', '6', '0', '9', '6', '7', '1', '8', '3', '7', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '0', '2', '7', '4', '9', '3', '1', '2', '3', '5', '9', '8', '6', '0', '4', '4', '5', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '8', '4', '1', '4', '2', '6', '7', '3', '0', '1', '2', '5', '9', '0', '3', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '3', '4', '1', '1', '8', '9', '1', '0', '0', '3', '6', '7', '1', '8', '1', '3', '4', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '4', '8', '6', '6', '1', '9', '1', '8', '8', '9', '3', '6', '7', '8', '0', '9', '1', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '8', '5', '0', '7', '8', '8', '5', '9', '9', '2', '3', '1', '0', '4', '2', '4', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '7', '0', '9', '5', '1', '0', '7', '2', '6', '5', '8', '1', '3', '8', '1', '4', '4', '4', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '7', '0', '5', '0', '4', '5', '9', '2', '9', '8', '1', '5', '4', '9', '6', '9', '7', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '8', '3', '6', '3', '6', '0', '0', '9', '3', '9', '5', '7', '4', '7', '6', '5', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '5', '2', '1', '7', '8', '5', '5', '1', '7', '6', '7', '4', '9', '2', '4', '0', '2', '6', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '3', '7', '1', '5', '0', '8', '3', '3', '0', '3', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '3', '9', '4', '2', '5', '8', '0', '8', '0', '0', '3', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk006Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['4', '1', '2', '4', '4', '7', '0', '1', '6', '5', '6', '0', '9', '6', '7', '1', '8', '3', '7', '0', '5']), .str (String.ofList ['4', '5', '0', '2', '7', '4', '9', '3', '1', '2', '3', '5', '9', '8', '6', '0', '4', '4', '5', '1', '2']), .str (String.ofList ['2', '0', '6', '7', '8', '4', '1', '4', '2', '6', '7', '3', '0', '1', '2', '5', '9', '0', '3', '2', '0']), .str (String.ofList ['5', '7', '3', '4', '1', '1', '8', '9', '1', '0', '0', '3', '6', '7', '1', '8', '1', '3', '4', '5', '5']), .str (String.ofList ['3', '3', '4', '8', '6', '6', '1', '9', '1', '8', '8', '9', '3', '6', '7', '8', '0', '9', '1', '2', '4']), .str (String.ofList ['5', '1', '0', '8', '5', '0', '7', '8', '8', '5', '9', '9', '2', '3', '1', '0', '4', '2', '4', '5', '9']), .str (String.ofList ['3', '3', '7', '0', '9', '5', '1', '0', '7', '2', '6', '5', '8', '1', '3', '8', '1', '4', '4', '4', '7']), .str (String.ofList ['5', '4', '7', '0', '5', '0', '4', '5', '9', '2', '9', '8', '1', '5', '4', '9', '6', '9', '7', '9', '8']), .str (String.ofList ['5', '1', '0', '8', '3', '6', '3', '6', '0', '0', '9', '3', '9', '5', '7', '4', '7', '6', '5', '8', '3']), .str (String.ofList ['4', '2', '5', '2', '1', '7', '8', '5', '5', '1', '7', '6', '7', '4', '9', '2', '4', '0', '2', '6', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '3', '7', '1', '5', '0', '8', '3', '3', '0', '3', '7', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '3', '9', '4', '2', '5', '8', '0', '8', '0', '0', '3', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_006_before_generic"
  err.flush

theorem array_moment_records_chunk_006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 87)
      (SourceJson.white (momentRecordsChunk006Chars ++ tail)) acc =
      SourceJson.array (fuel + 86) (SourceJson.white tail) (momentRecordsChunk006Push acc) := by rfl

noncomputable def momentRecordsAcc007 : List SourceJson := momentRecordsChunk006Push momentRecordsAcc006

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_006_generic_complete"
  err.flush

noncomputable def momentRecordsChunk007Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '0', '4', '1', '8', '5', '4', '3', '3', '3', '5', '3', '7', '0', '8', '4', '7', '9', '6', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '9', '8', '6', '2', '9', '8', '8', '5', '2', '2', '6', '5', '1', '6', '0', '3', '3', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '9', '2', '2', '7', '6', '2', '6', '5', '4', '0', '1', '4', '8', '5', '1', '8', '8', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '4', '4', '0', '5', '4', '9', '2', '6', '4', '5', '5', '8', '5', '4', '9', '7', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '9', '3', '8', '8', '9', '8', '4', '8', '3', '6', '6', '7', '3', '7', '8', '9', '5', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '8', '7', '3', '5', '5', '0', '1', '4', '4', '7', '6', '7', '8', '8', '7', '2', '1', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '1', '6', '0', '3', '8', '5', '2', '5', '2', '1', '5', '4', '0', '6', '1', '6', '8', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '6', '0', '0', '0', '8', '6', '9', '3', '7', '4', '4', '2', '0', '9', '9', '4', '1', '4', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '5', '5', '0', '6', '8', '7', '4', '6', '7', '0', '9', '5', '0', '3', '1', '1', '1', '4', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '2', '8', '7', '3', '0', '6', '8', '7', '7', '5', '3', '6', '9', '6', '3', '8', '5', '5', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '3', '3', '1', '1', '1', '2', '1', '8', '4', '3', '0', '9', '7', '3', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '3', '4', '8', '9', '1', '5', '3', '4', '8', '2', '3', '8', '8', '1', '5', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk007Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '4', '0', '4', '1', '8', '5', '4', '3', '3', '3', '5', '3', '7', '0', '8', '4', '7', '9', '6', '8']), .str (String.ofList ['3', '9', '9', '8', '6', '2', '9', '8', '8', '5', '2', '2', '6', '5', '1', '6', '0', '3', '3', '0', '4']), .str (String.ofList ['1', '9', '9', '2', '2', '7', '6', '2', '6', '5', '4', '0', '1', '4', '8', '5', '1', '8', '8', '2', '5']), .str (String.ofList ['4', '9', '6', '8', '4', '4', '0', '5', '4', '9', '2', '6', '4', '5', '5', '8', '5', '4', '9', '7', '7']), .str (String.ofList ['3', '2', '9', '3', '8', '8', '9', '8', '4', '8', '3', '6', '6', '7', '3', '7', '8', '9', '5', '4', '8']), .str (String.ofList ['4', '4', '8', '7', '3', '5', '5', '0', '1', '4', '4', '7', '6', '7', '8', '8', '7', '2', '1', '3', '1']), .str (String.ofList ['3', '3', '1', '6', '0', '3', '8', '5', '2', '5', '2', '1', '5', '4', '0', '6', '1', '6', '8', '0', '7']), .str (String.ofList ['5', '4', '6', '0', '0', '0', '8', '6', '9', '3', '7', '4', '4', '2', '0', '9', '9', '4', '1', '4', '4']), .str (String.ofList ['5', '2', '5', '5', '0', '6', '8', '7', '4', '6', '7', '0', '9', '5', '0', '3', '1', '1', '1', '4', '7']), .str (String.ofList ['4', '1', '2', '8', '7', '3', '0', '6', '8', '7', '7', '5', '3', '6', '9', '6', '3', '8', '5', '5', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '3', '3', '1', '1', '1', '2', '1', '8', '4', '3', '0', '9', '7', '3', '1', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '3', '4', '8', '9', '1', '5', '3', '4', '8', '2', '3', '8', '8', '1', '5', '0']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_007_before_generic"
  err.flush

theorem array_moment_records_chunk_007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 86)
      (SourceJson.white (momentRecordsChunk007Chars ++ tail)) acc =
      SourceJson.array (fuel + 85) (SourceJson.white tail) (momentRecordsChunk007Push acc) := by rfl

noncomputable def momentRecordsAcc008 : List SourceJson := momentRecordsChunk007Push momentRecordsAcc007

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_007_generic_complete"
  err.flush

noncomputable def momentRecordsBlock001Chars : List Char := momentRecordsChunk004Chars ++ momentRecordsChunk005Chars ++ momentRecordsChunk006Chars ++ momentRecordsChunk007Chars
noncomputable def momentRecordsBlock001Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk007Push (momentRecordsChunk006Push (momentRecordsChunk005Push (momentRecordsChunk004Push (acc))))

theorem array_moment_records_block_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 89)
      (SourceJson.white (momentRecordsBlock001Chars ++ tail)) acc =
      SourceJson.array (fuel + 85) (SourceJson.white tail) (momentRecordsBlock001Push acc) := by
  have hinput : momentRecordsBlock001Chars ++ tail = momentRecordsChunk004Chars ++ (momentRecordsChunk005Chars ++ (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail)))) := by
    simp only [momentRecordsBlock001Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 89) (SourceJson.white (momentRecordsBlock001Chars ++ tail)) acc =
        SourceJson.array (fuel + 89) (SourceJson.white (momentRecordsChunk004Chars ++ (momentRecordsChunk005Chars ++ (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 89) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 88) (SourceJson.white (momentRecordsChunk005Chars ++ (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail))))) (momentRecordsChunk004Push (acc)) := array_moment_records_chunk_004 fuel (momentRecordsChunk005Chars ++ (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 87) (SourceJson.white (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail)))) (momentRecordsChunk005Push (momentRecordsChunk004Push (acc))) := array_moment_records_chunk_005 fuel (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail))) (momentRecordsChunk004Push (acc))
    _ = SourceJson.array (fuel + 86) (SourceJson.white (momentRecordsChunk007Chars ++ (tail))) (momentRecordsChunk006Push (momentRecordsChunk005Push (momentRecordsChunk004Push (acc)))) := array_moment_records_chunk_006 fuel (momentRecordsChunk007Chars ++ (tail)) (momentRecordsChunk005Push (momentRecordsChunk004Push (acc)))
    _ = SourceJson.array (fuel + 85) (SourceJson.white tail) (momentRecordsBlock001Push acc) := array_moment_records_chunk_007 fuel (tail) (momentRecordsChunk006Push (momentRecordsChunk005Push (momentRecordsChunk004Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_block_001_before_raw_binding"
  err.flush

theorem moment_records_block_001_prefix :
    (momentRest00 2408).take 2044 = momentRecordsBlock001Chars := by rfl

theorem moment_records_block_001_split :
    momentRest00 2408 = momentRecordsBlock001Chars ++ momentRest00 4452 := by
  calc
    momentRest00 2408 =
        (momentRest00 2408).take 2044 ++ (momentRest00 2408).drop 2044 :=
      (List.take_append_drop 2044 (momentRest00 2408)).symm
    _ = momentRecordsBlock001Chars ++ (momentRest00 2408).drop 2044 :=
      congrArg (fun p => p ++ (momentRest00 2408).drop 2044) moment_records_block_001_prefix
    _ = momentRecordsBlock001Chars ++ momentRest00 4452 :=
      congrArg (fun rest => momentRecordsBlock001Chars ++ rest) (momentRest00_drop 2408 2044)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_block_001_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_001 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 89)
      (SourceJson.white (momentRest00 2408)) acc =
      SourceJson.array (fuel + 85) (SourceJson.white (momentRest00 4452)) (momentRecordsBlock001Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 89) (SourceJson.white s) acc)
      moment_records_block_001_split).trans (array_moment_records_block_001 fuel (momentRest00 4452) acc)

theorem moment_records_through_block_001 (fuel : Nat) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRest00 364)) [] =
      SourceJson.array (fuel + 85) (SourceJson.white (momentRest00 4452)) momentRecordsAcc008 := by
  exact (moment_records_through_block_000 fuel).trans (array_moment_records_original_block_001 fuel momentRecordsAcc004)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_block_001_complete"
  err.flush

#print axioms array_moment_records_chunk_004
#print axioms array_moment_records_chunk_005
#print axioms array_moment_records_chunk_006
#print axioms array_moment_records_chunk_007
#print axioms array_moment_records_block_001
#print axioms moment_records_block_001_prefix
#print axioms moment_records_block_001_split
#print axioms array_moment_records_original_block_001
#print axioms moment_records_through_block_001

end ImbalancedChen.P2OriginalSaving19Moment00Parsing
