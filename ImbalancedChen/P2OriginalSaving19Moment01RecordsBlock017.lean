import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock016

/-! Original moment records block 17. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk068Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '9', '6', '1', '1', '5', '4', '0', '0', '9', '2', '6', '5', '0', '0', '3', '8', '6', '5', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '0', '2', '0', '4', '5', '1', '6', '8', '8', '9', '1', '2', '7', '3', '4', '8', '1', '0', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '8', '1', '6', '4', '2', '0', '8', '7', '1', '7', '3', '8', '7', '1', '0', '5', '5', '9', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '3', '2', '3', '4', '6', '4', '5', '7', '1', '3', '7', '3', '2', '1', '0', '8', '5', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '7', '9', '8', '5', '2', '4', '0', '7', '6', '5', '9', '8', '0', '6', '8', '7', '8', '4', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '9', '5', '6', '3', '6', '6', '5', '9', '2', '7', '1', '4', '4', '9', '4', '3', '8', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '5', '2', '1', '5', '9', '1', '0', '1', '6', '3', '0', '6', '4', '4', '3', '8', '4', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '3', '1', '5', '5', '0', '4', '6', '2', '7', '8', '2', '9', '8', '8', '8', '9', '7', '6', '8', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '2', '8', '3', '6', '0', '1', '8', '5', '4', '0', '2', '2', '9', '0', '0', '4', '5', '3', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '2', '8', '9', '1', '3', '8', '6', '5', '7', '6', '7', '1', '6', '2', '4', '3', '9', '8', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '0', '1', '8', '1', '3', '8', '2', '6', '2', '3', '3', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '1', '6', '6', '0', '5', '3', '2', '2', '1', '5', '1', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk068Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['6', '8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '0', '9', '6', '1', '1', '5', '4', '0', '0', '9', '2', '6', '5', '0', '0', '3', '8', '6', '5', '0', '5']), .str (String.ofList ['3', '4', '0', '2', '0', '4', '5', '1', '6', '8', '8', '9', '1', '2', '7', '3', '4', '8', '1', '0', '2', '1']), .str (String.ofList ['2', '5', '8', '1', '6', '4', '2', '0', '8', '7', '1', '7', '3', '8', '7', '1', '0', '5', '5', '9', '4']), .str (String.ofList ['6', '2', '3', '2', '3', '4', '6', '4', '5', '7', '1', '3', '7', '3', '2', '1', '0', '8', '5', '2', '0']), .str (String.ofList ['1', '5', '7', '9', '8', '5', '2', '4', '0', '7', '6', '5', '9', '8', '0', '6', '8', '7', '8', '4', '9', '8']), .str (String.ofList ['1', '8', '3', '9', '5', '6', '3', '6', '6', '5', '9', '2', '7', '1', '4', '4', '9', '4', '3', '8', '8', '3']), .str (String.ofList ['1', '4', '4', '5', '2', '1', '5', '9', '1', '0', '1', '6', '3', '0', '6', '4', '4', '3', '8', '4', '6', '3']), .str (String.ofList ['1', '2', '3', '1', '5', '5', '0', '4', '6', '2', '7', '8', '2', '9', '8', '8', '8', '9', '7', '6', '8', '5']), .str (String.ofList ['1', '3', '2', '2', '8', '3', '6', '0', '1', '8', '5', '4', '0', '2', '2', '9', '0', '0', '4', '5', '3', '3']), .str (String.ofList ['1', '3', '2', '2', '8', '9', '1', '3', '8', '6', '5', '7', '6', '7', '1', '6', '2', '4', '3', '9', '8', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '1', '0', '1', '8', '1', '3', '8', '2', '6', '2', '3', '3', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '1', '1', '6', '6', '0', '5', '3', '2', '2', '1', '5', '1', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_068_before_generic"
  err.flush

theorem array_moment_records_chunk_068 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 113)
      (SourceJson.white (momentRecordsChunk068Chars ++ tail)) acc =
      SourceJson.array (fuel + 112) (SourceJson.white tail) (momentRecordsChunk068Push acc) := by rfl

noncomputable def momentRecordsAcc069 : List SourceJson := momentRecordsChunk068Push momentRecordsAcc068

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_068_generic_complete"
  err.flush

noncomputable def momentRecordsChunk069Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '8', '0', '9', '1', '9', '0', '4', '3', '9', '0', '0', '9', '4', '2', '1', '9', '4', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '4', '6', '3', '3', '3', '8', '3', '4', '3', '5', '0', '1', '3', '9', '3', '9', '5', '6', '9', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '3', '0', '6', '1', '2', '3', '6', '8', '6', '5', '3', '5', '5', '8', '2', '9', '8', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '2', '2', '9', '1', '9', '3', '9', '9', '1', '3', '9', '1', '5', '9', '4', '4', '3', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '2', '8', '8', '4', '9', '3', '8', '7', '7', '2', '3', '0', '1', '8', '1', '0', '2', '9', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '0', '1', '7', '6', '9', '2', '0', '3', '8', '9', '8', '4', '5', '7', '7', '6', '7', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '3', '3', '8', '5', '8', '6', '2', '0', '6', '2', '7', '4', '5', '8', '3', '1', '0', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '3', '0', '8', '5', '1', '4', '0', '3', '3', '5', '2', '8', '4', '7', '0', '6', '7', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '1', '6', '4', '1', '2', '2', '7', '6', '2', '2', '7', '8', '7', '2', '6', '5', '4', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '1', '7', '1', '0', '5', '1', '7', '0', '4', '0', '9', '5', '4', '3', '6', '9', '4', '3', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '0', '5', '8', '3', '1', '3', '2', '7', '9', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '0', '9', '3', '2', '7', '7', '5', '1', '2', '1', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk069Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['6', '9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '4', '6', '8', '0', '9', '1', '9', '0', '4', '3', '9', '0', '0', '9', '4', '2', '1', '9', '4', '4', '9']), .str (String.ofList ['2', '4', '4', '6', '3', '3', '3', '8', '3', '4', '3', '5', '0', '1', '3', '9', '3', '9', '5', '6', '9', '7']), .str (String.ofList ['1', '9', '3', '0', '6', '1', '2', '3', '6', '8', '6', '5', '3', '5', '5', '8', '2', '9', '8', '9', '5']), .str (String.ofList ['6', '9', '2', '2', '9', '1', '9', '3', '9', '9', '1', '3', '9', '1', '5', '9', '4', '4', '3', '8', '8']), .str (String.ofList ['1', '7', '9', '2', '8', '8', '4', '9', '3', '8', '7', '7', '2', '3', '0', '1', '8', '1', '0', '2', '9', '7']), .str (String.ofList ['1', '8', '6', '0', '1', '7', '6', '9', '2', '0', '3', '8', '9', '8', '4', '5', '7', '7', '6', '7', '6', '3']), .str (String.ofList ['1', '2', '4', '3', '3', '8', '5', '8', '6', '2', '0', '6', '2', '7', '4', '5', '8', '3', '1', '0', '7', '3']), .str (String.ofList ['1', '1', '0', '3', '0', '8', '5', '1', '4', '0', '3', '3', '5', '2', '8', '4', '7', '0', '6', '7', '0', '9']), .str (String.ofList ['9', '7', '1', '6', '4', '1', '2', '2', '7', '6', '2', '2', '7', '8', '7', '2', '6', '5', '4', '4', '2']), .str (String.ofList ['9', '7', '1', '7', '1', '0', '5', '1', '7', '0', '4', '0', '9', '5', '4', '3', '6', '9', '4', '3', '6'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '0', '5', '8', '3', '1', '3', '2', '7', '9', '6', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '0', '9', '3', '2', '7', '7', '5', '1', '2', '1', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_069_before_generic"
  err.flush

theorem array_moment_records_chunk_069 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 112)
      (SourceJson.white (momentRecordsChunk069Chars ++ tail)) acc =
      SourceJson.array (fuel + 111) (SourceJson.white tail) (momentRecordsChunk069Push acc) := by rfl

noncomputable def momentRecordsAcc070 : List SourceJson := momentRecordsChunk069Push momentRecordsAcc069

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_069_generic_complete"
  err.flush

noncomputable def momentRecordsChunk070Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '4', '8', '7', '8', '8', '4', '2', '2', '5', '9', '0', '1', '8', '6', '5', '3', '7', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '8', '1', '1', '1', '6', '8', '7', '7', '9', '0', '0', '1', '2', '4', '3', '0', '9', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '8', '9', '4', '9', '5', '5', '6', '4', '5', '2', '3', '8', '2', '3', '4', '3', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '8', '1', '7', '6', '1', '8', '6', '7', '6', '3', '0', '7', '4', '1', '4', '6', '5', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '0', '3', '0', '9', '7', '6', '5', '3', '4', '8', '1', '0', '2', '7', '2', '6', '5', '7', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '8', '2', '4', '5', '7', '1', '3', '3', '7', '2', '2', '1', '4', '7', '5', '6', '5', '4', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '1', '9', '9', '7', '1', '3', '9', '8', '6', '4', '6', '9', '2', '6', '3', '0', '5', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '0', '9', '5', '4', '4', '1', '3', '2', '8', '1', '4', '2', '6', '6', '6', '3', '8', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '1', '4', '3', '2', '5', '4', '9', '5', '3', '6', '9', '6', '3', '9', '6', '9', '8', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '1', '5', '0', '5', '8', '6', '9', '4', '8', '7', '2', '4', '7', '5', '2', '4', '7', '5', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '8', '7', '4', '0', '0', '6', '3', '8', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '9', '0', '6', '2', '8', '2', '2', '0', '7', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk070Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['7', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '4', '0', '4', '8', '7', '8', '8', '4', '2', '2', '5', '9', '0', '1', '8', '6', '5', '3', '7', '4', '5']), .str (String.ofList ['1', '4', '0', '8', '1', '1', '1', '6', '8', '7', '7', '9', '0', '0', '1', '2', '4', '3', '0', '9', '8', '3']), .str (String.ofList ['1', '2', '1', '8', '9', '4', '9', '5', '5', '6', '4', '5', '2', '3', '8', '2', '3', '4', '3', '7', '8']), .str (String.ofList ['6', '3', '8', '1', '7', '6', '1', '8', '6', '7', '6', '3', '0', '7', '4', '1', '4', '6', '5', '1', '7']), .str (String.ofList ['1', '8', '0', '3', '0', '9', '7', '6', '5', '3', '4', '8', '1', '0', '2', '7', '2', '6', '5', '7', '0', '9']), .str (String.ofList ['1', '2', '5', '8', '2', '4', '5', '7', '1', '3', '3', '7', '2', '2', '1', '4', '7', '5', '6', '5', '4', '4']), .str (String.ofList ['9', '8', '1', '9', '9', '7', '1', '3', '9', '8', '6', '4', '6', '9', '2', '6', '3', '0', '5', '4', '8']), .str (String.ofList ['8', '7', '0', '9', '5', '4', '4', '1', '3', '2', '8', '1', '4', '2', '6', '6', '6', '3', '8', '2', '4']), .str (String.ofList ['7', '7', '1', '4', '3', '2', '5', '4', '9', '5', '3', '6', '9', '6', '3', '9', '6', '9', '8', '8', '6']), .str (String.ofList ['7', '7', '1', '5', '0', '5', '8', '6', '9', '4', '8', '7', '2', '4', '7', '5', '2', '4', '7', '5', '0'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '8', '7', '4', '0', '0', '6', '3', '8', '9', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '9', '0', '6', '2', '8', '2', '2', '0', '7', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_070_before_generic"
  err.flush

theorem array_moment_records_chunk_070 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 111)
      (SourceJson.white (momentRecordsChunk070Chars ++ tail)) acc =
      SourceJson.array (fuel + 110) (SourceJson.white tail) (momentRecordsChunk070Push acc) := by rfl

noncomputable def momentRecordsAcc071 : List SourceJson := momentRecordsChunk070Push momentRecordsAcc070

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_070_generic_complete"
  err.flush

noncomputable def momentRecordsChunk071Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '7', '6', '4', '8', '1', '8', '5', '8', '8', '6', '1', '8', '4', '8', '4', '5', '7', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '2', '4', '6', '9', '2', '7', '6', '2', '3', '9', '7', '9', '8', '3', '1', '1', '4', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '3', '3', '3', '6', '5', '9', '9', '7', '3', '1', '5', '2', '1', '3', '9', '6', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '7', '9', '0', '3', '3', '0', '5', '9', '8', '1', '1', '2', '6', '6', '7', '7', '9', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '2', '9', '2', '9', '0', '2', '7', '0', '6', '6', '9', '3', '2', '4', '0', '3', '1', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '8', '9', '7', '3', '6', '0', '2', '7', '2', '5', '6', '0', '8', '2', '1', '5', '8', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '9', '0', '0', '2', '8', '7', '5', '7', '9', '3', '4', '2', '6', '3', '9', '1', '8', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '0', '8', '7', '9', '9', '3', '4', '1', '3', '2', '8', '2', '0', '1', '9', '4', '3', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '4', '2', '7', '6', '9', '2', '7', '7', '2', '1', '1', '7', '7', '9', '9', '7', '7', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '9', '5', '9', '0', '1', '1', '9', '1', '5', '4', '0', '2', '7', '3', '8', '7', '8', '4', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '1', '8', '2', '4', '8', '7', '1', '4', '5', '1', '6', '4', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '2', '4', '6', '7', '2', '6', '3', '6', '6', '9', '3', '5', '0', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk071Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['7', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '0', '7', '7', '6', '4', '8', '1', '8', '5', '8', '8', '6', '1', '8', '4', '8', '4', '5', '7', '2', '8']), .str (String.ofList ['1', '0', '7', '2', '4', '6', '9', '2', '7', '6', '2', '3', '9', '7', '9', '8', '3', '1', '1', '4', '8', '0']), .str (String.ofList ['1', '2', '4', '3', '3', '3', '6', '5', '9', '9', '7', '3', '1', '5', '2', '1', '3', '9', '6', '6', '4']), .str (String.ofList ['5', '8', '7', '9', '0', '3', '3', '0', '5', '9', '8', '1', '1', '2', '6', '6', '7', '7', '9', '0', '2']), .str (String.ofList ['1', '2', '0', '2', '9', '2', '9', '0', '2', '7', '0', '6', '6', '9', '3', '2', '4', '0', '3', '1', '7', '4']), .str (String.ofList ['1', '1', '9', '8', '9', '7', '3', '6', '0', '2', '7', '2', '5', '6', '0', '8', '2', '1', '5', '8', '4', '5']), .str (String.ofList ['8', '7', '9', '0', '0', '2', '8', '7', '5', '7', '9', '3', '4', '2', '6', '3', '9', '1', '8', '1', '5']), .str (String.ofList ['7', '8', '0', '8', '7', '9', '9', '3', '4', '1', '3', '2', '8', '2', '0', '1', '9', '4', '3', '7', '5']), .str (String.ofList ['7', '4', '4', '2', '7', '6', '9', '2', '7', '7', '2', '1', '1', '7', '7', '9', '9', '7', '7', '6', '3']), .str (String.ofList ['7', '5', '9', '5', '9', '0', '1', '1', '9', '1', '5', '4', '0', '2', '7', '3', '8', '7', '8', '4', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '1', '8', '2', '4', '8', '7', '1', '4', '5', '1', '6', '4', '0', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '2', '4', '6', '7', '2', '6', '3', '6', '6', '9', '3', '5', '0', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_071_before_generic"
  err.flush

theorem array_moment_records_chunk_071 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 110)
      (SourceJson.white (momentRecordsChunk071Chars ++ tail)) acc =
      SourceJson.array (fuel + 109) (SourceJson.white tail) (momentRecordsChunk071Push acc) := by rfl

noncomputable def momentRecordsAcc072 : List SourceJson := momentRecordsChunk071Push momentRecordsAcc071

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_071_generic_complete"
  err.flush

noncomputable def momentRecordsBlock017Chars : List Char := momentRecordsChunk068Chars ++ momentRecordsChunk069Chars ++ momentRecordsChunk070Chars ++ momentRecordsChunk071Chars
noncomputable def momentRecordsBlock017Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk071Push (momentRecordsChunk070Push (momentRecordsChunk069Push (momentRecordsChunk068Push (acc))))

theorem array_moment_records_block_017 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 113)
      (SourceJson.white (momentRecordsBlock017Chars ++ tail)) acc =
      SourceJson.array (fuel + 109) (SourceJson.white tail) (momentRecordsBlock017Push acc) := by
  have hinput : momentRecordsBlock017Chars ++ tail = momentRecordsChunk068Chars ++ (momentRecordsChunk069Chars ++ (momentRecordsChunk070Chars ++ (momentRecordsChunk071Chars ++ (tail)))) := by
    simp only [momentRecordsBlock017Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 113) (SourceJson.white (momentRecordsBlock017Chars ++ tail)) acc =
        SourceJson.array (fuel + 113) (SourceJson.white (momentRecordsChunk068Chars ++ (momentRecordsChunk069Chars ++ (momentRecordsChunk070Chars ++ (momentRecordsChunk071Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 113) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 112) (SourceJson.white (momentRecordsChunk069Chars ++ (momentRecordsChunk070Chars ++ (momentRecordsChunk071Chars ++ (tail))))) (momentRecordsChunk068Push (acc)) := array_moment_records_chunk_068 fuel (momentRecordsChunk069Chars ++ (momentRecordsChunk070Chars ++ (momentRecordsChunk071Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 111) (SourceJson.white (momentRecordsChunk070Chars ++ (momentRecordsChunk071Chars ++ (tail)))) (momentRecordsChunk069Push (momentRecordsChunk068Push (acc))) := array_moment_records_chunk_069 fuel (momentRecordsChunk070Chars ++ (momentRecordsChunk071Chars ++ (tail))) (momentRecordsChunk068Push (acc))
    _ = SourceJson.array (fuel + 110) (SourceJson.white (momentRecordsChunk071Chars ++ (tail))) (momentRecordsChunk070Push (momentRecordsChunk069Push (momentRecordsChunk068Push (acc)))) := array_moment_records_chunk_070 fuel (momentRecordsChunk071Chars ++ (tail)) (momentRecordsChunk069Push (momentRecordsChunk068Push (acc)))
    _ = SourceJson.array (fuel + 109) (SourceJson.white tail) (momentRecordsBlock017Push acc) := array_moment_records_chunk_071 fuel (tail) (momentRecordsChunk070Push (momentRecordsChunk069Push (momentRecordsChunk068Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_017_before_raw_binding"
  err.flush

theorem moment_records_block_017_prefix :
    (momentRest01 35763).take 2054 = momentRecordsBlock017Chars := by rfl

theorem moment_records_block_017_split :
    momentRest01 35763 = momentRecordsBlock017Chars ++ momentRest01 37817 := by
  calc
    momentRest01 35763 =
        (momentRest01 35763).take 2054 ++ (momentRest01 35763).drop 2054 :=
      (List.take_append_drop 2054 (momentRest01 35763)).symm
    _ = momentRecordsBlock017Chars ++ (momentRest01 35763).drop 2054 :=
      congrArg (fun p => p ++ (momentRest01 35763).drop 2054) moment_records_block_017_prefix
    _ = momentRecordsBlock017Chars ++ momentRest01 37817 :=
      congrArg (fun rest => momentRecordsBlock017Chars ++ rest) (momentRest01_drop 35763 2054)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_017_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_017 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 113)
      (SourceJson.white (momentRest01 35763)) acc =
      SourceJson.array (fuel + 109) (SourceJson.white (momentRest01 37817)) (momentRecordsBlock017Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 113) (SourceJson.white s) acc)
      moment_records_block_017_split).trans (array_moment_records_block_017 fuel (momentRest01 37817) acc)

theorem moment_records_through_block_017 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 109) (SourceJson.white (momentRest01 37817)) momentRecordsAcc072 := by
  exact (moment_records_through_block_016 fuel).trans (array_moment_records_original_block_017 fuel momentRecordsAcc068)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_017_complete"
  err.flush

#print axioms array_moment_records_chunk_068
#print axioms array_moment_records_chunk_069
#print axioms array_moment_records_chunk_070
#print axioms array_moment_records_chunk_071
#print axioms array_moment_records_block_017
#print axioms moment_records_block_017_prefix
#print axioms moment_records_block_017_split
#print axioms array_moment_records_original_block_017
#print axioms moment_records_through_block_017

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
