import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock001

/-! Original moment records block 2. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk008Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '5', '3', '1', '2', '0', '1', '6', '5', '8', '3', '8', '5', '0', '0', '3', '4', '2', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '6', '3', '1', '6', '0', '9', '5', '3', '0', '6', '0', '4', '3', '9', '2', '5', '5', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '3', '7', '0', '4', '6', '3', '7', '0', '8', '8', '2', '2', '1', '0', '9', '2', '6', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '5', '0', '6', '0', '9', '2', '3', '4', '2', '5', '0', '7', '3', '4', '8', '9', '6', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '1', '6', '7', '6', '7', '5', '0', '2', '4', '1', '8', '0', '5', '0', '1', '4', '3', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '6', '0', '5', '2', '2', '1', '2', '8', '1', '1', '8', '6', '7', '3', '4', '9', '6', '7', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '9', '8', '3', '2', '8', '8', '8', '5', '0', '5', '1', '9', '4', '4', '8', '7', '6', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '7', '6', '3', '3', '5', '5', '6', '0', '4', '0', '4', '8', '1', '3', '0', '6', '4', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '9', '3', '5', '3', '4', '4', '3', '4', '6', '4', '2', '3', '4', '6', '5', '3', '7', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '1', '8', '7', '9', '6', '6', '5', '0', '8', '5', '5', '9', '7', '0', '3', '9', '1', '5', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '0', '7', '3', '0', '3', '0', '8', '3', '9', '0', '8', '7', '6', '7', '9', '0', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '1', '2', '6', '3', '0', '3', '6', '2', '9', '6', '7', '0', '5', '9', '2', '3', '3', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk008Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '7', '5', '3', '1', '2', '0', '1', '6', '5', '8', '3', '8', '5', '0', '0', '3', '4', '2', '9', '3']), .str (String.ofList ['1', '4', '6', '6', '3', '1', '6', '0', '9', '5', '3', '0', '6', '0', '4', '3', '9', '2', '5', '5', '9', '2']), .str (String.ofList ['2', '6', '3', '7', '0', '4', '6', '3', '7', '0', '8', '8', '2', '2', '1', '0', '9', '2', '6', '3', '5']), .str (String.ofList ['3', '8', '5', '0', '6', '0', '9', '2', '3', '4', '2', '5', '0', '7', '3', '4', '8', '9', '6', '9', '2']), .str (String.ofList ['6', '0', '1', '6', '7', '6', '7', '5', '0', '2', '4', '1', '8', '0', '5', '0', '1', '4', '3', '3', '1']), .str (String.ofList ['1', '6', '6', '0', '5', '2', '2', '1', '2', '8', '1', '1', '8', '6', '7', '3', '4', '9', '6', '7', '5', '6']), .str (String.ofList ['7', '4', '9', '8', '3', '2', '8', '8', '8', '5', '0', '5', '1', '9', '4', '4', '8', '7', '6', '2', '7']), .str (String.ofList ['7', '6', '7', '6', '3', '3', '5', '5', '6', '0', '4', '0', '4', '8', '1', '3', '0', '6', '4', '5', '9']), .str (String.ofList ['1', '0', '7', '9', '3', '5', '3', '4', '4', '3', '4', '6', '4', '2', '3', '4', '6', '5', '3', '7', '6', '1']), .str (String.ofList ['7', '2', '1', '8', '7', '9', '6', '6', '5', '0', '8', '5', '5', '9', '7', '0', '3', '9', '1', '5', '4'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['7', '0', '7', '3', '0', '3', '0', '8', '3', '9', '0', '8', '7', '6', '7', '9', '0', '1', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['7', '1', '2', '6', '3', '0', '3', '6', '2', '9', '6', '7', '0', '5', '9', '2', '3', '3', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_008_before_generic"
  err.flush

theorem array_moment_records_chunk_008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 173)
      (SourceJson.white (momentRecordsChunk008Chars ++ tail)) acc =
      SourceJson.array (fuel + 172) (SourceJson.white tail) (momentRecordsChunk008Push acc) := by rfl

noncomputable def momentRecordsAcc009 : List SourceJson := momentRecordsChunk008Push momentRecordsAcc008

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_008_generic_complete"
  err.flush

noncomputable def momentRecordsChunk009Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '4', '8', '3', '9', '8', '7', '0', '2', '7', '7', '5', '2', '7', '4', '5', '3', '9', '9', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '2', '3', '3', '1', '0', '6', '9', '1', '3', '6', '8', '8', '3', '2', '2', '1', '6', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '5', '3', '7', '9', '7', '0', '5', '7', '2', '8', '9', '8', '1', '7', '8', '6', '2', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '6', '0', '5', '9', '5', '5', '5', '9', '3', '6', '1', '8', '9', '8', '2', '0', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '3', '4', '9', '2', '4', '1', '2', '6', '4', '3', '4', '1', '5', '7', '2', '1', '7', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '4', '5', '6', '7', '8', '7', '7', '3', '1', '4', '6', '7', '4', '8', '1', '0', '1', '3', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '4', '9', '8', '0', '0', '9', '8', '5', '0', '2', '9', '9', '3', '4', '7', '8', '5', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '6', '7', '3', '5', '0', '2', '7', '5', '8', '2', '9', '1', '0', '8', '6', '0', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '5', '0', '5', '0', '4', '8', '2', '8', '1', '3', '2', '6', '2', '2', '7', '1', '1', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '6', '1', '9', '2', '6', '3', '0', '7', '3', '0', '1', '4', '0', '9', '7', '9', '9', '8', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '5', '0', '6', '1', '6', '2', '3', '3', '5', '1', '7', '3', '1', '6', '1', '1', '9', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '5', '7', '0', '2', '9', '2', '5', '3', '6', '4', '3', '2', '3', '1', '8', '1', '1', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk009Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '3', '4', '8', '3', '9', '8', '7', '0', '2', '7', '7', '5', '2', '7', '4', '5', '3', '9', '9', '9']), .str (String.ofList ['1', '4', '5', '2', '3', '3', '1', '0', '6', '9', '1', '3', '6', '8', '8', '3', '2', '2', '1', '6', '4', '6']), .str (String.ofList ['2', '4', '5', '3', '7', '9', '7', '0', '5', '7', '2', '8', '9', '8', '1', '7', '8', '6', '2', '3', '6']), .str (String.ofList ['3', '3', '2', '6', '0', '5', '9', '5', '5', '5', '9', '3', '6', '1', '8', '9', '8', '2', '0', '6', '0']), .str (String.ofList ['5', '7', '3', '4', '9', '2', '4', '1', '2', '6', '4', '3', '4', '1', '5', '7', '2', '1', '7', '5', '3']), .str (String.ofList ['1', '7', '4', '5', '6', '7', '8', '7', '7', '3', '1', '4', '6', '7', '4', '8', '1', '0', '1', '3', '1', '9']), .str (String.ofList ['9', '3', '4', '9', '8', '0', '0', '9', '8', '5', '0', '2', '9', '9', '3', '4', '7', '8', '5', '1', '4']), .str (String.ofList ['6', '8', '9', '6', '7', '3', '5', '0', '2', '7', '5', '8', '2', '9', '1', '0', '8', '6', '0', '3', '1']), .str (String.ofList ['9', '5', '5', '0', '5', '0', '4', '8', '2', '8', '1', '3', '2', '6', '2', '2', '7', '1', '1', '7', '3']), .str (String.ofList ['8', '1', '6', '1', '9', '2', '6', '3', '0', '7', '3', '0', '1', '4', '0', '9', '7', '9', '9', '8', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '5', '0', '6', '1', '6', '2', '3', '3', '5', '1', '7', '3', '1', '6', '1', '1', '9', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '5', '7', '0', '2', '9', '2', '5', '3', '6', '4', '3', '2', '3', '1', '8', '1', '1', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_009_before_generic"
  err.flush

theorem array_moment_records_chunk_009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 172)
      (SourceJson.white (momentRecordsChunk009Chars ++ tail)) acc =
      SourceJson.array (fuel + 171) (SourceJson.white tail) (momentRecordsChunk009Push acc) := by rfl

noncomputable def momentRecordsAcc010 : List SourceJson := momentRecordsChunk009Push momentRecordsAcc009

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_009_generic_complete"
  err.flush

noncomputable def momentRecordsChunk010Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '5', '7', '8', '7', '6', '4', '7', '0', '7', '4', '9', '4', '3', '3', '9', '1', '3', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '7', '6', '4', '4', '2', '3', '1', '4', '0', '7', '4', '3', '6', '9', '2', '1', '5', '0', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '6', '5', '9', '6', '5', '8', '5', '3', '3', '0', '0', '8', '8', '5', '1', '8', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '6', '3', '6', '5', '7', '3', '6', '7', '2', '8', '6', '1', '0', '1', '0', '6', '9', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '6', '3', '5', '8', '7', '4', '4', '8', '3', '9', '7', '4', '4', '6', '8', '8', '6', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '0', '3', '0', '0', '9', '5', '5', '7', '9', '2', '5', '7', '2', '6', '9', '9', '8', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '7', '4', '8', '5', '4', '7', '6', '9', '0', '0', '4', '1', '9', '7', '2', '5', '7', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '7', '2', '7', '6', '0', '5', '2', '9', '0', '4', '6', '3', '5', '6', '7', '4', '4', '5', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '8', '4', '5', '7', '4', '9', '6', '8', '8', '2', '3', '1', '1', '9', '3', '7', '0', '7', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '0', '9', '4', '8', '5', '1', '0', '5', '4', '7', '5', '4', '1', '0', '6', '9', '5', '8', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '7', '1', '8', '2', '0', '2', '5', '6', '2', '3', '6', '7', '3', '3', '5', '3', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '7', '4', '1', '5', '7', '2', '1', '8', '9', '5', '2', '1', '0', '1', '1', '5', '5', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk010Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '0', '6', '5', '7', '8', '7', '6', '4', '7', '0', '7', '4', '9', '4', '3', '3', '9', '1', '3', '7', '2']), .str (String.ofList ['1', '2', '4', '7', '6', '4', '4', '2', '3', '1', '4', '0', '7', '4', '3', '6', '9', '2', '1', '5', '0', '3']), .str (String.ofList ['2', '0', '8', '6', '5', '9', '6', '5', '8', '5', '3', '3', '0', '0', '8', '8', '5', '1', '8', '2', '8']), .str (String.ofList ['1', '6', '1', '6', '3', '6', '5', '7', '3', '6', '7', '2', '8', '6', '1', '0', '1', '0', '6', '9', '7']), .str (String.ofList ['4', '8', '6', '3', '5', '8', '7', '4', '4', '8', '3', '9', '7', '4', '4', '6', '8', '8', '6', '3', '9']), .str (String.ofList ['1', '1', '0', '0', '3', '0', '0', '9', '5', '5', '7', '9', '2', '5', '7', '2', '6', '9', '9', '8', '0', '7']), .str (String.ofList ['9', '4', '7', '4', '8', '5', '4', '7', '6', '9', '0', '0', '4', '1', '9', '7', '2', '5', '7', '6', '3']), .str (String.ofList ['6', '8', '7', '2', '7', '6', '0', '5', '2', '9', '0', '4', '6', '3', '5', '6', '7', '4', '4', '5', '4']), .str (String.ofList ['9', '3', '8', '4', '5', '7', '4', '9', '6', '8', '8', '2', '3', '1', '1', '9', '3', '7', '0', '7', '9']), .str (String.ofList ['7', '3', '0', '9', '4', '8', '5', '1', '0', '5', '4', '7', '5', '4', '1', '0', '6', '9', '5', '8', '7'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '7', '1', '8', '2', '0', '2', '5', '6', '2', '3', '6', '7', '3', '3', '5', '3', '9', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '7', '4', '1', '5', '7', '2', '1', '8', '9', '5', '2', '1', '0', '1', '1', '5', '5', '8']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_010_before_generic"
  err.flush

theorem array_moment_records_chunk_010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 171)
      (SourceJson.white (momentRecordsChunk010Chars ++ tail)) acc =
      SourceJson.array (fuel + 170) (SourceJson.white tail) (momentRecordsChunk010Push acc) := by rfl

noncomputable def momentRecordsAcc011 : List SourceJson := momentRecordsChunk010Push momentRecordsAcc010

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_010_generic_complete"
  err.flush

noncomputable def momentRecordsChunk011Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '8', '1', '2', '1', '2', '7', '1', '7', '6', '2', '8', '4', '6', '7', '5', '1', '1', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '4', '3', '0', '4', '6', '6', '0', '2', '7', '0', '7', '7', '4', '0', '7', '3', '6', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '5', '1', '2', '2', '9', '0', '4', '1', '1', '1', '6', '0', '9', '8', '7', '0', '5', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '2', '4', '5', '0', '1', '1', '8', '5', '5', '2', '4', '3', '9', '2', '7', '1', '3', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '7', '3', '3', '0', '4', '0', '0', '3', '7', '1', '3', '3', '1', '0', '6', '9', '1', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '7', '4', '8', '2', '2', '0', '5', '8', '0', '0', '7', '4', '5', '4', '7', '1', '8', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '0', '0', '3', '8', '3', '2', '0', '9', '2', '4', '3', '5', '8', '8', '9', '9', '4', '7', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '1', '8', '3', '1', '0', '6', '1', '3', '0', '9', '6', '4', '2', '7', '8', '0', '2', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '4', '0', '2', '4', '0', '2', '0', '8', '0', '9', '8', '4', '5', '5', '8', '9', '5', '7', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '2', '7', '6', '6', '6', '7', '1', '2', '3', '3', '3', '2', '1', '8', '1', '8', '3', '8', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '7', '0', '6', '3', '3', '3', '8', '7', '3', '2', '7', '9', '7', '1', '0', '7', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '7', '4', '8', '4', '1', '9', '7', '9', '7', '0', '4', '5', '7', '4', '9', '5', '4', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk011Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '3', '3', '8', '1', '2', '1', '2', '7', '1', '7', '6', '2', '8', '4', '6', '7', '5', '1', '1', '2', '7']), .str (String.ofList ['1', '4', '5', '4', '3', '0', '4', '6', '6', '0', '2', '7', '0', '7', '7', '4', '0', '7', '3', '6', '7', '6']), .str (String.ofList ['2', '5', '5', '1', '2', '2', '9', '0', '4', '1', '1', '1', '6', '0', '9', '8', '7', '0', '5', '9', '6']), .str (String.ofList ['3', '5', '2', '4', '5', '0', '1', '1', '8', '5', '5', '2', '4', '3', '9', '2', '7', '1', '3', '6', '9']), .str (String.ofList ['5', '0', '7', '3', '3', '0', '4', '0', '0', '3', '7', '1', '3', '3', '1', '0', '6', '9', '1', '7', '3']), .str (String.ofList ['1', '6', '7', '7', '4', '8', '2', '2', '0', '5', '8', '0', '0', '7', '4', '5', '4', '7', '1', '8', '3', '7']), .str (String.ofList ['7', '3', '0', '0', '3', '8', '3', '2', '0', '9', '2', '4', '3', '5', '8', '8', '9', '9', '4', '7', '7']), .str (String.ofList ['6', '6', '1', '8', '3', '1', '0', '6', '1', '3', '0', '9', '6', '4', '2', '7', '8', '0', '2', '9', '8']), .str (String.ofList ['1', '0', '9', '4', '0', '2', '4', '0', '2', '0', '8', '0', '9', '8', '4', '5', '5', '8', '9', '5', '7', '9']), .str (String.ofList ['8', '1', '2', '7', '6', '6', '6', '7', '1', '2', '3', '3', '3', '2', '1', '8', '1', '8', '3', '8', '0'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '7', '0', '6', '3', '3', '3', '8', '7', '3', '2', '7', '9', '7', '1', '0', '7', '2', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '7', '4', '8', '4', '1', '9', '7', '9', '7', '0', '4', '5', '7', '4', '9', '5', '4', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_011_before_generic"
  err.flush

theorem array_moment_records_chunk_011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 170)
      (SourceJson.white (momentRecordsChunk011Chars ++ tail)) acc =
      SourceJson.array (fuel + 169) (SourceJson.white tail) (momentRecordsChunk011Push acc) := by rfl

noncomputable def momentRecordsAcc012 : List SourceJson := momentRecordsChunk011Push momentRecordsAcc011

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_011_generic_complete"
  err.flush

noncomputable def momentRecordsBlock002Chars : List Char := momentRecordsChunk008Chars ++ momentRecordsChunk009Chars ++ momentRecordsChunk010Chars ++ momentRecordsChunk011Chars
noncomputable def momentRecordsBlock002Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk011Push (momentRecordsChunk010Push (momentRecordsChunk009Push (momentRecordsChunk008Push (acc))))

theorem array_moment_records_block_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 173)
      (SourceJson.white (momentRecordsBlock002Chars ++ tail)) acc =
      SourceJson.array (fuel + 169) (SourceJson.white tail) (momentRecordsBlock002Push acc) := by
  have hinput : momentRecordsBlock002Chars ++ tail = momentRecordsChunk008Chars ++ (momentRecordsChunk009Chars ++ (momentRecordsChunk010Chars ++ (momentRecordsChunk011Chars ++ (tail)))) := by
    simp only [momentRecordsBlock002Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 173) (SourceJson.white (momentRecordsBlock002Chars ++ tail)) acc =
        SourceJson.array (fuel + 173) (SourceJson.white (momentRecordsChunk008Chars ++ (momentRecordsChunk009Chars ++ (momentRecordsChunk010Chars ++ (momentRecordsChunk011Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 173) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 172) (SourceJson.white (momentRecordsChunk009Chars ++ (momentRecordsChunk010Chars ++ (momentRecordsChunk011Chars ++ (tail))))) (momentRecordsChunk008Push (acc)) := array_moment_records_chunk_008 fuel (momentRecordsChunk009Chars ++ (momentRecordsChunk010Chars ++ (momentRecordsChunk011Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 171) (SourceJson.white (momentRecordsChunk010Chars ++ (momentRecordsChunk011Chars ++ (tail)))) (momentRecordsChunk009Push (momentRecordsChunk008Push (acc))) := array_moment_records_chunk_009 fuel (momentRecordsChunk010Chars ++ (momentRecordsChunk011Chars ++ (tail))) (momentRecordsChunk008Push (acc))
    _ = SourceJson.array (fuel + 170) (SourceJson.white (momentRecordsChunk011Chars ++ (tail))) (momentRecordsChunk010Push (momentRecordsChunk009Push (momentRecordsChunk008Push (acc)))) := array_moment_records_chunk_010 fuel (momentRecordsChunk011Chars ++ (tail)) (momentRecordsChunk009Push (momentRecordsChunk008Push (acc)))
    _ = SourceJson.array (fuel + 169) (SourceJson.white tail) (momentRecordsBlock002Push acc) := array_moment_records_chunk_011 fuel (tail) (momentRecordsChunk010Push (momentRecordsChunk009Push (momentRecordsChunk008Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_002_before_raw_binding"
  err.flush

theorem moment_records_block_002_prefix :
    (momentRest01 4510).take 2092 = momentRecordsBlock002Chars := by rfl

theorem moment_records_block_002_split :
    momentRest01 4510 = momentRecordsBlock002Chars ++ momentRest01 6602 := by
  calc
    momentRest01 4510 =
        (momentRest01 4510).take 2092 ++ (momentRest01 4510).drop 2092 :=
      (List.take_append_drop 2092 (momentRest01 4510)).symm
    _ = momentRecordsBlock002Chars ++ (momentRest01 4510).drop 2092 :=
      congrArg (fun p => p ++ (momentRest01 4510).drop 2092) moment_records_block_002_prefix
    _ = momentRecordsBlock002Chars ++ momentRest01 6602 :=
      congrArg (fun rest => momentRecordsBlock002Chars ++ rest) (momentRest01_drop 4510 2092)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_002_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_002 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 173)
      (SourceJson.white (momentRest01 4510)) acc =
      SourceJson.array (fuel + 169) (SourceJson.white (momentRest01 6602)) (momentRecordsBlock002Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 173) (SourceJson.white s) acc)
      moment_records_block_002_split).trans (array_moment_records_block_002 fuel (momentRest01 6602) acc)

theorem moment_records_through_block_002 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 169) (SourceJson.white (momentRest01 6602)) momentRecordsAcc012 := by
  exact (moment_records_through_block_001 fuel).trans (array_moment_records_original_block_002 fuel momentRecordsAcc008)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_002_complete"
  err.flush

#print axioms array_moment_records_chunk_008
#print axioms array_moment_records_chunk_009
#print axioms array_moment_records_chunk_010
#print axioms array_moment_records_chunk_011
#print axioms array_moment_records_block_002
#print axioms moment_records_block_002_prefix
#print axioms moment_records_block_002_split
#print axioms array_moment_records_original_block_002
#print axioms moment_records_through_block_002

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
