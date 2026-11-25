import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock015

/-! Original moment records block 16. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk064Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '4', '7', '0', '3', '5', '1', '9', '8', '9', '3', '9', '8', '4', '9', '1', '6', '4', '5', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '7', '5', '5', '1', '7', '6', '0', '0', '7', '6', '1', '9', '1', '2', '6', '7', '1', '3', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '9', '2', '3', '0', '2', '9', '4', '2', '7', '7', '7', '8', '8', '8', '2', '6', '1', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '0', '2', '4', '0', '6', '5', '7', '9', '2', '8', '2', '8', '1', '7', '0', '0', '8', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '3', '8', '4', '0', '7', '6', '3', '2', '9', '2', '6', '3', '1', '6', '4', '1', '3', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '2', '7', '1', '6', '3', '0', '5', '2', '3', '5', '8', '1', '1', '8', '2', '8', '5', '3', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '3', '5', '7', '1', '1', '8', '4', '7', '5', '2', '5', '2', '2', '4', '6', '5', '6', '0', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '5', '0', '3', '8', '7', '2', '2', '3', '2', '0', '9', '3', '1', '3', '1', '8', '5', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '8', '3', '3', '4', '1', '8', '7', '1', '8', '4', '3', '0', '9', '4', '5', '3', '3', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '8', '3', '1', '8', '8', '0', '4', '5', '1', '5', '4', '2', '9', '6', '5', '6', '6', '1', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '4', '9', '5', '8', '0', '8', '8', '8', '8', '1', '4', '7', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '5', '7', '5', '0', '9', '6', '8', '9', '6', '5', '7', '1', '4', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk064Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['6', '4'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '4', '4', '7', '0', '3', '5', '1', '9', '8', '9', '3', '9', '8', '4', '9', '1', '6', '4', '5', '2', '6']), .str (String.ofList ['2', '5', '7', '5', '5', '1', '7', '6', '0', '0', '7', '6', '1', '9', '1', '2', '6', '7', '1', '3', '2', '8']), .str (String.ofList ['2', '8', '9', '2', '3', '0', '2', '9', '4', '2', '7', '7', '7', '8', '8', '8', '2', '6', '1', '0', '8']), .str (String.ofList ['3', '8', '0', '2', '4', '0', '6', '5', '7', '9', '2', '8', '2', '8', '1', '7', '0', '0', '8', '3', '1']), .str (String.ofList ['9', '3', '3', '8', '4', '0', '7', '6', '3', '2', '9', '2', '6', '3', '1', '6', '4', '1', '3', '1', '3']), .str (String.ofList ['2', '0', '2', '7', '1', '6', '3', '0', '5', '2', '3', '5', '8', '1', '1', '8', '2', '8', '5', '3', '4', '8']), .str (String.ofList ['1', '5', '3', '5', '7', '1', '1', '8', '4', '7', '5', '2', '5', '2', '2', '4', '6', '5', '6', '0', '0', '1']), .str (String.ofList ['1', '0', '7', '5', '0', '3', '8', '7', '2', '2', '3', '2', '0', '9', '3', '1', '3', '1', '8', '5', '8', '8']), .str (String.ofList ['7', '2', '8', '3', '3', '4', '1', '8', '7', '1', '8', '4', '3', '0', '9', '4', '5', '3', '3', '5', '9']), .str (String.ofList ['7', '2', '8', '3', '1', '8', '8', '0', '4', '5', '1', '5', '4', '2', '9', '6', '5', '6', '6', '1', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['7', '4', '9', '5', '8', '0', '8', '8', '8', '8', '1', '4', '7', '5', '7'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['7', '5', '7', '5', '0', '9', '6', '8', '9', '6', '5', '7', '1', '4', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_064_before_generic"
  err.flush

theorem array_moment_records_chunk_064 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 117)
      (SourceJson.white (momentRecordsChunk064Chars ++ tail)) acc =
      SourceJson.array (fuel + 116) (SourceJson.white tail) (momentRecordsChunk064Push acc) := by rfl

noncomputable def momentRecordsAcc065 : List SourceJson := momentRecordsChunk064Push momentRecordsAcc064

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_064_generic_complete"
  err.flush

noncomputable def momentRecordsChunk065Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '1', '0', '8', '0', '9', '2', '3', '8', '1', '8', '5', '5', '9', '7', '2', '0', '2', '3', '4', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '8', '2', '4', '6', '1', '2', '3', '4', '1', '2', '7', '5', '9', '3', '8', '1', '8', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '5', '9', '6', '6', '5', '9', '4', '1', '3', '1', '7', '0', '8', '3', '8', '8', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '6', '7', '2', '3', '0', '1', '6', '2', '9', '8', '0', '1', '3', '7', '4', '7', '2', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '8', '0', '6', '2', '5', '3', '7', '3', '7', '5', '7', '4', '1', '1', '0', '7', '2', '5', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '2', '0', '5', '0', '6', '7', '0', '0', '2', '6', '9', '5', '2', '8', '0', '3', '5', '6', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '6', '3', '1', '0', '7', '3', '2', '8', '4', '3', '8', '5', '0', '1', '8', '0', '7', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '1', '1', '6', '4', '8', '3', '4', '7', '8', '9', '5', '2', '3', '4', '6', '0', '7', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '4', '3', '9', '9', '1', '0', '8', '9', '2', '4', '0', '0', '1', '4', '9', '6', '3', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '4', '4', '0', '9', '1', '6', '4', '0', '6', '2', '1', '7', '2', '9', '5', '4', '6', '4', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '2', '5', '3', '3', '4', '5', '3', '1', '9', '7', '9', '4', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '3', '7', '2', '3', '3', '0', '4', '6', '2', '0', '3', '8', '1', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk065Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['6', '5'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '7', '1', '0', '8', '0', '9', '2', '3', '8', '1', '8', '5', '5', '9', '7', '2', '0', '2', '3', '4', '5']), .str (String.ofList ['2', '8', '5', '8', '2', '4', '6', '1', '2', '3', '4', '1', '2', '7', '5', '9', '3', '8', '1', '8', '2', '9']), .str (String.ofList ['2', '8', '7', '5', '9', '6', '6', '5', '9', '4', '1', '3', '1', '7', '0', '8', '3', '8', '8', '6', '4']), .str (String.ofList ['4', '3', '6', '7', '2', '3', '0', '1', '6', '2', '9', '8', '0', '1', '3', '7', '4', '7', '2', '7', '0']), .str (String.ofList ['1', '0', '9', '8', '0', '6', '2', '5', '3', '7', '3', '7', '5', '7', '4', '1', '1', '0', '7', '2', '5', '8']), .str (String.ofList ['2', '0', '2', '0', '5', '0', '6', '7', '0', '0', '2', '6', '9', '5', '2', '8', '0', '3', '5', '6', '5', '3']), .str (String.ofList ['1', '6', '7', '6', '3', '1', '0', '7', '3', '2', '8', '4', '3', '8', '5', '0', '1', '8', '0', '7', '7', '8']), .str (String.ofList ['8', '7', '1', '1', '6', '4', '8', '3', '4', '7', '8', '9', '5', '2', '3', '4', '6', '0', '7', '2', '4']), .str (String.ofList ['9', '9', '4', '3', '9', '9', '1', '0', '8', '9', '2', '4', '0', '0', '1', '4', '9', '6', '3', '2', '7']), .str (String.ofList ['9', '9', '4', '4', '0', '9', '1', '6', '4', '0', '6', '2', '1', '7', '2', '9', '5', '4', '6', '4', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '2', '5', '3', '3', '4', '5', '3', '1', '9', '7', '9', '4', '2', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '3', '7', '2', '3', '3', '0', '4', '6', '2', '0', '3', '8', '1', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_065_before_generic"
  err.flush

theorem array_moment_records_chunk_065 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 116)
      (SourceJson.white (momentRecordsChunk065Chars ++ tail)) acc =
      SourceJson.array (fuel + 115) (SourceJson.white tail) (momentRecordsChunk065Push acc) := by rfl

noncomputable def momentRecordsAcc066 : List SourceJson := momentRecordsChunk065Push momentRecordsAcc065

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_065_generic_complete"
  err.flush

noncomputable def momentRecordsChunk066Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '3', '7', '3', '0', '0', '9', '6', '1', '7', '5', '0', '1', '5', '2', '7', '0', '3', '2', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '2', '9', '6', '2', '3', '6', '0', '7', '8', '8', '2', '2', '4', '1', '4', '7', '0', '0', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '0', '5', '9', '4', '6', '7', '4', '9', '7', '1', '9', '3', '8', '2', '8', '9', '5', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '9', '4', '4', '1', '7', '2', '1', '7', '9', '1', '6', '5', '9', '4', '7', '7', '5', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '6', '8', '1', '8', '7', '8', '7', '6', '6', '4', '9', '5', '1', '3', '2', '0', '2', '6', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '4', '2', '4', '7', '6', '7', '2', '2', '7', '1', '6', '8', '2', '2', '4', '9', '7', '7', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '0', '6', '9', '7', '4', '1', '8', '9', '6', '6', '6', '1', '0', '7', '9', '4', '2', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '3', '3', '6', '4', '0', '0', '7', '6', '5', '8', '1', '9', '5', '7', '0', '2', '4', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '0', '6', '1', '1', '7', '7', '8', '2', '5', '9', '9', '0', '8', '8', '5', '4', '3', '7', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '0', '6', '3', '9', '1', '6', '8', '6', '7', '5', '8', '8', '0', '7', '3', '0', '9', '8', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '1', '7', '2', '8', '6', '2', '3', '7', '1', '3', '9', '6', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '1', '9', '9', '1', '2', '0', '0', '9', '3', '5', '1', '6', '4', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk066Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['6', '6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '9', '3', '7', '3', '0', '0', '9', '6', '1', '7', '5', '0', '1', '5', '2', '7', '0', '3', '2', '8', '3']), .str (String.ofList ['3', '1', '2', '9', '6', '2', '3', '6', '0', '7', '8', '8', '2', '2', '4', '1', '4', '7', '0', '0', '8', '8']), .str (String.ofList ['2', '8', '0', '5', '9', '4', '6', '7', '4', '9', '7', '1', '9', '3', '8', '2', '8', '9', '5', '2', '8']), .str (String.ofList ['4', '9', '9', '4', '4', '1', '7', '2', '1', '7', '9', '1', '6', '5', '9', '4', '7', '7', '5', '7', '3']), .str (String.ofList ['1', '2', '4', '6', '8', '1', '8', '7', '8', '7', '6', '6', '4', '9', '5', '1', '3', '2', '0', '2', '6', '8']), .str (String.ofList ['1', '9', '4', '2', '4', '7', '6', '7', '2', '2', '7', '1', '6', '8', '2', '2', '4', '9', '7', '7', '9', '0']), .str (String.ofList ['1', '1', '7', '0', '6', '9', '7', '4', '1', '8', '9', '6', '6', '6', '1', '0', '7', '9', '4', '2', '8', '0']), .str (String.ofList ['8', '9', '3', '3', '6', '4', '0', '0', '7', '6', '5', '8', '1', '9', '5', '7', '0', '2', '4', '0', '6']), .str (String.ofList ['1', '2', '1', '0', '6', '1', '1', '7', '7', '8', '2', '5', '9', '9', '0', '8', '8', '5', '4', '3', '7', '7']), .str (String.ofList ['1', '2', '1', '0', '6', '3', '9', '1', '6', '8', '6', '7', '5', '8', '8', '0', '7', '3', '0', '9', '8', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '1', '7', '2', '8', '6', '2', '3', '7', '1', '3', '9', '6', '1', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '1', '9', '9', '1', '2', '0', '0', '9', '3', '5', '1', '6', '4', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_066_before_generic"
  err.flush

theorem array_moment_records_chunk_066 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 115)
      (SourceJson.white (momentRecordsChunk066Chars ++ tail)) acc =
      SourceJson.array (fuel + 114) (SourceJson.white tail) (momentRecordsChunk066Push acc) := by rfl

noncomputable def momentRecordsAcc067 : List SourceJson := momentRecordsChunk066Push momentRecordsAcc066

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_066_generic_complete"
  err.flush

noncomputable def momentRecordsChunk067Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '7', '5', '1', '0', '6', '0', '4', '6', '6', '8', '1', '8', '5', '2', '3', '3', '8', '8', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '1', '8', '8', '1', '9', '0', '6', '0', '8', '8', '2', '8', '2', '8', '8', '4', '5', '7', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '5', '0', '6', '6', '8', '9', '0', '7', '0', '7', '4', '2', '6', '4', '1', '8', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '3', '0', '5', '7', '1', '1', '9', '7', '1', '0', '9', '9', '2', '8', '9', '5', '4', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '4', '2', '9', '6', '2', '3', '3', '6', '9', '7', '6', '4', '2', '5', '3', '8', '5', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '4', '2', '1', '0', '7', '1', '5', '0', '4', '2', '4', '5', '2', '1', '1', '0', '4', '1', '5', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '6', '7', '6', '3', '8', '7', '7', '2', '8', '2', '4', '9', '2', '5', '5', '9', '1', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '4', '7', '8', '2', '1', '2', '7', '9', '0', '4', '9', '7', '3', '1', '7', '4', '6', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '6', '8', '2', '3', '3', '4', '9', '5', '3', '3', '9', '1', '8', '8', '7', '9', '3', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '6', '8', '6', '5', '3', '6', '0', '3', '1', '2', '8', '7', '2', '7', '1', '2', '5', '6', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '7', '6', '5', '0', '5', '0', '5', '6', '8', '6', '6', '8', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '8', '2', '5', '9', '0', '3', '7', '9', '0', '5', '0', '6', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk067Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['6', '7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '0', '7', '5', '1', '0', '6', '0', '4', '6', '6', '8', '1', '8', '5', '2', '3', '3', '8', '8', '5', '6']), .str (String.ofList ['3', '3', '1', '8', '8', '1', '9', '0', '6', '0', '8', '8', '2', '8', '2', '8', '8', '4', '5', '7', '9', '3']), .str (String.ofList ['2', '7', '2', '5', '0', '6', '6', '8', '9', '0', '7', '0', '7', '4', '2', '6', '4', '1', '8', '8', '8']), .str (String.ofList ['5', '6', '3', '0', '5', '7', '1', '1', '9', '7', '1', '0', '9', '9', '2', '8', '9', '5', '4', '7', '6']), .str (String.ofList ['1', '3', '7', '4', '2', '9', '6', '2', '3', '3', '6', '9', '7', '6', '4', '2', '5', '3', '8', '5', '9', '1']), .str (String.ofList ['1', '8', '4', '2', '1', '0', '7', '1', '5', '0', '4', '2', '4', '5', '2', '1', '1', '0', '4', '1', '5', '4']), .str (String.ofList ['1', '3', '0', '6', '7', '6', '3', '8', '7', '7', '2', '8', '2', '4', '9', '2', '5', '5', '9', '1', '1', '6']), .str (String.ofList ['1', '0', '5', '4', '7', '8', '2', '1', '2', '7', '9', '0', '4', '9', '7', '3', '1', '7', '4', '6', '4', '2']), .str (String.ofList ['1', '2', '6', '6', '8', '2', '3', '3', '4', '9', '5', '3', '3', '9', '1', '8', '8', '7', '9', '3', '9', '6']), .str (String.ofList ['1', '2', '6', '6', '8', '6', '5', '3', '6', '0', '3', '1', '2', '8', '7', '2', '7', '1', '2', '5', '6', '6'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '7', '6', '5', '0', '5', '0', '5', '6', '8', '6', '6', '8', '5'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '8', '2', '5', '9', '0', '3', '7', '9', '0', '5', '0', '6', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_067_before_generic"
  err.flush

theorem array_moment_records_chunk_067 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 114)
      (SourceJson.white (momentRecordsChunk067Chars ++ tail)) acc =
      SourceJson.array (fuel + 113) (SourceJson.white tail) (momentRecordsChunk067Push acc) := by rfl

noncomputable def momentRecordsAcc068 : List SourceJson := momentRecordsChunk067Push momentRecordsAcc067

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_067_generic_complete"
  err.flush

noncomputable def momentRecordsBlock016Chars : List Char := momentRecordsChunk064Chars ++ momentRecordsChunk065Chars ++ momentRecordsChunk066Chars ++ momentRecordsChunk067Chars
noncomputable def momentRecordsBlock016Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk067Push (momentRecordsChunk066Push (momentRecordsChunk065Push (momentRecordsChunk064Push (acc))))

theorem array_moment_records_block_016 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 117)
      (SourceJson.white (momentRecordsBlock016Chars ++ tail)) acc =
      SourceJson.array (fuel + 113) (SourceJson.white tail) (momentRecordsBlock016Push acc) := by
  have hinput : momentRecordsBlock016Chars ++ tail = momentRecordsChunk064Chars ++ (momentRecordsChunk065Chars ++ (momentRecordsChunk066Chars ++ (momentRecordsChunk067Chars ++ (tail)))) := by
    simp only [momentRecordsBlock016Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 117) (SourceJson.white (momentRecordsBlock016Chars ++ tail)) acc =
        SourceJson.array (fuel + 117) (SourceJson.white (momentRecordsChunk064Chars ++ (momentRecordsChunk065Chars ++ (momentRecordsChunk066Chars ++ (momentRecordsChunk067Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 117) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 116) (SourceJson.white (momentRecordsChunk065Chars ++ (momentRecordsChunk066Chars ++ (momentRecordsChunk067Chars ++ (tail))))) (momentRecordsChunk064Push (acc)) := array_moment_records_chunk_064 fuel (momentRecordsChunk065Chars ++ (momentRecordsChunk066Chars ++ (momentRecordsChunk067Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 115) (SourceJson.white (momentRecordsChunk066Chars ++ (momentRecordsChunk067Chars ++ (tail)))) (momentRecordsChunk065Push (momentRecordsChunk064Push (acc))) := array_moment_records_chunk_065 fuel (momentRecordsChunk066Chars ++ (momentRecordsChunk067Chars ++ (tail))) (momentRecordsChunk064Push (acc))
    _ = SourceJson.array (fuel + 114) (SourceJson.white (momentRecordsChunk067Chars ++ (tail))) (momentRecordsChunk066Push (momentRecordsChunk065Push (momentRecordsChunk064Push (acc)))) := array_moment_records_chunk_066 fuel (momentRecordsChunk067Chars ++ (tail)) (momentRecordsChunk065Push (momentRecordsChunk064Push (acc)))
    _ = SourceJson.array (fuel + 113) (SourceJson.white tail) (momentRecordsBlock016Push acc) := array_moment_records_chunk_067 fuel (tail) (momentRecordsChunk066Push (momentRecordsChunk065Push (momentRecordsChunk064Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_016_before_raw_binding"
  err.flush

theorem moment_records_block_016_prefix :
    (momentRest01 33690).take 2073 = momentRecordsBlock016Chars := by rfl

theorem moment_records_block_016_split :
    momentRest01 33690 = momentRecordsBlock016Chars ++ momentRest01 35763 := by
  calc
    momentRest01 33690 =
        (momentRest01 33690).take 2073 ++ (momentRest01 33690).drop 2073 :=
      (List.take_append_drop 2073 (momentRest01 33690)).symm
    _ = momentRecordsBlock016Chars ++ (momentRest01 33690).drop 2073 :=
      congrArg (fun p => p ++ (momentRest01 33690).drop 2073) moment_records_block_016_prefix
    _ = momentRecordsBlock016Chars ++ momentRest01 35763 :=
      congrArg (fun rest => momentRecordsBlock016Chars ++ rest) (momentRest01_drop 33690 2073)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_016_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_016 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 117)
      (SourceJson.white (momentRest01 33690)) acc =
      SourceJson.array (fuel + 113) (SourceJson.white (momentRest01 35763)) (momentRecordsBlock016Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 117) (SourceJson.white s) acc)
      moment_records_block_016_split).trans (array_moment_records_block_016 fuel (momentRest01 35763) acc)

theorem moment_records_through_block_016 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 113) (SourceJson.white (momentRest01 35763)) momentRecordsAcc068 := by
  exact (moment_records_through_block_015 fuel).trans (array_moment_records_original_block_016 fuel momentRecordsAcc064)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_016_complete"
  err.flush

#print axioms array_moment_records_chunk_064
#print axioms array_moment_records_chunk_065
#print axioms array_moment_records_chunk_066
#print axioms array_moment_records_chunk_067
#print axioms array_moment_records_block_016
#print axioms moment_records_block_016_prefix
#print axioms moment_records_block_016_split
#print axioms array_moment_records_original_block_016
#print axioms moment_records_through_block_016

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
