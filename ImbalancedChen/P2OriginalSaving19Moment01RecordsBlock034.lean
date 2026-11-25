import ImbalancedChen.P2OriginalSaving19Moment01RecordsBlock033

/-! Original moment records block 34. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk136Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '0', '6', '2', '7', '9', '8', '3', '8', '1', '5', '7', '3', '8', '9', '0', '1', '4', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '1', '2', '2', '5', '1', '6', '3', '6', '6', '3', '3', '5', '9', '9', '7', '6', '4', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '2', '5', '7', '7', '7', '5', '6', '6', '9', '2', '6', '4', '8', '4', '0', '9', '2', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '7', '5', '6', '2', '7', '3', '7', '1', '2', '4', '2', '0', '8', '8', '4', '2', '2', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '2', '2', '5', '0', '6', '2', '0', '6', '6', '7', '5', '1', '3', '4', '4', '9', '8', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '5', '3', '2', '1', '6', '1', '7', '1', '6', '0', '9', '9', '1', '6', '8', '8', '0', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '2', '8', '9', '7', '2', '3', '6', '7', '7', '5', '1', '3', '5', '4', '9', '6', '0', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '3', '2', '2', '1', '8', '8', '3', '4', '2', '7', '8', '9', '0', '9', '3', '6', '3', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '5', '0', '7', '9', '9', '4', '8', '3', '3', '9', '7', '4', '6', '1', '4', '3', '1', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '5', '1', '3', '8', '2', '6', '6', '6', '2', '1', '7', '2', '4', '0', '6', '8', '5', '7', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '4', '1', '2', '6', '7', '5', '2', '0', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '4', '5', '2', '4', '0', '4', '8', '9', '9', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk136Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '3', '6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '0', '4', '0', '6', '2', '7', '9', '8', '3', '8', '1', '5', '7', '3', '8', '9', '0', '1', '4', '9', '3']), .str (String.ofList ['1', '0', '2', '1', '2', '2', '5', '1', '6', '3', '6', '6', '3', '3', '5', '9', '9', '7', '6', '4', '0', '1']), .str (String.ofList ['1', '6', '2', '5', '7', '7', '7', '5', '6', '6', '9', '2', '6', '4', '8', '4', '0', '9', '2', '0', '7']), .str (String.ofList ['9', '2', '7', '5', '6', '2', '7', '3', '7', '1', '2', '4', '2', '0', '8', '8', '4', '2', '2', '0', '1']), .str (String.ofList ['5', '2', '2', '2', '5', '0', '6', '2', '0', '6', '6', '7', '5', '1', '3', '4', '4', '9', '8', '7', '5']), .str (String.ofList ['1', '7', '5', '5', '3', '2', '1', '6', '1', '7', '1', '6', '0', '9', '9', '1', '6', '8', '8', '0', '3', '4']), .str (String.ofList ['1', '4', '8', '2', '8', '9', '7', '2', '3', '6', '7', '7', '5', '1', '3', '5', '4', '9', '6', '0', '0', '6']), .str (String.ofList ['1', '3', '7', '3', '2', '2', '1', '8', '8', '3', '4', '2', '7', '8', '9', '0', '9', '3', '6', '3', '4', '3']), .str (String.ofList ['1', '2', '7', '5', '0', '7', '9', '9', '4', '8', '3', '3', '9', '7', '4', '6', '1', '4', '3', '1', '2', '7']), .str (String.ofList ['1', '2', '7', '5', '1', '3', '8', '2', '6', '6', '6', '2', '1', '7', '2', '4', '0', '6', '8', '5', '7', '7'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '4', '1', '2', '6', '7', '5', '2', '0', '6', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '4', '5', '2', '4', '0', '4', '8', '9', '9', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_136_before_generic"
  err.flush

theorem array_moment_records_chunk_136 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 45)
      (SourceJson.white (momentRecordsChunk136Chars ++ tail)) acc =
      SourceJson.array (fuel + 44) (SourceJson.white tail) (momentRecordsChunk136Push acc) := by rfl

noncomputable def momentRecordsAcc137 : List SourceJson := momentRecordsChunk136Push momentRecordsAcc136

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_136_generic_complete"
  err.flush

noncomputable def momentRecordsChunk137Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '2', '3', '4', '0', '1', '2', '7', '3', '9', '6', '2', '8', '5', '9', '9', '2', '6', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '0', '1', '7', '2', '9', '6', '5', '5', '6', '7', '4', '7', '5', '8', '8', '5', '0', '4', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '4', '1', '1', '9', '0', '6', '4', '1', '2', '3', '5', '7', '9', '6', '3', '2', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '3', '4', '0', '7', '1', '0', '6', '1', '9', '8', '1', '8', '3', '6', '4', '4', '7', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '6', '8', '3', '2', '9', '7', '7', '8', '6', '2', '2', '0', '9', '2', '3', '7', '3', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '1', '2', '3', '1', '7', '0', '6', '5', '2', '3', '1', '8', '2', '0', '7', '7', '2', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '7', '1', '7', '3', '8', '4', '7', '9', '2', '9', '0', '0', '4', '3', '9', '0', '7', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '0', '9', '1', '0', '6', '2', '5', '2', '3', '6', '1', '2', '6', '5', '3', '6', '4', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '5', '2', '8', '8', '1', '3', '5', '7', '0', '3', '0', '6', '9', '4', '0', '9', '1', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '6', '6', '4', '7', '4', '5', '1', '1', '7', '1', '9', '4', '8', '5', '5', '2', '8', '6', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '4', '1', '7', '5', '1', '8', '1', '0', '8', '7', '3', '5', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '4', '7', '2', '6', '6', '1', '9', '0', '8', '4', '1', '4', '0', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk137Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '3', '7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['6', '7', '2', '3', '4', '0', '1', '2', '7', '3', '9', '6', '2', '8', '5', '9', '9', '2', '6', '9', '8']), .str (String.ofList ['6', '6', '0', '1', '7', '2', '9', '6', '5', '5', '6', '7', '4', '7', '5', '8', '8', '5', '0', '4', '0']), .str (String.ofList ['1', '0', '8', '4', '1', '1', '9', '0', '6', '4', '1', '2', '3', '5', '7', '9', '6', '3', '2', '1', '6']), .str (String.ofList ['5', '4', '3', '4', '0', '7', '1', '0', '6', '1', '9', '8', '1', '8', '3', '6', '4', '4', '7', '1', '9']), .str (String.ofList ['4', '4', '6', '8', '3', '2', '9', '7', '7', '8', '6', '2', '2', '0', '9', '2', '3', '7', '3', '3', '4']), .str (String.ofList ['1', '0', '2', '1', '2', '3', '1', '7', '0', '6', '5', '2', '3', '1', '8', '2', '0', '7', '7', '2', '6', '9']), .str (String.ofList ['7', '8', '7', '1', '7', '3', '8', '4', '7', '9', '2', '9', '0', '0', '4', '3', '9', '0', '7', '9', '2']), .str (String.ofList ['7', '1', '0', '9', '1', '0', '6', '2', '5', '2', '3', '6', '1', '2', '6', '5', '3', '6', '4', '1', '5']), .str (String.ofList ['6', '8', '5', '2', '8', '8', '1', '3', '5', '7', '0', '3', '0', '6', '9', '4', '0', '9', '1', '4', '3']), .str (String.ofList ['7', '4', '6', '6', '4', '7', '4', '5', '1', '1', '7', '1', '9', '4', '8', '5', '5', '2', '8', '6', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '4', '1', '7', '5', '1', '8', '1', '0', '8', '7', '3', '5', '9', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '0', '4', '7', '2', '6', '6', '1', '9', '0', '8', '4', '1', '4', '0', '2']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_137_before_generic"
  err.flush

theorem array_moment_records_chunk_137 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 44)
      (SourceJson.white (momentRecordsChunk137Chars ++ tail)) acc =
      SourceJson.array (fuel + 43) (SourceJson.white tail) (momentRecordsChunk137Push acc) := by rfl

noncomputable def momentRecordsAcc138 : List SourceJson := momentRecordsChunk137Push momentRecordsAcc137

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_137_generic_complete"
  err.flush

noncomputable def momentRecordsChunk138Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '8', '2', '1', '2', '1', '2', '1', '9', '3', '2', '8', '8', '6', '8', '8', '2', '1', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '8', '1', '2', '6', '4', '5', '8', '6', '8', '8', '8', '6', '2', '4', '5', '5', '5', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '5', '7', '8', '7', '9', '6', '8', '7', '3', '8', '7', '5', '1', '9', '8', '9', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '7', '9', '7', '8', '4', '5', '0', '8', '7', '7', '1', '9', '6', '6', '5', '4', '1', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '4', '9', '1', '9', '3', '2', '3', '0', '9', '3', '1', '3', '2', '4', '9', '4', '7', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '3', '6', '6', '7', '3', '1', '5', '2', '8', '5', '8', '3', '8', '1', '7', '8', '9', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '0', '6', '7', '4', '2', '9', '1', '1', '1', '8', '3', '9', '5', '1', '3', '7', '3', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '3', '6', '6', '0', '6', '1', '2', '7', '9', '8', '3', '1', '5', '6', '3', '0', '9', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '1', '9', '2', '9', '6', '7', '5', '3', '3', '7', '1', '7', '2', '6', '5', '0', '1', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '1', '9', '7', '8', '0', '4', '5', '9', '8', '9', '5', '2', '6', '3', '7', '3', '3', '0', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '8', '3', '8', '1', '5', '5', '5', '9', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '1', '0', '5', '5', '0', '8', '4', '7', '3', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk138Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '3', '8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['6', '7', '8', '2', '1', '2', '1', '2', '1', '9', '3', '2', '8', '8', '6', '8', '8', '2', '1', '7', '1']), .str (String.ofList ['6', '6', '8', '1', '2', '6', '4', '5', '8', '6', '8', '8', '8', '6', '2', '4', '5', '5', '5', '1', '7']), .str (String.ofList ['1', '0', '3', '5', '7', '8', '7', '9', '6', '8', '7', '3', '8', '7', '5', '1', '9', '8', '9', '1', '9']), .str (String.ofList ['5', '8', '7', '9', '7', '8', '4', '5', '0', '8', '7', '7', '1', '9', '6', '6', '5', '4', '1', '8', '1']), .str (String.ofList ['4', '6', '4', '9', '1', '9', '3', '2', '3', '0', '9', '3', '1', '3', '2', '4', '9', '4', '7', '1', '2']), .str (String.ofList ['1', '0', '0', '3', '6', '6', '7', '3', '1', '5', '2', '8', '5', '8', '3', '8', '1', '7', '8', '9', '7', '3']), .str (String.ofList ['8', '0', '0', '6', '7', '4', '2', '9', '1', '1', '1', '8', '3', '9', '5', '1', '3', '7', '3', '1', '4']), .str (String.ofList ['7', '3', '3', '6', '6', '0', '6', '1', '2', '7', '9', '8', '3', '1', '5', '6', '3', '0', '9', '7', '3']), .str (String.ofList ['6', '8', '1', '9', '2', '9', '6', '7', '5', '3', '3', '7', '1', '7', '2', '6', '5', '0', '1', '7', '1']), .str (String.ofList ['6', '8', '1', '9', '7', '8', '0', '4', '5', '9', '8', '9', '5', '2', '6', '3', '7', '3', '3', '0', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '0', '8', '3', '8', '1', '5', '5', '5', '9', '7'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '1', '0', '5', '5', '0', '8', '4', '7', '3', '0']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_138_before_generic"
  err.flush

theorem array_moment_records_chunk_138 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 43)
      (SourceJson.white (momentRecordsChunk138Chars ++ tail)) acc =
      SourceJson.array (fuel + 42) (SourceJson.white tail) (momentRecordsChunk138Push acc) := by rfl

noncomputable def momentRecordsAcc139 : List SourceJson := momentRecordsChunk138Push momentRecordsAcc138

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_138_generic_complete"
  err.flush

noncomputable def momentRecordsChunk139Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '3', '2', '9', '9', '4', '5', '6', '3', '6', '7', '5', '1', '3', '4', '1', '8', '8', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '9', '3', '0', '9', '4', '4', '8', '4', '3', '3', '4', '9', '3', '0', '3', '3', '4', '9', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '0', '0', '6', '2', '8', '4', '6', '8', '3', '2', '3', '5', '1', '2', '6', '2', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '6', '3', '6', '9', '2', '9', '2', '8', '9', '4', '2', '6', '6', '0', '4', '2', '3', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '2', '3', '0', '7', '5', '2', '8', '9', '5', '3', '2', '2', '4', '3', '1', '8', '9', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '7', '7', '3', '0', '4', '5', '5', '9', '1', '3', '8', '5', '8', '0', '9', '2', '8', '4', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '0', '0', '6', '2', '9', '5', '8', '1', '6', '5', '9', '4', '1', '4', '0', '8', '3', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '2', '5', '9', '1', '0', '0', '6', '7', '8', '9', '9', '4', '1', '2', '1', '2', '3', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '3', '9', '0', '9', '9', '2', '5', '0', '1', '2', '4', '4', '6', '2', '8', '9', '0', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '4', '6', '1', '6', '0', '3', '4', '3', '8', '7', '0', '9', '6', '9', '8', '1', '8', '5', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '7', '9', '6', '1', '4', '5', '2', '6', '6', '2', '4', '2', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '8', '4', '7', '6', '8', '0', '4', '6', '9', '5', '3', '9', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk139Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '3', '9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['6', '8', '3', '2', '9', '9', '4', '5', '6', '3', '6', '7', '5', '1', '3', '4', '1', '8', '8', '0', '2']), .str (String.ofList ['6', '6', '9', '3', '0', '9', '4', '4', '8', '4', '3', '3', '4', '9', '3', '0', '3', '3', '4', '9', '4']), .str (String.ofList ['1', '0', '3', '0', '0', '6', '2', '8', '4', '6', '8', '3', '2', '3', '5', '1', '2', '6', '2', '0', '9']), .str (String.ofList ['5', '6', '6', '3', '6', '9', '2', '9', '2', '8', '9', '4', '2', '6', '6', '0', '4', '2', '3', '9', '3']), .str (String.ofList ['4', '6', '2', '3', '0', '7', '5', '2', '8', '9', '5', '3', '2', '2', '4', '3', '1', '8', '9', '8', '7']), .str (String.ofList ['9', '6', '7', '7', '3', '0', '4', '5', '5', '9', '1', '3', '8', '5', '8', '0', '9', '2', '8', '4', '4']), .str (String.ofList ['8', '0', '0', '0', '6', '2', '9', '5', '8', '1', '6', '5', '9', '4', '1', '4', '0', '8', '3', '2', '0']), .str (String.ofList ['7', '3', '2', '5', '9', '1', '0', '0', '6', '7', '8', '9', '9', '4', '1', '2', '1', '2', '3', '5', '1']), .str (String.ofList ['6', '8', '3', '9', '0', '9', '9', '2', '5', '0', '1', '2', '4', '4', '6', '2', '8', '9', '0', '0', '7']), .str (String.ofList ['6', '7', '4', '6', '1', '6', '0', '3', '4', '3', '8', '7', '0', '9', '6', '9', '8', '1', '8', '5', '2'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '7', '9', '6', '1', '4', '5', '2', '6', '6', '2', '4', '2', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '8', '4', '7', '6', '8', '0', '4', '6', '9', '5', '3', '9', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_139_before_generic"
  err.flush

theorem array_moment_records_chunk_139 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 42)
      (SourceJson.white (momentRecordsChunk139Chars ++ tail)) acc =
      SourceJson.array (fuel + 41) (SourceJson.white tail) (momentRecordsChunk139Push acc) := by rfl

noncomputable def momentRecordsAcc140 : List SourceJson := momentRecordsChunk139Push momentRecordsAcc139

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_chunk_139_generic_complete"
  err.flush

noncomputable def momentRecordsBlock034Chars : List Char := momentRecordsChunk136Chars ++ momentRecordsChunk137Chars ++ momentRecordsChunk138Chars ++ momentRecordsChunk139Chars
noncomputable def momentRecordsBlock034Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk139Push (momentRecordsChunk138Push (momentRecordsChunk137Push (momentRecordsChunk136Push (acc))))

theorem array_moment_records_block_034 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 45)
      (SourceJson.white (momentRecordsBlock034Chars ++ tail)) acc =
      SourceJson.array (fuel + 41) (SourceJson.white tail) (momentRecordsBlock034Push acc) := by
  have hinput : momentRecordsBlock034Chars ++ tail = momentRecordsChunk136Chars ++ (momentRecordsChunk137Chars ++ (momentRecordsChunk138Chars ++ (momentRecordsChunk139Chars ++ (tail)))) := by
    simp only [momentRecordsBlock034Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 45) (SourceJson.white (momentRecordsBlock034Chars ++ tail)) acc =
        SourceJson.array (fuel + 45) (SourceJson.white (momentRecordsChunk136Chars ++ (momentRecordsChunk137Chars ++ (momentRecordsChunk138Chars ++ (momentRecordsChunk139Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 45) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 44) (SourceJson.white (momentRecordsChunk137Chars ++ (momentRecordsChunk138Chars ++ (momentRecordsChunk139Chars ++ (tail))))) (momentRecordsChunk136Push (acc)) := array_moment_records_chunk_136 fuel (momentRecordsChunk137Chars ++ (momentRecordsChunk138Chars ++ (momentRecordsChunk139Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 43) (SourceJson.white (momentRecordsChunk138Chars ++ (momentRecordsChunk139Chars ++ (tail)))) (momentRecordsChunk137Push (momentRecordsChunk136Push (acc))) := array_moment_records_chunk_137 fuel (momentRecordsChunk138Chars ++ (momentRecordsChunk139Chars ++ (tail))) (momentRecordsChunk136Push (acc))
    _ = SourceJson.array (fuel + 42) (SourceJson.white (momentRecordsChunk139Chars ++ (tail))) (momentRecordsChunk138Push (momentRecordsChunk137Push (momentRecordsChunk136Push (acc)))) := array_moment_records_chunk_138 fuel (momentRecordsChunk139Chars ++ (tail)) (momentRecordsChunk137Push (momentRecordsChunk136Push (acc)))
    _ = SourceJson.array (fuel + 41) (SourceJson.white tail) (momentRecordsBlock034Push acc) := array_moment_records_chunk_139 fuel (tail) (momentRecordsChunk138Push (momentRecordsChunk137Push (momentRecordsChunk136Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_034_before_raw_binding"
  err.flush

theorem moment_records_block_034_prefix :
    (momentRest01 71010).take 2045 = momentRecordsBlock034Chars := by rfl

theorem moment_records_block_034_split :
    momentRest01 71010 = momentRecordsBlock034Chars ++ momentRest01 73055 := by
  calc
    momentRest01 71010 =
        (momentRest01 71010).take 2045 ++ (momentRest01 71010).drop 2045 :=
      (List.take_append_drop 2045 (momentRest01 71010)).symm
    _ = momentRecordsBlock034Chars ++ (momentRest01 71010).drop 2045 :=
      congrArg (fun p => p ++ (momentRest01 71010).drop 2045) moment_records_block_034_prefix
    _ = momentRecordsBlock034Chars ++ momentRest01 73055 :=
      congrArg (fun rest => momentRecordsBlock034Chars ++ rest) (momentRest01_drop 71010 2045)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_034_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_034 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 45)
      (SourceJson.white (momentRest01 71010)) acc =
      SourceJson.array (fuel + 41) (SourceJson.white (momentRest01 73055)) (momentRecordsBlock034Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 45) (SourceJson.white s) acc)
      moment_records_block_034_split).trans (array_moment_records_block_034 fuel (momentRest01 73055) acc)

theorem moment_records_through_block_034 (fuel : Nat) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (momentRest01 364)) [] =
      SourceJson.array (fuel + 41) (SourceJson.white (momentRest01 73055)) momentRecordsAcc140 := by
  exact (moment_records_through_block_033 fuel).trans (array_moment_records_original_block_034 fuel momentRecordsAcc136)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 records_block_034_complete"
  err.flush

#print axioms array_moment_records_chunk_136
#print axioms array_moment_records_chunk_137
#print axioms array_moment_records_chunk_138
#print axioms array_moment_records_chunk_139
#print axioms array_moment_records_block_034
#print axioms moment_records_block_034_prefix
#print axioms moment_records_block_034_split
#print axioms array_moment_records_original_block_034
#print axioms moment_records_through_block_034

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
