import ImbalancedChen.P2OriginalSaving19Moment00RecordsBlock010

/-! Original moment records block 11. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk044Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '7', '6', '8', '7', '0', '3', '2', '6', '7', '2', '6', '0', '7', '3', '7', '1', '2', '0', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '6', '3', '3', '1', '9', '1', '0', '5', '5', '7', '2', '1', '1', '0', '2', '8', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '3', '2', '4', '2', '3', '4', '2', '8', '3', '4', '2', '9', '6', '1', '6', '0', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '9', '3', '9', '0', '8', '7', '4', '3', '4', '8', '8', '9', '6', '6', '2', '4', '0', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '7', '1', '5', '0', '0', '0', '6', '6', '7', '7', '4', '1', '2', '6', '2', '4', '9', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '2', '6', '6', '2', '5', '4', '6', '3', '7', '3', '1', '3', '4', '7', '5', '2', '2', '6', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '9', '6', '8', '9', '2', '6', '2', '2', '9', '5', '5', '0', '0', '7', '0', '2', '0', '9', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '8', '2', '4', '4', '3', '8', '0', '1', '5', '1', '3', '6', '1', '3', '9', '2', '1', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '3', '6', '7', '6', '3', '6', '2', '2', '6', '3', '4', '0', '2', '3', '3', '8', '8', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '5', '8', '5', '9', '0', '7', '0', '7', '1', '1', '3', '8', '4', '3', '7', '4', '4', '4', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '0', '5', '8', '4', '9', '3', '4', '6', '9', '5', '2', '7', '8', '5', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '0', '7', '7', '7', '7', '9', '9', '7', '2', '6', '5', '7', '3', '1', '0', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk044Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['4', '4'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '5', '7', '6', '8', '7', '0', '3', '2', '6', '7', '2', '6', '0', '7', '3', '7', '1', '2', '0', '3']), .str (String.ofList ['1', '5', '6', '6', '3', '3', '1', '9', '1', '0', '5', '5', '7', '2', '1', '1', '0', '2', '8', '2', '7']), .str (String.ofList ['1', '4', '5', '3', '2', '4', '2', '3', '4', '2', '8', '3', '4', '2', '9', '6', '1', '6', '0', '1', '0']), .str (String.ofList ['3', '9', '9', '3', '9', '0', '8', '7', '4', '3', '4', '8', '8', '9', '6', '6', '2', '4', '0', '9', '0']), .str (String.ofList ['1', '9', '0', '7', '1', '5', '0', '0', '0', '6', '6', '7', '7', '4', '1', '2', '6', '2', '4', '9', '9']), .str (String.ofList ['3', '5', '2', '6', '6', '2', '5', '4', '6', '3', '7', '3', '1', '3', '4', '7', '5', '2', '2', '6', '6']), .str (String.ofList ['4', '8', '9', '6', '8', '9', '2', '6', '2', '2', '9', '5', '5', '0', '0', '7', '0', '2', '0', '9', '4']), .str (String.ofList ['3', '3', '8', '2', '4', '4', '3', '8', '0', '1', '5', '1', '3', '6', '1', '3', '9', '2', '1', '9', '6']), .str (String.ofList ['3', '4', '3', '6', '7', '6', '3', '6', '2', '2', '6', '3', '4', '0', '2', '3', '3', '8', '8', '7', '3']), .str (String.ofList ['3', '1', '5', '8', '5', '9', '0', '7', '0', '7', '1', '1', '3', '8', '4', '3', '7', '4', '4', '4', '4'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '0', '5', '8', '4', '9', '3', '4', '6', '9', '5', '2', '7', '8', '5', '1', '9'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '0', '7', '7', '7', '7', '9', '9', '7', '2', '6', '5', '7', '3', '1', '0', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_044_before_generic"
  err.flush

theorem array_moment_records_chunk_044 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 49)
      (SourceJson.white (momentRecordsChunk044Chars ++ tail)) acc =
      SourceJson.array (fuel + 48) (SourceJson.white tail) (momentRecordsChunk044Push acc) := by rfl

noncomputable def momentRecordsAcc045 : List SourceJson := momentRecordsChunk044Push momentRecordsAcc044

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_044_generic_complete"
  err.flush

noncomputable def momentRecordsChunk045Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '7', '0', '5', '0', '3', '2', '0', '6', '3', '6', '7', '4', '9', '3', '5', '2', '0', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '3', '5', '6', '8', '1', '0', '1', '7', '6', '2', '0', '1', '6', '8', '5', '6', '1', '5', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '4', '6', '9', '0', '5', '9', '6', '3', '9', '3', '4', '8', '2', '6', '9', '9', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '7', '4', '2', '1', '6', '0', '2', '7', '7', '3', '3', '7', '1', '0', '1', '2', '6', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '1', '3', '3', '0', '7', '2', '4', '0', '6', '5', '2', '0', '0', '6', '4', '4', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '3', '5', '9', '6', '1', '1', '0', '9', '0', '7', '9', '5', '8', '9', '2', '8', '1', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '0', '0', '3', '7', '3', '3', '9', '3', '6', '8', '0', '3', '0', '6', '7', '7', '3', '6', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '3', '2', '6', '4', '7', '1', '1', '7', '8', '0', '8', '0', '9', '7', '3', '1', '1', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '2', '4', '9', '0', '8', '2', '6', '0', '9', '0', '9', '6', '1', '8', '6', '9', '7', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '2', '7', '8', '7', '4', '2', '6', '5', '0', '6', '3', '2', '6', '8', '7', '5', '8', '9', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '3', '7', '3', '0', '3', '3', '0', '0', '8', '8', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '3', '9', '5', '6', '0', '6', '2', '9', '0', '3', '1', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk045Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['4', '5'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '7', '7', '0', '5', '0', '3', '2', '0', '6', '3', '6', '7', '4', '9', '3', '5', '2', '0', '8', '2']), .str (String.ofList ['1', '9', '3', '5', '6', '8', '1', '0', '1', '7', '6', '2', '0', '1', '6', '8', '5', '6', '1', '5', '4']), .str (String.ofList ['1', '4', '4', '4', '6', '9', '0', '5', '9', '6', '3', '9', '3', '4', '8', '2', '6', '9', '9', '9', '2']), .str (String.ofList ['4', '5', '7', '4', '2', '1', '6', '0', '2', '7', '7', '3', '3', '7', '1', '0', '1', '2', '6', '5', '2']), .str (String.ofList ['1', '9', '0', '1', '3', '3', '0', '7', '2', '4', '0', '6', '5', '2', '0', '0', '6', '4', '4', '7', '0']), .str (String.ofList ['3', '6', '3', '5', '9', '6', '1', '1', '0', '9', '0', '7', '9', '5', '8', '9', '2', '8', '1', '8', '6']), .str (String.ofList ['5', '0', '0', '0', '3', '7', '3', '3', '9', '3', '6', '8', '0', '3', '0', '6', '7', '7', '3', '6', '8']), .str (String.ofList ['3', '7', '3', '2', '6', '4', '7', '1', '1', '7', '8', '0', '8', '0', '9', '7', '3', '1', '1', '7', '8']), .str (String.ofList ['4', '2', '2', '4', '9', '0', '8', '2', '6', '0', '9', '0', '9', '6', '1', '8', '6', '9', '7', '3', '4']), .str (String.ofList ['4', '3', '2', '7', '8', '7', '4', '2', '6', '5', '0', '6', '3', '2', '6', '8', '7', '5', '8', '9', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '3', '7', '3', '0', '3', '3', '0', '0', '8', '8', '4', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '3', '9', '5', '6', '0', '6', '2', '9', '0', '3', '1', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_045_before_generic"
  err.flush

theorem array_moment_records_chunk_045 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 48)
      (SourceJson.white (momentRecordsChunk045Chars ++ tail)) acc =
      SourceJson.array (fuel + 47) (SourceJson.white tail) (momentRecordsChunk045Push acc) := by rfl

noncomputable def momentRecordsAcc046 : List SourceJson := momentRecordsChunk045Push momentRecordsAcc045

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_045_generic_complete"
  err.flush

noncomputable def momentRecordsChunk046Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '3', '3', '7', '5', '1', '7', '9', '5', '3', '2', '4', '8', '1', '3', '1', '5', '8', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '2', '1', '3', '4', '6', '2', '7', '8', '8', '4', '7', '1', '7', '7', '3', '3', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '4', '6', '9', '0', '5', '9', '6', '3', '9', '3', '4', '8', '2', '6', '9', '9', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '8', '3', '6', '6', '1', '2', '8', '6', '7', '4', '7', '1', '2', '2', '4', '9', '9', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '1', '3', '3', '0', '7', '2', '4', '0', '6', '5', '2', '0', '0', '6', '4', '4', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '3', '5', '9', '6', '1', '1', '0', '9', '0', '7', '9', '5', '8', '9', '2', '8', '1', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '0', '0', '3', '7', '3', '3', '9', '3', '6', '8', '0', '3', '0', '6', '7', '7', '3', '6', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '3', '2', '6', '4', '7', '1', '1', '7', '8', '0', '8', '0', '9', '7', '3', '1', '1', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '3', '6', '9', '1', '0', '7', '6', '7', '9', '4', '2', '2', '0', '7', '6', '6', '7', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '9', '8', '4', '4', '1', '7', '5', '8', '2', '4', '2', '6', '7', '1', '8', '8', '0', '9', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '7', '4', '1', '7', '2', '5', '3', '4', '5', '6', '0', '1', '1', '0', '7', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '7', '6', '3', '1', '0', '7', '8', '8', '7', '1', '1', '5', '4', '6', '3', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk046Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['4', '6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '5', '3', '3', '7', '5', '1', '7', '9', '5', '3', '2', '4', '8', '1', '3', '1', '5', '8', '3', '9']), .str (String.ofList ['1', '6', '4', '2', '1', '3', '4', '6', '2', '7', '8', '8', '4', '7', '1', '7', '7', '3', '3', '8', '0']), .str (String.ofList ['1', '4', '4', '4', '6', '9', '0', '5', '9', '6', '3', '9', '3', '4', '8', '2', '6', '9', '9', '9', '2']), .str (String.ofList ['3', '9', '0', '8', '3', '6', '6', '1', '2', '8', '6', '7', '4', '7', '1', '2', '2', '4', '9', '9', '9']), .str (String.ofList ['1', '9', '0', '1', '3', '3', '0', '7', '2', '4', '0', '6', '5', '2', '0', '0', '6', '4', '4', '7', '0']), .str (String.ofList ['3', '6', '3', '5', '9', '6', '1', '1', '0', '9', '0', '7', '9', '5', '8', '9', '2', '8', '1', '8', '6']), .str (String.ofList ['5', '0', '0', '0', '3', '7', '3', '3', '9', '3', '6', '8', '0', '3', '0', '6', '7', '7', '3', '6', '8']), .str (String.ofList ['3', '7', '3', '2', '6', '4', '7', '1', '1', '7', '8', '0', '8', '0', '9', '7', '3', '1', '1', '7', '8']), .str (String.ofList ['3', '6', '3', '6', '9', '1', '0', '7', '6', '7', '9', '4', '2', '2', '0', '7', '6', '6', '7', '7', '5']), .str (String.ofList ['3', '0', '9', '8', '4', '4', '1', '7', '5', '8', '2', '4', '2', '6', '7', '1', '8', '8', '0', '9', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '7', '4', '1', '7', '2', '5', '3', '4', '5', '6', '0', '1', '1', '0', '7', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '7', '6', '3', '1', '0', '7', '8', '8', '7', '1', '1', '5', '4', '6', '3', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_046_before_generic"
  err.flush

theorem array_moment_records_chunk_046 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 47)
      (SourceJson.white (momentRecordsChunk046Chars ++ tail)) acc =
      SourceJson.array (fuel + 46) (SourceJson.white tail) (momentRecordsChunk046Push acc) := by rfl

noncomputable def momentRecordsAcc047 : List SourceJson := momentRecordsChunk046Push momentRecordsAcc046

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_046_generic_complete"
  err.flush

noncomputable def momentRecordsChunk047Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '2', '8', '1', '1', '7', '1', '5', '7', '2', '5', '9', '8', '6', '0', '1', '8', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '3', '2', '0', '4', '8', '0', '7', '4', '9', '0', '3', '2', '8', '4', '6', '8', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '2', '7', '3', '0', '2', '8', '2', '5', '1', '2', '8', '7', '0', '5', '3', '5', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '2', '4', '9', '0', '3', '5', '1', '3', '2', '1', '3', '4', '7', '2', '8', '9', '5', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '7', '7', '8', '3', '9', '0', '7', '9', '2', '4', '4', '8', '0', '2', '0', '2', '9', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '0', '4', '8', '6', '7', '6', '4', '7', '7', '0', '3', '0', '0', '6', '0', '2', '1', '8', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '7', '1', '4', '8', '4', '2', '9', '6', '6', '1', '2', '2', '5', '7', '9', '4', '1', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '8', '6', '7', '0', '3', '1', '4', '5', '9', '7', '5', '4', '3', '7', '5', '2', '7', '8', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '2', '9', '2', '6', '7', '2', '0', '6', '4', '4', '4', '6', '7', '6', '4', '9', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '3', '1', '9', '8', '7', '0', '0', '6', '0', '4', '4', '2', '0', '8', '1', '9', '0', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '4', '1', '9', '8', '0', '7', '2', '2', '5', '2', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '4', '3', '4', '8', '0', '5', '5', '4', '3', '0', '0', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk047Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['4', '7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '2', '5', '2', '8', '1', '1', '7', '1', '5', '7', '2', '5', '9', '8', '6', '0', '1', '8', '0', '5']), .str (String.ofList ['1', '2', '9', '3', '2', '0', '4', '8', '0', '7', '4', '9', '0', '3', '2', '8', '4', '6', '8', '9', '2']), .str (String.ofList ['1', '4', '1', '2', '7', '3', '0', '2', '8', '2', '5', '1', '2', '8', '7', '0', '5', '3', '5', '2', '4']), .str (String.ofList ['3', '9', '2', '4', '9', '0', '3', '5', '1', '3', '2', '1', '3', '4', '7', '2', '8', '9', '5', '5', '6']), .str (String.ofList ['1', '9', '7', '7', '8', '3', '9', '0', '7', '9', '2', '4', '4', '8', '0', '2', '0', '2', '9', '4', '6']), .str (String.ofList ['3', '5', '0', '4', '8', '6', '7', '6', '4', '7', '7', '0', '3', '0', '0', '6', '0', '2', '1', '8', '9']), .str (String.ofList ['6', '2', '7', '1', '4', '8', '4', '2', '9', '6', '6', '1', '2', '2', '5', '7', '9', '4', '1', '0', '2']), .str (String.ofList ['3', '5', '8', '6', '7', '0', '3', '1', '4', '5', '9', '7', '5', '4', '3', '7', '5', '2', '7', '8', '5']), .str (String.ofList ['2', '4', '9', '2', '9', '2', '6', '7', '2', '0', '6', '4', '4', '4', '6', '7', '6', '4', '9', '5', '2']), .str (String.ofList ['2', '4', '9', '3', '1', '9', '8', '7', '0', '0', '6', '0', '4', '4', '2', '0', '8', '1', '9', '0', '4'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '4', '1', '9', '8', '0', '7', '2', '2', '5', '2', '0', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '4', '3', '4', '8', '0', '5', '5', '4', '3', '0', '0', '8']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_047_before_generic"
  err.flush

theorem array_moment_records_chunk_047 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 46)
      (SourceJson.white (momentRecordsChunk047Chars ++ tail)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white tail) (momentRecordsChunk047Push acc) := by rfl

noncomputable def momentRecordsAcc048 : List SourceJson := momentRecordsChunk047Push momentRecordsAcc047

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_047_generic_complete"
  err.flush

noncomputable def momentRecordsBlock011Chars : List Char := momentRecordsChunk044Chars ++ momentRecordsChunk045Chars ++ momentRecordsChunk046Chars ++ momentRecordsChunk047Chars
noncomputable def momentRecordsBlock011Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk047Push (momentRecordsChunk046Push (momentRecordsChunk045Push (momentRecordsChunk044Push (acc))))

theorem array_moment_records_block_011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 49)
      (SourceJson.white (momentRecordsBlock011Chars ++ tail)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white tail) (momentRecordsBlock011Push acc) := by
  have hinput : momentRecordsBlock011Chars ++ tail = momentRecordsChunk044Chars ++ (momentRecordsChunk045Chars ++ (momentRecordsChunk046Chars ++ (momentRecordsChunk047Chars ++ (tail)))) := by
    simp only [momentRecordsBlock011Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 49) (SourceJson.white (momentRecordsBlock011Chars ++ tail)) acc =
        SourceJson.array (fuel + 49) (SourceJson.white (momentRecordsChunk044Chars ++ (momentRecordsChunk045Chars ++ (momentRecordsChunk046Chars ++ (momentRecordsChunk047Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 49) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 48) (SourceJson.white (momentRecordsChunk045Chars ++ (momentRecordsChunk046Chars ++ (momentRecordsChunk047Chars ++ (tail))))) (momentRecordsChunk044Push (acc)) := array_moment_records_chunk_044 fuel (momentRecordsChunk045Chars ++ (momentRecordsChunk046Chars ++ (momentRecordsChunk047Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 47) (SourceJson.white (momentRecordsChunk046Chars ++ (momentRecordsChunk047Chars ++ (tail)))) (momentRecordsChunk045Push (momentRecordsChunk044Push (acc))) := array_moment_records_chunk_045 fuel (momentRecordsChunk046Chars ++ (momentRecordsChunk047Chars ++ (tail))) (momentRecordsChunk044Push (acc))
    _ = SourceJson.array (fuel + 46) (SourceJson.white (momentRecordsChunk047Chars ++ (tail))) (momentRecordsChunk046Push (momentRecordsChunk045Push (momentRecordsChunk044Push (acc)))) := array_moment_records_chunk_046 fuel (momentRecordsChunk047Chars ++ (tail)) (momentRecordsChunk045Push (momentRecordsChunk044Push (acc)))
    _ = SourceJson.array (fuel + 45) (SourceJson.white tail) (momentRecordsBlock011Push acc) := array_moment_records_chunk_047 fuel (tail) (momentRecordsChunk046Push (momentRecordsChunk045Push (momentRecordsChunk044Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_block_011_before_raw_binding"
  err.flush

theorem moment_records_block_011_prefix :
    (momentRest00 22878).take 2048 = momentRecordsBlock011Chars := by rfl

theorem moment_records_block_011_split :
    momentRest00 22878 = momentRecordsBlock011Chars ++ momentRest00 24926 := by
  calc
    momentRest00 22878 =
        (momentRest00 22878).take 2048 ++ (momentRest00 22878).drop 2048 :=
      (List.take_append_drop 2048 (momentRest00 22878)).symm
    _ = momentRecordsBlock011Chars ++ (momentRest00 22878).drop 2048 :=
      congrArg (fun p => p ++ (momentRest00 22878).drop 2048) moment_records_block_011_prefix
    _ = momentRecordsBlock011Chars ++ momentRest00 24926 :=
      congrArg (fun rest => momentRecordsBlock011Chars ++ rest) (momentRest00_drop 22878 2048)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_block_011_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_011 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 49)
      (SourceJson.white (momentRest00 22878)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white (momentRest00 24926)) (momentRecordsBlock011Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 49) (SourceJson.white s) acc)
      moment_records_block_011_split).trans (array_moment_records_block_011 fuel (momentRest00 24926) acc)

theorem moment_records_through_block_011 (fuel : Nat) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRest00 364)) [] =
      SourceJson.array (fuel + 45) (SourceJson.white (momentRest00 24926)) momentRecordsAcc048 := by
  exact (moment_records_through_block_010 fuel).trans (array_moment_records_original_block_011 fuel momentRecordsAcc044)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_block_011_complete"
  err.flush

#print axioms array_moment_records_chunk_044
#print axioms array_moment_records_chunk_045
#print axioms array_moment_records_chunk_046
#print axioms array_moment_records_chunk_047
#print axioms array_moment_records_block_011
#print axioms moment_records_block_011_prefix
#print axioms moment_records_block_011_split
#print axioms array_moment_records_original_block_011
#print axioms moment_records_through_block_011

end ImbalancedChen.P2OriginalSaving19Moment00Parsing
