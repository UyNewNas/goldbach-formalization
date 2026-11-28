/- SOURCE_CANDIDATE: original Cell06 source only. No Lean compilation,
independent kernel replay, full-owned audit or formal acceptance is claimed. -/

import ImbalancedChen.P2OriginalSaving19Moment06RecordsBlock003

/-! Original moment records block 4. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment06Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk016Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '1', '6', '1', '3', '2', '1', '0', '0', '7', '7', '5', '5', '7', '7', '0', '7', '0', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '8', '6', '9', '5', '8', '8', '3', '8', '9', '7', '7', '6', '4', '1', '9', '8', '3', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '1', '0', '1', '4', '2', '0', '2', '0', '6', '5', '5', '4', '8', '9', '3', '4', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '2', '7', '6', '6', '9', '1', '4', '2', '9', '2', '3', '7', '9', '2', '2', '4', '8', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '2', '5', '6', '5', '5', '2', '9', '3', '5', '3', '6', '5', '1', '4', '9', '1', '9', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '2', '7', '8', '5', '4', '4', '2', '4', '3', '8', '5', '6', '2', '1', '3', '6', '0', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '4', '0', '2', '2', '1', '3', '7', '2', '6', '1', '6', '3', '3', '9', '8', '6', '4', '1', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '9', '2', '1', '7', '8', '8', '9', '7', '2', '3', '8', '5', '6', '5', '4', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '7', '8', '9', '8', '3', '5', '7', '0', '2', '3', '3', '4', '4', '3', '1', '5', '0', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '5', '1', '4', '7', '8', '7', '6', '9', '6', '7', '1', '0', '9', '6', '2', '2', '2', '5', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '8', '6', '7', '2', '6', '4', '1', '2', '1', '1', '8', '2', '2', '2', '7', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '8', '8', '2', '4', '9', '1', '6', '3', '3', '2', '1', '9', '6', '0', '2', '8', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk016Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '9', '1', '6', '1', '3', '2', '1', '0', '0', '7', '7', '5', '5', '7', '7', '0', '7', '0', '8', '0']), .str (String.ofList ['3', '5', '8', '6', '9', '5', '8', '8', '3', '8', '9', '7', '7', '6', '4', '1', '9', '8', '3', '1', '4']), .str (String.ofList ['1', '4', '0', '1', '0', '1', '4', '2', '0', '2', '0', '6', '5', '5', '4', '8', '9', '3', '4', '5', '5']), .str (String.ofList ['2', '4', '2', '7', '6', '6', '9', '1', '4', '2', '9', '2', '3', '7', '9', '2', '2', '4', '8', '7', '4']), .str (String.ofList ['2', '8', '2', '5', '6', '5', '5', '2', '9', '3', '5', '3', '6', '5', '1', '4', '9', '1', '9', '3', '9']), .str (String.ofList ['2', '4', '2', '7', '8', '5', '4', '4', '2', '4', '3', '8', '5', '6', '2', '1', '3', '6', '0', '2', '9']), .str (String.ofList ['7', '9', '4', '0', '2', '2', '1', '3', '7', '2', '6', '1', '6', '3', '3', '9', '8', '6', '4', '1', '8']), .str (String.ofList ['3', '9', '0', '6', '9', '2', '1', '7', '8', '8', '9', '7', '2', '3', '8', '5', '6', '5', '4', '7', '4']), .str (String.ofList ['4', '4', '7', '8', '9', '8', '3', '5', '7', '0', '2', '3', '3', '4', '4', '3', '1', '5', '0', '3', '6']), .str (String.ofList ['4', '8', '5', '1', '4', '7', '8', '7', '6', '9', '6', '7', '1', '0', '9', '6', '2', '2', '2', '5', '9'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '8', '6', '7', '2', '6', '4', '1', '2', '1', '1', '8', '2', '2', '2', '7', '5', '9'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '8', '8', '2', '4', '9', '1', '6', '3', '3', '2', '1', '9', '6', '0', '2', '8', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_016_before_generic"
  err.flush

theorem array_moment_records_chunk_016 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 134)
      (SourceJson.white (momentRecordsChunk016Chars ++ tail)) acc =
      SourceJson.array (fuel + 133) (SourceJson.white tail) (momentRecordsChunk016Push acc) := by rfl

noncomputable def momentRecordsAcc017 : List SourceJson := momentRecordsChunk016Push momentRecordsAcc016

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_016_generic_complete"
  err.flush

noncomputable def momentRecordsChunk017Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '7', '3', '4', '8', '0', '2', '2', '5', '9', '6', '1', '4', '4', '9', '2', '7', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '0', '4', '9', '6', '1', '8', '9', '5', '4', '9', '8', '3', '6', '2', '4', '8', '0', '6', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '7', '2', '7', '2', '0', '5', '5', '7', '2', '4', '4', '2', '6', '9', '4', '4', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '7', '6', '5', '0', '6', '0', '4', '1', '1', '4', '7', '0', '2', '2', '7', '3', '8', '7', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '5', '0', '0', '1', '7', '5', '6', '5', '7', '1', '3', '1', '0', '6', '5', '9', '2', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '2', '6', '8', '7', '2', '1', '8', '1', '4', '4', '2', '6', '3', '3', '6', '0', '7', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '6', '1', '1', '7', '2', '8', '3', '4', '2', '5', '3', '1', '5', '4', '9', '5', '4', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '5', '0', '4', '9', '0', '1', '4', '8', '8', '8', '0', '0', '2', '2', '4', '4', '4', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '7', '5', '1', '7', '2', '6', '1', '5', '8', '3', '4', '6', '0', '4', '4', '1', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '2', '3', '5', '0', '4', '9', '8', '7', '4', '7', '6', '6', '7', '1', '1', '5', '7', '7', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '6', '7', '0', '2', '0', '2', '6', '3', '0', '8', '9', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '6', '7', '7', '9', '7', '8', '9', '0', '3', '5', '1', '0', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk017Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '7', '8', '7', '3', '4', '8', '0', '2', '2', '5', '9', '6', '1', '4', '4', '9', '2', '7', '9', '6']), .str (String.ofList ['3', '0', '0', '4', '9', '6', '1', '8', '9', '5', '4', '9', '8', '3', '6', '2', '4', '8', '0', '6', '9']), .str (String.ofList ['1', '2', '2', '7', '2', '7', '2', '0', '5', '5', '7', '2', '4', '4', '2', '6', '9', '4', '4', '5', '5']), .str (String.ofList ['2', '6', '7', '6', '5', '0', '6', '0', '4', '1', '1', '4', '7', '0', '2', '2', '7', '3', '8', '7', '7']), .str (String.ofList ['2', '9', '5', '0', '0', '1', '7', '5', '6', '5', '7', '1', '3', '1', '0', '6', '5', '9', '2', '9', '2']), .str (String.ofList ['2', '2', '2', '6', '8', '7', '2', '1', '8', '1', '4', '4', '2', '6', '3', '3', '6', '0', '7', '0', '4']), .str (String.ofList ['7', '7', '6', '1', '1', '7', '2', '8', '3', '4', '2', '5', '3', '1', '5', '4', '9', '5', '4', '8', '3']), .str (String.ofList ['3', '6', '5', '0', '4', '9', '0', '1', '4', '8', '8', '8', '0', '0', '2', '2', '4', '4', '4', '9', '8']), .str (String.ofList ['4', '5', '4', '7', '5', '1', '7', '2', '6', '1', '5', '8', '3', '4', '6', '0', '4', '4', '1', '4', '9']), .str (String.ofList ['4', '3', '2', '3', '5', '0', '4', '9', '8', '7', '4', '7', '6', '6', '7', '1', '1', '5', '7', '7', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '6', '7', '0', '2', '0', '2', '6', '3', '0', '8', '9', '2', '9'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '6', '7', '7', '9', '7', '8', '9', '0', '3', '5', '1', '0', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_017_before_generic"
  err.flush

theorem array_moment_records_chunk_017 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 133)
      (SourceJson.white (momentRecordsChunk017Chars ++ tail)) acc =
      SourceJson.array (fuel + 132) (SourceJson.white tail) (momentRecordsChunk017Push acc) := by rfl

noncomputable def momentRecordsAcc018 : List SourceJson := momentRecordsChunk017Push momentRecordsAcc017

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_017_generic_complete"
  err.flush

noncomputable def momentRecordsChunk018Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '1', '1', '9', '8', '7', '4', '1', '3', '0', '9', '8', '8', '1', '0', '5', '6', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '5', '7', '6', '5', '0', '8', '9', '2', '1', '7', '8', '0', '7', '2', '7', '8', '7', '3', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '7', '2', '7', '2', '0', '5', '5', '7', '2', '4', '4', '2', '6', '9', '4', '4', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '7', '6', '6', '2', '0', '3', '5', '0', '6', '9', '0', '0', '1', '1', '7', '6', '1', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '5', '0', '0', '1', '7', '5', '6', '5', '7', '1', '3', '1', '0', '6', '5', '9', '2', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '2', '6', '8', '7', '2', '1', '8', '1', '4', '4', '2', '6', '3', '3', '6', '0', '7', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '6', '1', '1', '7', '2', '8', '3', '4', '2', '5', '3', '1', '5', '4', '9', '5', '4', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '5', '0', '4', '9', '0', '1', '4', '8', '8', '8', '0', '0', '2', '2', '4', '4', '4', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '0', '4', '7', '3', '7', '8', '3', '7', '3', '4', '6', '9', '2', '5', '0', '6', '7', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '0', '1', '3', '7', '8', '2', '9', '5', '7', '9', '4', '0', '9', '9', '4', '9', '2', '3', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '8', '7', '2', '1', '4', '7', '0', '2', '7', '5', '4', '6', '2', '4', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '9', '4', '6', '9', '6', '3', '5', '1', '9', '0', '8', '2', '7', '2', '2', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk018Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '8', '5', '1', '1', '9', '8', '7', '4', '1', '3', '0', '9', '8', '8', '1', '0', '5', '6', '2', '9']), .str (String.ofList ['2', '9', '5', '7', '6', '5', '0', '8', '9', '2', '1', '7', '8', '0', '7', '2', '7', '8', '7', '3', '3']), .str (String.ofList ['1', '2', '2', '7', '2', '7', '2', '0', '5', '5', '7', '2', '4', '4', '2', '6', '9', '4', '4', '5', '5']), .str (String.ofList ['2', '2', '7', '6', '6', '2', '0', '3', '5', '0', '6', '9', '0', '0', '1', '1', '7', '6', '1', '1', '7']), .str (String.ofList ['2', '9', '5', '0', '0', '1', '7', '5', '6', '5', '7', '1', '3', '1', '0', '6', '5', '9', '2', '9', '2']), .str (String.ofList ['2', '2', '2', '6', '8', '7', '2', '1', '8', '1', '4', '4', '2', '6', '3', '3', '6', '0', '7', '0', '4']), .str (String.ofList ['7', '7', '6', '1', '1', '7', '2', '8', '3', '4', '2', '5', '3', '1', '5', '4', '9', '5', '4', '8', '3']), .str (String.ofList ['3', '6', '5', '0', '4', '9', '0', '1', '4', '8', '8', '8', '0', '0', '2', '2', '4', '4', '4', '9', '8']), .str (String.ofList ['3', '7', '0', '4', '7', '3', '7', '8', '3', '7', '3', '4', '6', '9', '2', '5', '0', '6', '7', '1', '9']), .str (String.ofList ['2', '8', '0', '1', '3', '7', '8', '2', '9', '5', '7', '9', '4', '0', '9', '9', '4', '9', '2', '3', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '7', '8', '7', '2', '1', '4', '7', '0', '2', '7', '5', '4', '6', '2', '4', '8', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '7', '9', '4', '6', '9', '6', '3', '5', '1', '9', '0', '8', '2', '7', '2', '2', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_018_before_generic"
  err.flush

theorem array_moment_records_chunk_018 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 132)
      (SourceJson.white (momentRecordsChunk018Chars ++ tail)) acc =
      SourceJson.array (fuel + 131) (SourceJson.white tail) (momentRecordsChunk018Push acc) := by rfl

noncomputable def momentRecordsAcc019 : List SourceJson := momentRecordsChunk018Push momentRecordsAcc018

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_018_generic_complete"
  err.flush

noncomputable def momentRecordsChunk019Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '3', '7', '8', '1', '0', '0', '2', '8', '4', '9', '5', '3', '2', '9', '2', '7', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '2', '0', '3', '7', '1', '9', '0', '9', '5', '2', '0', '8', '2', '0', '1', '1', '9', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '1', '3', '4', '9', '4', '8', '6', '9', '2', '2', '5', '0', '1', '1', '3', '4', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '5', '5', '1', '9', '9', '9', '0', '6', '3', '5', '3', '5', '8', '3', '5', '5', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '5', '8', '1', '0', '1', '0', '6', '2', '2', '9', '5', '0', '0', '5', '5', '1', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '7', '4', '4', '4', '5', '2', '1', '1', '1', '6', '4', '1', '3', '3', '0', '1', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '9', '6', '5', '6', '1', '2', '9', '5', '1', '9', '2', '6', '7', '7', '1', '0', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '3', '3', '0', '8', '3', '7', '3', '7', '1', '8', '2', '8', '9', '2', '9', '4', '5', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '7', '9', '7', '8', '2', '8', '3', '2', '8', '9', '2', '6', '9', '9', '8', '8', '7', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '9', '4', '3', '3', '6', '2', '9', '0', '0', '8', '3', '0', '9', '4', '9', '5', '4', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '5', '8', '6', '1', '3', '0', '3', '5', '6', '7', '8', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '5', '9', '3', '7', '1', '6', '3', '9', '4', '8', '8', '2', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk019Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['8', '8', '3', '7', '8', '1', '0', '0', '2', '8', '4', '9', '5', '3', '2', '9', '2', '7', '0', '6']), .str (String.ofList ['2', '1', '2', '0', '3', '7', '1', '9', '0', '9', '5', '2', '0', '8', '2', '0', '1', '1', '9', '3', '1']), .str (String.ofList ['2', '7', '7', '1', '3', '4', '9', '4', '8', '6', '9', '2', '2', '5', '0', '1', '1', '3', '4', '1', '7']), .str (String.ofList ['8', '4', '5', '5', '1', '9', '9', '9', '0', '6', '3', '5', '3', '5', '8', '3', '5', '5', '1', '9']), .str (String.ofList ['1', '5', '1', '5', '8', '1', '0', '1', '0', '6', '2', '2', '9', '5', '0', '0', '5', '5', '1', '9', '3']), .str (String.ofList ['1', '2', '4', '7', '4', '4', '4', '5', '2', '1', '1', '1', '6', '4', '1', '3', '3', '0', '1', '5', '7']), .str (String.ofList ['1', '3', '1', '9', '6', '5', '6', '1', '2', '9', '5', '1', '9', '2', '6', '7', '7', '1', '0', '8', '8']), .str (String.ofList ['1', '2', '3', '3', '0', '8', '3', '7', '3', '7', '1', '8', '2', '8', '9', '2', '9', '4', '5', '1', '2']), .str (String.ofList ['3', '6', '7', '9', '7', '8', '2', '8', '3', '2', '8', '9', '2', '6', '9', '9', '8', '8', '7', '0', '5']), .str (String.ofList ['7', '8', '9', '4', '3', '3', '6', '2', '9', '0', '0', '8', '3', '0', '9', '4', '9', '5', '4', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '5', '8', '6', '1', '3', '0', '3', '5', '6', '7', '8', '8', '7'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '5', '9', '3', '7', '1', '6', '3', '9', '4', '8', '8', '2', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_019_before_generic"
  err.flush

theorem array_moment_records_chunk_019 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 131)
      (SourceJson.white (momentRecordsChunk019Chars ++ tail)) acc =
      SourceJson.array (fuel + 130) (SourceJson.white tail) (momentRecordsChunk019Push acc) := by rfl

noncomputable def momentRecordsAcc020 : List SourceJson := momentRecordsChunk019Push momentRecordsAcc019

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_019_generic_complete"
  err.flush

noncomputable def momentRecordsBlock004Chars : List Char := momentRecordsChunk016Chars ++ momentRecordsChunk017Chars ++ momentRecordsChunk018Chars ++ momentRecordsChunk019Chars
noncomputable def momentRecordsBlock004Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk019Push (momentRecordsChunk018Push (momentRecordsChunk017Push (momentRecordsChunk016Push (acc))))

theorem array_moment_records_block_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 134)
      (SourceJson.white (momentRecordsBlock004Chars ++ tail)) acc =
      SourceJson.array (fuel + 130) (SourceJson.white tail) (momentRecordsBlock004Push acc) := by
  have hinput : momentRecordsBlock004Chars ++ tail = momentRecordsChunk016Chars ++ (momentRecordsChunk017Chars ++ (momentRecordsChunk018Chars ++ (momentRecordsChunk019Chars ++ (tail)))) := by
    simp only [momentRecordsBlock004Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 134) (SourceJson.white (momentRecordsBlock004Chars ++ tail)) acc =
        SourceJson.array (fuel + 134) (SourceJson.white (momentRecordsChunk016Chars ++ (momentRecordsChunk017Chars ++ (momentRecordsChunk018Chars ++ (momentRecordsChunk019Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 134) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 133) (SourceJson.white (momentRecordsChunk017Chars ++ (momentRecordsChunk018Chars ++ (momentRecordsChunk019Chars ++ (tail))))) (momentRecordsChunk016Push (acc)) := array_moment_records_chunk_016 fuel (momentRecordsChunk017Chars ++ (momentRecordsChunk018Chars ++ (momentRecordsChunk019Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 132) (SourceJson.white (momentRecordsChunk018Chars ++ (momentRecordsChunk019Chars ++ (tail)))) (momentRecordsChunk017Push (momentRecordsChunk016Push (acc))) := array_moment_records_chunk_017 fuel (momentRecordsChunk018Chars ++ (momentRecordsChunk019Chars ++ (tail))) (momentRecordsChunk016Push (acc))
    _ = SourceJson.array (fuel + 131) (SourceJson.white (momentRecordsChunk019Chars ++ (tail))) (momentRecordsChunk018Push (momentRecordsChunk017Push (momentRecordsChunk016Push (acc)))) := array_moment_records_chunk_018 fuel (momentRecordsChunk019Chars ++ (tail)) (momentRecordsChunk017Push (momentRecordsChunk016Push (acc)))
    _ = SourceJson.array (fuel + 130) (SourceJson.white tail) (momentRecordsBlock004Push acc) := array_moment_records_chunk_019 fuel (tail) (momentRecordsChunk018Push (momentRecordsChunk017Push (momentRecordsChunk016Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_004_before_raw_binding"
  err.flush

theorem moment_records_block_004_prefix :
    (momentRest06 8547).take 2053 = momentRecordsBlock004Chars := by rfl

theorem moment_records_block_004_split :
    momentRest06 8547 = momentRecordsBlock004Chars ++ momentRest06 10600 := by
  calc
    momentRest06 8547 =
        (momentRest06 8547).take 2053 ++ (momentRest06 8547).drop 2053 :=
      (List.take_append_drop 2053 (momentRest06 8547)).symm
    _ = momentRecordsBlock004Chars ++ (momentRest06 8547).drop 2053 :=
      congrArg (fun p => p ++ (momentRest06 8547).drop 2053) moment_records_block_004_prefix
    _ = momentRecordsBlock004Chars ++ momentRest06 10600 :=
      congrArg (fun rest => momentRecordsBlock004Chars ++ rest) (momentRest06_drop 8547 2053)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_004_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_004 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 134)
      (SourceJson.white (momentRest06 8547)) acc =
      SourceJson.array (fuel + 130) (SourceJson.white (momentRest06 10600)) (momentRecordsBlock004Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 134) (SourceJson.white s) acc)
      moment_records_block_004_split).trans (array_moment_records_block_004 fuel (momentRest06 10600) acc)

theorem moment_records_through_block_004 (fuel : Nat) :
    SourceJson.array (fuel + 150)
      (SourceJson.white (momentRest06 364)) [] =
      SourceJson.array (fuel + 130) (SourceJson.white (momentRest06 10600)) momentRecordsAcc020 := by
  exact (moment_records_through_block_003 fuel).trans (array_moment_records_original_block_004 fuel momentRecordsAcc016)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_004_complete"
  err.flush

#print axioms array_moment_records_chunk_016
#print axioms array_moment_records_chunk_017
#print axioms array_moment_records_chunk_018
#print axioms array_moment_records_chunk_019
#print axioms array_moment_records_block_004
#print axioms moment_records_block_004_prefix
#print axioms moment_records_block_004_split
#print axioms array_moment_records_original_block_004
#print axioms moment_records_through_block_004

end ImbalancedChen.P2OriginalSaving19Moment06Parsing
