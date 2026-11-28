/- SOURCE_CANDIDATE: original Cell06 source only. No Lean compilation,
independent kernel replay, full-owned audit or formal acceptance is claimed. -/

import ImbalancedChen.P2OriginalSaving19Moment06RecordsBlock002

/-! Original moment records block 3. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment06Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk012Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '1', '6', '1', '8', '4', '2', '9', '4', '8', '4', '0', '8', '9', '4', '5', '5', '1', '0', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '8', '6', '9', '9', '0', '3', '3', '3', '2', '2', '5', '5', '8', '9', '2', '0', '5', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '1', '6', '4', '9', '2', '0', '2', '9', '1', '0', '2', '7', '9', '8', '1', '2', '1', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '7', '2', '2', '0', '1', '4', '8', '1', '7', '8', '4', '9', '7', '6', '1', '5', '4', '0', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '7', '6', '7', '5', '9', '5', '4', '6', '5', '5', '3', '8', '9', '7', '0', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '1', '5', '8', '6', '8', '4', '9', '1', '5', '8', '2', '2', '3', '4', '2', '9', '8', '1', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '7', '0', '3', '8', '3', '6', '8', '8', '9', '7', '2', '7', '8', '8', '3', '0', '5', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '5', '4', '2', '7', '6', '2', '7', '4', '2', '9', '3', '6', '2', '0', '1', '4', '5', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '8', '5', '3', '9', '7', '6', '4', '2', '1', '1', '3', '0', '0', '2', '7', '6', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '5', '1', '4', '3', '8', '7', '4', '5', '8', '6', '2', '4', '3', '7', '1', '2', '3', '5', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '9', '8', '3', '7', '0', '8', '4', '6', '3', '8', '4', '2', '0', '2', '4', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '0', '0', '6', '5', '8', '5', '7', '1', '3', '7', '6', '9', '7', '0', '8', '7', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk012Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '2'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '9', '1', '6', '1', '8', '4', '2', '9', '4', '8', '4', '0', '8', '9', '4', '5', '5', '1', '0', '3']), .str (String.ofList ['3', '5', '8', '6', '9', '9', '0', '3', '3', '3', '2', '2', '5', '5', '8', '9', '2', '0', '5', '1', '9']), .str (String.ofList ['1', '4', '1', '1', '6', '4', '9', '2', '0', '2', '9', '1', '0', '2', '7', '9', '8', '1', '2', '1', '6']), .str (String.ofList ['2', '4', '7', '2', '2', '0', '1', '4', '8', '1', '7', '8', '4', '9', '7', '6', '1', '5', '4', '0', '5']), .str (String.ofList ['2', '8', '5', '9', '7', '6', '7', '5', '9', '5', '4', '6', '5', '5', '3', '8', '9', '7', '0', '2', '9']), .str (String.ofList ['2', '6', '1', '5', '8', '6', '8', '4', '9', '1', '5', '8', '2', '2', '3', '4', '2', '9', '8', '1', '1']), .str (String.ofList ['7', '9', '7', '0', '3', '8', '3', '6', '8', '8', '9', '7', '2', '7', '8', '8', '3', '0', '5', '6', '7']), .str (String.ofList ['4', '4', '5', '4', '2', '7', '6', '2', '7', '4', '2', '9', '3', '6', '2', '0', '1', '4', '5', '2', '5']), .str (String.ofList ['5', '3', '9', '8', '5', '3', '9', '7', '6', '4', '2', '1', '1', '3', '0', '0', '2', '7', '6', '7', '1']), .str (String.ofList ['4', '8', '5', '1', '4', '3', '8', '7', '4', '5', '8', '6', '2', '4', '3', '7', '1', '2', '3', '5', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '9', '8', '3', '7', '0', '8', '4', '6', '3', '8', '4', '2', '0', '2', '4', '2', '6'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['7', '0', '0', '6', '5', '8', '5', '7', '1', '3', '7', '6', '9', '7', '0', '8', '7', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_012_before_generic"
  err.flush

theorem array_moment_records_chunk_012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 138)
      (SourceJson.white (momentRecordsChunk012Chars ++ tail)) acc =
      SourceJson.array (fuel + 137) (SourceJson.white tail) (momentRecordsChunk012Push acc) := by rfl

noncomputable def momentRecordsAcc013 : List SourceJson := momentRecordsChunk012Push momentRecordsAcc012

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_012_generic_complete"
  err.flush

noncomputable def momentRecordsChunk013Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '8', '3', '8', '6', '8', '3', '5', '4', '2', '5', '1', '6', '9', '4', '2', '7', '0', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '0', '1', '9', '3', '3', '1', '3', '0', '9', '6', '3', '6', '7', '3', '3', '1', '6', '7', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '3', '5', '0', '5', '2', '4', '7', '2', '4', '5', '9', '8', '5', '9', '5', '8', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '0', '7', '7', '1', '5', '7', '5', '9', '4', '8', '6', '4', '5', '3', '0', '5', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '2', '8', '4', '5', '4', '8', '0', '1', '7', '4', '3', '5', '5', '7', '5', '5', '1', '0', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '7', '5', '0', '6', '1', '3', '1', '4', '8', '4', '3', '7', '6', '5', '2', '1', '6', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '5', '7', '9', '2', '6', '4', '2', '4', '0', '2', '9', '5', '8', '0', '6', '3', '1', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '6', '6', '2', '3', '6', '9', '6', '1', '5', '2', '2', '4', '3', '7', '6', '4', '8', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '2', '0', '8', '4', '8', '0', '5', '1', '0', '0', '0', '6', '1', '1', '1', '7', '4', '4', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '6', '5', '4', '6', '3', '4', '4', '1', '9', '2', '8', '0', '0', '2', '1', '3', '9', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '7', '8', '6', '9', '2', '9', '7', '6', '2', '6', '3', '2', '4', '2', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '8', '4', '9', '0', '3', '6', '8', '6', '1', '1', '4', '5', '2', '8', '0', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk013Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '3'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '8', '8', '3', '8', '6', '8', '3', '5', '4', '2', '5', '1', '6', '9', '4', '2', '7', '0', '3', '5']), .str (String.ofList ['2', '9', '0', '1', '9', '3', '3', '1', '3', '0', '9', '6', '3', '6', '7', '3', '3', '1', '6', '7', '8']), .str (String.ofList ['1', '4', '1', '3', '5', '0', '5', '2', '4', '7', '2', '4', '5', '9', '8', '5', '9', '5', '8', '2', '8']), .str (String.ofList ['2', '4', '8', '0', '7', '7', '1', '5', '7', '5', '9', '4', '8', '6', '4', '5', '3', '0', '5', '7', '6']), .str (String.ofList ['2', '9', '2', '8', '4', '5', '4', '8', '0', '1', '7', '4', '3', '5', '5', '7', '5', '5', '1', '0', '3']), .str (String.ofList ['2', '3', '7', '5', '0', '6', '1', '3', '1', '4', '8', '4', '3', '7', '6', '5', '2', '1', '6', '3', '5']), .str (String.ofList ['8', '0', '5', '7', '9', '2', '6', '4', '2', '4', '0', '2', '9', '5', '8', '0', '6', '3', '1', '0', '4']), .str (String.ofList ['3', '4', '6', '6', '2', '3', '6', '9', '6', '1', '5', '2', '2', '4', '3', '7', '6', '4', '8', '4', '3']), .str (String.ofList ['3', '5', '2', '0', '8', '4', '8', '0', '5', '1', '0', '0', '0', '6', '1', '1', '1', '7', '4', '4', '0']), .str (String.ofList ['2', '8', '7', '6', '5', '4', '6', '3', '4', '4', '1', '9', '2', '8', '0', '0', '2', '1', '3', '9', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '2', '7', '8', '6', '9', '2', '9', '7', '6', '2', '6', '3', '2', '4', '2', '6', '0'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '2', '8', '4', '9', '0', '3', '6', '8', '6', '1', '1', '4', '5', '2', '8', '0', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_013_before_generic"
  err.flush

theorem array_moment_records_chunk_013 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 137)
      (SourceJson.white (momentRecordsChunk013Chars ++ tail)) acc =
      SourceJson.array (fuel + 136) (SourceJson.white tail) (momentRecordsChunk013Push acc) := by rfl

noncomputable def momentRecordsAcc014 : List SourceJson := momentRecordsChunk013Push momentRecordsAcc013

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_013_generic_complete"
  err.flush

noncomputable def momentRecordsChunk014Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '0', '0', '5', '0', '1', '1', '5', '2', '6', '0', '7', '5', '4', '9', '5', '8', '8', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '9', '2', '5', '7', '2', '4', '7', '9', '1', '4', '4', '6', '0', '1', '7', '0', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '2', '5', '1', '7', '6', '2', '8', '6', '1', '7', '3', '5', '6', '3', '5', '6', '0', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '1', '0', '8', '7', '5', '6', '4', '0', '0', '0', '3', '3', '5', '8', '8', '9', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '5', '6', '9', '7', '3', '3', '6', '9', '8', '1', '0', '6', '7', '6', '2', '6', '3', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '2', '8', '6', '9', '9', '7', '2', '5', '6', '9', '8', '4', '6', '3', '3', '6', '6', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '7', '6', '0', '6', '6', '9', '2', '4', '0', '0', '2', '8', '7', '2', '1', '4', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '1', '5', '1', '8', '1', '1', '0', '3', '7', '2', '2', '8', '1', '4', '5', '8', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '9', '0', '8', '1', '6', '8', '0', '7', '7', '3', '6', '9', '0', '6', '8', '7', '3', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '4', '9', '5', '3', '3', '4', '6', '2', '0', '5', '7', '2', '2', '3', '0', '9', '2', '4', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '5', '3', '3', '9', '5', '1', '3', '2', '3', '4', '7', '8', '4', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '5', '5', '8', '0', '6', '8', '7', '7', '5', '0', '2', '9', '9', '5', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk014Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '4'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '3', '0', '0', '5', '0', '1', '1', '5', '2', '6', '0', '7', '5', '4', '9', '5', '8', '8', '0', '0']), .str (String.ofList ['2', '7', '2', '9', '2', '5', '7', '2', '4', '7', '9', '1', '4', '4', '6', '0', '1', '7', '0', '6', '2']), .str (String.ofList ['1', '6', '2', '5', '1', '7', '6', '2', '8', '6', '1', '7', '3', '5', '6', '3', '5', '6', '0', '7', '1']), .str (String.ofList ['2', '4', '6', '1', '0', '8', '7', '5', '6', '4', '0', '0', '0', '3', '3', '5', '8', '8', '9', '5', '9']), .str (String.ofList ['3', '0', '5', '6', '9', '7', '3', '3', '6', '9', '8', '1', '0', '6', '7', '6', '2', '6', '3', '8', '6']), .str (String.ofList ['1', '6', '2', '8', '6', '9', '9', '7', '2', '5', '6', '9', '8', '4', '6', '3', '3', '6', '6', '0', '7']), .str (String.ofList ['1', '5', '4', '7', '6', '0', '6', '6', '9', '2', '4', '0', '0', '2', '8', '7', '2', '1', '4', '0', '4']), .str (String.ofList ['1', '6', '0', '1', '5', '1', '8', '1', '1', '0', '3', '7', '2', '2', '8', '1', '4', '5', '8', '8', '7']), .str (String.ofList ['2', '0', '3', '9', '0', '8', '1', '6', '8', '0', '7', '7', '3', '6', '9', '0', '6', '8', '7', '3', '7']), .str (String.ofList ['3', '2', '4', '9', '5', '3', '3', '4', '6', '2', '0', '5', '7', '2', '2', '3', '0', '9', '2', '4', '2'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '2', '5', '3', '3', '9', '5', '1', '3', '2', '3', '4', '7', '8', '4', '3', '9'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '2', '5', '5', '8', '0', '6', '8', '7', '7', '5', '0', '2', '9', '9', '5', '3']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_014_before_generic"
  err.flush

theorem array_moment_records_chunk_014 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 136)
      (SourceJson.white (momentRecordsChunk014Chars ++ tail)) acc =
      SourceJson.array (fuel + 135) (SourceJson.white tail) (momentRecordsChunk014Push acc) := by rfl

noncomputable def momentRecordsAcc015 : List SourceJson := momentRecordsChunk014Push momentRecordsAcc014

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_014_generic_complete"
  err.flush

noncomputable def momentRecordsChunk015Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '9', '6', '8', '8', '6', '6', '7', '8', '9', '7', '7', '4', '7', '8', '0', '5', '3', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '9', '0', '4', '3', '4', '5', '0', '3', '4', '7', '5', '1', '5', '0', '1', '0', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '6', '6', '2', '8', '5', '0', '7', '6', '4', '8', '1', '3', '5', '5', '6', '1', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '5', '0', '3', '4', '4', '3', '8', '8', '9', '9', '0', '5', '4', '6', '7', '3', '7', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '7', '7', '8', '0', '7', '0', '6', '5', '5', '0', '5', '9', '1', '9', '8', '7', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '7', '9', '7', '6', '7', '5', '8', '9', '4', '0', '9', '9', '8', '5', '9', '9', '6', '6', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '4', '1', '9', '5', '4', '8', '9', '4', '2', '7', '5', '6', '4', '8', '2', '4', '4', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '5', '8', '0', '3', '4', '5', '6', '1', '5', '8', '8', '3', '6', '2', '2', '1', '7', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '1', '2', '6', '9', '0', '1', '5', '0', '6', '6', '7', '7', '5', '5', '4', '7', '2', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '6', '1', '3', '3', '8', '7', '4', '1', '8', '3', '2', '6', '6', '2', '6', '8', '3', '4', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '8', '9', '8', '0', '5', '3', '6', '3', '9', '8', '0', '3', '6', '7', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '9', '2', '4', '1', '0', '9', '5', '1', '2', '9', '0', '3', '8', '4', '5', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk015Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '5'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '2', '9', '6', '8', '8', '6', '6', '7', '8', '9', '7', '7', '4', '7', '8', '0', '5', '3', '6', '4']), .str (String.ofList ['2', '7', '2', '9', '0', '4', '3', '4', '5', '0', '3', '4', '7', '5', '1', '5', '0', '1', '0', '5', '3']), .str (String.ofList ['1', '4', '9', '6', '6', '2', '8', '5', '0', '7', '6', '4', '8', '1', '3', '5', '5', '6', '1', '2', '6']), .str (String.ofList ['2', '5', '5', '0', '3', '4', '4', '3', '8', '8', '9', '9', '0', '5', '4', '6', '7', '3', '7', '5', '1']), .str (String.ofList ['3', '0', '3', '7', '7', '8', '0', '7', '0', '6', '5', '5', '0', '5', '9', '1', '9', '8', '7', '7', '4']), .str (String.ofList ['1', '9', '7', '9', '7', '6', '7', '5', '8', '9', '4', '0', '9', '9', '8', '5', '9', '9', '6', '6', '0']), .str (String.ofList ['7', '6', '4', '1', '9', '5', '4', '8', '9', '4', '2', '7', '5', '6', '4', '8', '2', '4', '4', '2', '4']), .str (String.ofList ['2', '7', '7', '5', '8', '0', '3', '4', '5', '6', '1', '5', '8', '8', '3', '6', '2', '2', '1', '7', '9']), .str (String.ofList ['3', '0', '1', '2', '6', '9', '0', '1', '5', '0', '6', '6', '7', '7', '5', '5', '4', '7', '2', '6', '4']), .str (String.ofList ['3', '2', '6', '1', '3', '3', '8', '7', '4', '1', '8', '3', '2', '6', '6', '2', '6', '8', '3', '4', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '8', '9', '8', '0', '5', '3', '6', '3', '9', '8', '0', '3', '6', '7', '9', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '9', '2', '4', '1', '0', '9', '5', '1', '2', '9', '0', '3', '8', '4', '5', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_015_before_generic"
  err.flush

theorem array_moment_records_chunk_015 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 135)
      (SourceJson.white (momentRecordsChunk015Chars ++ tail)) acc =
      SourceJson.array (fuel + 134) (SourceJson.white tail) (momentRecordsChunk015Push acc) := by rfl

noncomputable def momentRecordsAcc016 : List SourceJson := momentRecordsChunk015Push momentRecordsAcc015

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_015_generic_complete"
  err.flush

noncomputable def momentRecordsBlock003Chars : List Char := momentRecordsChunk012Chars ++ momentRecordsChunk013Chars ++ momentRecordsChunk014Chars ++ momentRecordsChunk015Chars
noncomputable def momentRecordsBlock003Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk015Push (momentRecordsChunk014Push (momentRecordsChunk013Push (momentRecordsChunk012Push (acc))))

theorem array_moment_records_block_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 138)
      (SourceJson.white (momentRecordsBlock003Chars ++ tail)) acc =
      SourceJson.array (fuel + 134) (SourceJson.white tail) (momentRecordsBlock003Push acc) := by
  have hinput : momentRecordsBlock003Chars ++ tail = momentRecordsChunk012Chars ++ (momentRecordsChunk013Chars ++ (momentRecordsChunk014Chars ++ (momentRecordsChunk015Chars ++ (tail)))) := by
    simp only [momentRecordsBlock003Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 138) (SourceJson.white (momentRecordsBlock003Chars ++ tail)) acc =
        SourceJson.array (fuel + 138) (SourceJson.white (momentRecordsChunk012Chars ++ (momentRecordsChunk013Chars ++ (momentRecordsChunk014Chars ++ (momentRecordsChunk015Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 138) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 137) (SourceJson.white (momentRecordsChunk013Chars ++ (momentRecordsChunk014Chars ++ (momentRecordsChunk015Chars ++ (tail))))) (momentRecordsChunk012Push (acc)) := array_moment_records_chunk_012 fuel (momentRecordsChunk013Chars ++ (momentRecordsChunk014Chars ++ (momentRecordsChunk015Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 136) (SourceJson.white (momentRecordsChunk014Chars ++ (momentRecordsChunk015Chars ++ (tail)))) (momentRecordsChunk013Push (momentRecordsChunk012Push (acc))) := array_moment_records_chunk_013 fuel (momentRecordsChunk014Chars ++ (momentRecordsChunk015Chars ++ (tail))) (momentRecordsChunk012Push (acc))
    _ = SourceJson.array (fuel + 135) (SourceJson.white (momentRecordsChunk015Chars ++ (tail))) (momentRecordsChunk014Push (momentRecordsChunk013Push (momentRecordsChunk012Push (acc)))) := array_moment_records_chunk_014 fuel (momentRecordsChunk015Chars ++ (tail)) (momentRecordsChunk013Push (momentRecordsChunk012Push (acc)))
    _ = SourceJson.array (fuel + 134) (SourceJson.white tail) (momentRecordsBlock003Push acc) := array_moment_records_chunk_015 fuel (tail) (momentRecordsChunk014Push (momentRecordsChunk013Push (momentRecordsChunk012Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_003_before_raw_binding"
  err.flush

theorem moment_records_block_003_prefix :
    (momentRest06 6479).take 2068 = momentRecordsBlock003Chars := by rfl

theorem moment_records_block_003_split :
    momentRest06 6479 = momentRecordsBlock003Chars ++ momentRest06 8547 := by
  calc
    momentRest06 6479 =
        (momentRest06 6479).take 2068 ++ (momentRest06 6479).drop 2068 :=
      (List.take_append_drop 2068 (momentRest06 6479)).symm
    _ = momentRecordsBlock003Chars ++ (momentRest06 6479).drop 2068 :=
      congrArg (fun p => p ++ (momentRest06 6479).drop 2068) moment_records_block_003_prefix
    _ = momentRecordsBlock003Chars ++ momentRest06 8547 :=
      congrArg (fun rest => momentRecordsBlock003Chars ++ rest) (momentRest06_drop 6479 2068)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_003_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_003 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 138)
      (SourceJson.white (momentRest06 6479)) acc =
      SourceJson.array (fuel + 134) (SourceJson.white (momentRest06 8547)) (momentRecordsBlock003Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 138) (SourceJson.white s) acc)
      moment_records_block_003_split).trans (array_moment_records_block_003 fuel (momentRest06 8547) acc)

theorem moment_records_through_block_003 (fuel : Nat) :
    SourceJson.array (fuel + 150)
      (SourceJson.white (momentRest06 364)) [] =
      SourceJson.array (fuel + 134) (SourceJson.white (momentRest06 8547)) momentRecordsAcc016 := by
  exact (moment_records_through_block_002 fuel).trans (array_moment_records_original_block_003 fuel momentRecordsAcc012)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_003_complete"
  err.flush

#print axioms array_moment_records_chunk_012
#print axioms array_moment_records_chunk_013
#print axioms array_moment_records_chunk_014
#print axioms array_moment_records_chunk_015
#print axioms array_moment_records_block_003
#print axioms moment_records_block_003_prefix
#print axioms moment_records_block_003_split
#print axioms array_moment_records_original_block_003
#print axioms moment_records_through_block_003

end ImbalancedChen.P2OriginalSaving19Moment06Parsing
