/- SOURCE_CANDIDATE: original Cell06 source only. No Lean compilation,
independent kernel replay, full-owned audit or formal acceptance is claimed. -/

import ImbalancedChen.P2OriginalSaving19Moment06RecordsBlock000

/-! Original moment records block 1. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment06Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk004Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '9', '7', '4', '6', '9', '9', '3', '6', '4', '0', '9', '6', '9', '9', '3', '2', '3', '1', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '2', '5', '7', '4', '0', '1', '7', '7', '6', '3', '9', '7', '7', '2', '1', '9', '7', '8', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '2', '5', '4', '1', '3', '5', '8', '4', '4', '9', '5', '4', '3', '4', '9', '8', '8', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '0', '2', '1', '1', '9', '5', '6', '1', '6', '0', '1', '0', '0', '0', '7', '7', '8', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '8', '1', '6', '0', '1', '4', '7', '0', '2', '3', '8', '8', '0', '1', '6', '3', '4', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '8', '6', '4', '4', '9', '6', '3', '9', '7', '6', '5', '3', '7', '9', '3', '4', '0', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '1', '7', '7', '7', '1', '0', '0', '8', '5', '0', '3', '6', '6', '4', '5', '2', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '7', '9', '3', '6', '8', '3', '1', '5', '8', '7', '2', '4', '0', '5', '8', '0', '8', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '8', '0', '4', '1', '3', '5', '2', '5', '9', '5', '5', '1', '1', '7', '8', '4', '9', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '6', '2', '8', '6', '9', '8', '5', '6', '2', '2', '3', '3', '1', '8', '9', '6', '9', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '3', '1', '8', '4', '9', '3', '1', '5', '7', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '3', '5', '0', '1', '0', '5', '8', '5', '8', '3', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk004Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['4'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '9', '9', '7', '4', '6', '9', '9', '3', '6', '4', '0', '9', '6', '9', '9', '3', '2', '3', '1', '1']), .str (String.ofList ['3', '2', '2', '5', '7', '4', '0', '1', '7', '7', '6', '3', '9', '7', '7', '2', '1', '9', '7', '8', '9']), .str (String.ofList ['1', '6', '2', '5', '4', '1', '3', '5', '8', '4', '4', '9', '5', '4', '3', '4', '9', '8', '8', '0', '4']), .str (String.ofList ['2', '6', '0', '2', '1', '1', '9', '5', '6', '1', '6', '0', '1', '0', '0', '0', '7', '7', '8', '2', '7']), .str (String.ofList ['3', '1', '8', '1', '6', '0', '1', '4', '7', '0', '2', '3', '8', '8', '0', '1', '6', '3', '4', '8', '1']), .str (String.ofList ['1', '8', '8', '6', '4', '4', '9', '6', '3', '9', '7', '6', '5', '3', '7', '9', '3', '4', '0', '2', '5']), .str (String.ofList ['1', '6', '7', '1', '7', '7', '7', '1', '0', '0', '8', '5', '0', '3', '6', '6', '4', '5', '2', '2', '8']), .str (String.ofList ['1', '6', '5', '7', '9', '3', '6', '8', '3', '1', '5', '8', '7', '2', '4', '0', '5', '8', '0', '8', '9']), .str (String.ofList ['1', '6', '5', '8', '0', '4', '1', '3', '5', '2', '5', '9', '5', '5', '1', '1', '7', '8', '4', '9', '4']), .str (String.ofList ['3', '4', '1', '6', '2', '8', '6', '9', '8', '5', '6', '2', '2', '3', '3', '1', '8', '9', '6', '9', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '5', '3', '1', '8', '4', '9', '3', '1', '5', '7', '1', '9'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '5', '3', '5', '0', '1', '0', '5', '8', '5', '8', '3', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_004_before_generic"
  err.flush

theorem array_moment_records_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 146)
      (SourceJson.white (momentRecordsChunk004Chars ++ tail)) acc =
      SourceJson.array (fuel + 145) (SourceJson.white tail) (momentRecordsChunk004Push acc) := by rfl

noncomputable def momentRecordsAcc005 : List SourceJson := momentRecordsChunk004Push momentRecordsAcc004

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_004_generic_complete"
  err.flush

noncomputable def momentRecordsChunk005Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '4', '3', '0', '6', '8', '6', '4', '3', '6', '9', '2', '8', '6', '7', '6', '7', '1', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '2', '7', '0', '7', '6', '3', '3', '5', '3', '7', '8', '6', '1', '7', '8', '1', '8', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '6', '3', '0', '1', '8', '1', '5', '9', '5', '9', '8', '9', '5', '1', '2', '6', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '7', '4', '1', '7', '6', '4', '9', '7', '7', '3', '5', '7', '9', '4', '8', '2', '1', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '4', '4', '1', '7', '8', '9', '4', '1', '4', '3', '1', '1', '3', '6', '2', '1', '2', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '5', '7', '7', '3', '2', '4', '7', '9', '3', '9', '1', '8', '4', '0', '9', '7', '6', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '7', '3', '5', '7', '0', '2', '1', '9', '9', '1', '1', '6', '7', '0', '0', '7', '1', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '8', '9', '6', '0', '6', '3', '7', '6', '8', '9', '1', '9', '4', '0', '2', '1', '1', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '8', '9', '6', '8', '7', '2', '7', '4', '7', '5', '4', '3', '9', '1', '8', '5', '0', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '2', '9', '2', '8', '2', '6', '9', '7', '6', '0', '9', '1', '7', '5', '5', '6', '1', '2', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '0', '9', '4', '8', '9', '6', '8', '3', '9', '4', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '1', '2', '8', '6', '8', '4', '3', '5', '6', '0', '9', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk005Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '9', '4', '3', '0', '6', '8', '6', '4', '3', '6', '9', '2', '8', '6', '7', '6', '7', '1', '4', '2']), .str (String.ofList ['3', '2', '2', '7', '0', '7', '6', '3', '3', '5', '3', '7', '8', '6', '1', '7', '8', '1', '8', '3', '8']), .str (String.ofList ['1', '4', '9', '6', '3', '0', '1', '8', '1', '5', '9', '5', '9', '8', '9', '5', '1', '2', '6', '1', '3']), .str (String.ofList ['2', '6', '7', '4', '1', '7', '6', '4', '9', '7', '7', '3', '5', '7', '9', '4', '8', '2', '1', '9', '0']), .str (String.ofList ['3', '1', '4', '4', '1', '7', '8', '9', '4', '1', '4', '3', '1', '1', '3', '6', '2', '1', '2', '7', '1']), .str (String.ofList ['2', '1', '5', '7', '7', '3', '2', '4', '7', '9', '3', '9', '1', '8', '4', '0', '9', '7', '6', '9', '1']), .str (String.ofList ['8', '2', '7', '3', '5', '7', '0', '2', '1', '9', '9', '1', '1', '6', '7', '0', '0', '7', '1', '0', '0']), .str (String.ofList ['2', '6', '8', '9', '6', '0', '6', '3', '7', '6', '8', '9', '1', '9', '4', '0', '2', '1', '1', '7', '1']), .str (String.ofList ['2', '6', '8', '9', '6', '8', '7', '2', '7', '4', '7', '5', '4', '3', '9', '1', '8', '5', '0', '5', '2']), .str (String.ofList ['3', '4', '2', '9', '2', '8', '2', '6', '9', '7', '6', '0', '9', '1', '7', '5', '5', '6', '1', '2', '3'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '2', '0', '9', '4', '8', '9', '6', '8', '3', '9', '4', '6', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['1', '2', '1', '2', '8', '6', '8', '4', '3', '5', '6', '0', '9', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_005_before_generic"
  err.flush

theorem array_moment_records_chunk_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 145)
      (SourceJson.white (momentRecordsChunk005Chars ++ tail)) acc =
      SourceJson.array (fuel + 144) (SourceJson.white tail) (momentRecordsChunk005Push acc) := by rfl

noncomputable def momentRecordsAcc006 : List SourceJson := momentRecordsChunk005Push momentRecordsAcc005

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_005_generic_complete"
  err.flush

noncomputable def momentRecordsChunk006Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '1', '2', '6', '0', '6', '1', '6', '4', '5', '9', '3', '9', '2', '1', '1', '6', '4', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '8', '0', '9', '5', '0', '2', '1', '5', '7', '3', '0', '9', '3', '5', '0', '7', '8', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '0', '3', '9', '8', '2', '7', '9', '9', '8', '0', '9', '3', '3', '2', '7', '2', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '3', '7', '2', '8', '2', '6', '7', '9', '2', '2', '5', '9', '8', '2', '0', '2', '1', '3', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '1', '6', '9', '9', '8', '9', '9', '2', '8', '9', '2', '1', '4', '8', '0', '6', '6', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '1', '5', '8', '7', '5', '2', '6', '3', '2', '7', '1', '0', '3', '7', '9', '1', '6', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '6', '8', '8', '1', '6', '1', '5', '6', '7', '8', '4', '3', '9', '9', '0', '4', '2', '3', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '5', '6', '9', '6', '2', '0', '8', '5', '4', '2', '6', '8', '1', '3', '9', '1', '4', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '5', '7', '0', '8', '2', '8', '4', '8', '9', '9', '9', '0', '0', '7', '4', '7', '4', '9', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '9', '2', '1', '1', '9', '3', '0', '0', '7', '8', '0', '5', '0', '3', '0', '6', '2', '3', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '4', '5', '6', '8', '2', '8', '1', '4', '7', '4', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '6', '5', '4', '1', '6', '8', '4', '6', '1', '8', '8', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk006Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['6'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['4', '6', '1', '2', '6', '0', '6', '1', '6', '4', '5', '9', '3', '9', '2', '1', '1', '6', '4', '1', '0']), .str (String.ofList ['4', '1', '8', '0', '9', '5', '0', '2', '1', '5', '7', '3', '0', '9', '3', '5', '0', '7', '8', '4', '9']), .str (String.ofList ['1', '4', '0', '0', '3', '9', '8', '2', '7', '9', '9', '8', '0', '9', '3', '3', '2', '7', '2', '2', '0']), .str (String.ofList ['2', '5', '3', '7', '2', '8', '2', '6', '7', '9', '2', '2', '5', '9', '8', '2', '0', '2', '1', '3', '1']), .str (String.ofList ['2', '9', '1', '6', '9', '9', '8', '9', '9', '2', '8', '9', '2', '1', '4', '8', '0', '6', '6', '6', '2']), .str (String.ofList ['2', '5', '1', '5', '8', '7', '5', '2', '6', '3', '2', '7', '1', '0', '3', '7', '9', '1', '6', '1', '3']), .str (String.ofList ['8', '6', '8', '8', '1', '6', '1', '5', '6', '7', '8', '4', '3', '9', '9', '0', '4', '2', '3', '4', '6']), .str (String.ofList ['4', '0', '5', '6', '9', '6', '2', '0', '8', '5', '4', '2', '6', '8', '1', '3', '9', '1', '4', '2', '2']), .str (String.ofList ['4', '0', '5', '7', '0', '8', '2', '8', '4', '8', '9', '9', '9', '0', '0', '7', '4', '7', '4', '9', '0']), .str (String.ofList ['5', '0', '9', '2', '1', '1', '9', '3', '0', '0', '7', '8', '0', '5', '0', '3', '0', '6', '2', '3', '7'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '9', '4', '5', '6', '8', '2', '8', '1', '4', '7', '4', '1', '7'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '9', '6', '5', '4', '1', '6', '8', '4', '6', '1', '8', '8', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_006_before_generic"
  err.flush

theorem array_moment_records_chunk_006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 144)
      (SourceJson.white (momentRecordsChunk006Chars ++ tail)) acc =
      SourceJson.array (fuel + 143) (SourceJson.white tail) (momentRecordsChunk006Push acc) := by rfl

noncomputable def momentRecordsAcc007 : List SourceJson := momentRecordsChunk006Push momentRecordsAcc006

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_006_generic_complete"
  err.flush

noncomputable def momentRecordsChunk007Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '1', '3', '6', '8', '8', '0', '9', '5', '3', '4', '4', '1', '1', '0', '7', '6', '3', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '3', '8', '4', '0', '4', '8', '5', '9', '0', '2', '7', '0', '0', '2', '8', '4', '2', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '4', '5', '9', '8', '5', '5', '4', '1', '4', '8', '7', '2', '2', '5', '2', '3', '1', '8', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '3', '7', '9', '5', '9', '7', '8', '1', '8', '5', '4', '9', '8', '3', '8', '8', '0', '1', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '2', '7', '8', '0', '3', '8', '3', '5', '3', '1', '8', '0', '3', '8', '8', '6', '8', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '2', '0', '2', '5', '2', '9', '5', '5', '1', '4', '8', '9', '9', '1', '7', '1', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '0', '3', '8', '5', '4', '0', '0', '7', '9', '8', '5', '5', '7', '2', '8', '5', '2', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '2', '2', '1', '9', '1', '8', '8', '1', '9', '5', '7', '8', '7', '0', '6', '9', '1', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '2', '1', '8', '9', '4', '7', '9', '0', '5', '1', '2', '6', '3', '5', '0', '5', '1', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '6', '7', '0', '3', '1', '5', '2', '6', '4', '0', '2', '9', '4', '1', '7', '4', '9', '6', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '9', '1', '9', '2', '3', '8', '7', '2', '2', '2', '9', '9', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '7', '0', '4', '6', '4', '8', '7', '7', '5', '4', '9', '2', '0', '8', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk007Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['7'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '2', '1', '3', '6', '8', '8', '0', '9', '5', '3', '4', '4', '1', '1', '0', '7', '6', '3', '5', '7']), .str (String.ofList ['2', '7', '7', '3', '8', '4', '0', '4', '8', '5', '9', '0', '2', '7', '0', '0', '2', '8', '4', '2', '3']), .str (String.ofList ['1', '7', '4', '5', '9', '8', '5', '5', '4', '1', '4', '8', '7', '2', '2', '5', '2', '3', '1', '8', '9']), .str (String.ofList ['2', '3', '3', '7', '9', '5', '9', '7', '8', '1', '8', '5', '4', '9', '8', '3', '8', '8', '0', '1', '5']), .str (String.ofList ['3', '0', '2', '7', '8', '0', '3', '8', '3', '5', '3', '1', '8', '0', '3', '8', '8', '6', '8', '2', '5']), .str (String.ofList ['1', '6', '5', '2', '0', '2', '5', '2', '9', '5', '5', '1', '4', '8', '9', '9', '1', '7', '1', '4', '8']), .str (String.ofList ['1', '5', '0', '3', '8', '5', '4', '0', '0', '7', '9', '8', '5', '5', '7', '2', '8', '5', '2', '5', '1']), .str (String.ofList ['1', '5', '2', '2', '1', '9', '1', '8', '8', '1', '9', '5', '7', '8', '7', '0', '6', '9', '1', '6', '1']), .str (String.ofList ['2', '0', '2', '1', '8', '9', '4', '7', '9', '0', '5', '1', '2', '6', '3', '5', '0', '5', '1', '1', '0']), .str (String.ofList ['3', '1', '6', '7', '0', '3', '1', '5', '2', '6', '4', '0', '2', '9', '4', '1', '7', '4', '9', '6', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '6', '9', '1', '9', '2', '3', '8', '7', '2', '2', '2', '9', '9', '9', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '7', '0', '4', '6', '4', '8', '7', '7', '5', '4', '9', '2', '0', '8', '0']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_007_before_generic"
  err.flush

theorem array_moment_records_chunk_007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 143)
      (SourceJson.white (momentRecordsChunk007Chars ++ tail)) acc =
      SourceJson.array (fuel + 142) (SourceJson.white tail) (momentRecordsChunk007Push acc) := by rfl

noncomputable def momentRecordsAcc008 : List SourceJson := momentRecordsChunk007Push momentRecordsAcc007

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_007_generic_complete"
  err.flush

noncomputable def momentRecordsBlock001Chars : List Char := momentRecordsChunk004Chars ++ momentRecordsChunk005Chars ++ momentRecordsChunk006Chars ++ momentRecordsChunk007Chars
noncomputable def momentRecordsBlock001Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk007Push (momentRecordsChunk006Push (momentRecordsChunk005Push (momentRecordsChunk004Push (acc))))

theorem array_moment_records_block_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 146)
      (SourceJson.white (momentRecordsBlock001Chars ++ tail)) acc =
      SourceJson.array (fuel + 142) (SourceJson.white tail) (momentRecordsBlock001Push acc) := by
  have hinput : momentRecordsBlock001Chars ++ tail = momentRecordsChunk004Chars ++ (momentRecordsChunk005Chars ++ (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail)))) := by
    simp only [momentRecordsBlock001Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 146) (SourceJson.white (momentRecordsBlock001Chars ++ tail)) acc =
        SourceJson.array (fuel + 146) (SourceJson.white (momentRecordsChunk004Chars ++ (momentRecordsChunk005Chars ++ (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 146) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 145) (SourceJson.white (momentRecordsChunk005Chars ++ (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail))))) (momentRecordsChunk004Push (acc)) := array_moment_records_chunk_004 fuel (momentRecordsChunk005Chars ++ (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 144) (SourceJson.white (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail)))) (momentRecordsChunk005Push (momentRecordsChunk004Push (acc))) := array_moment_records_chunk_005 fuel (momentRecordsChunk006Chars ++ (momentRecordsChunk007Chars ++ (tail))) (momentRecordsChunk004Push (acc))
    _ = SourceJson.array (fuel + 143) (SourceJson.white (momentRecordsChunk007Chars ++ (tail))) (momentRecordsChunk006Push (momentRecordsChunk005Push (momentRecordsChunk004Push (acc)))) := array_moment_records_chunk_006 fuel (momentRecordsChunk007Chars ++ (tail)) (momentRecordsChunk005Push (momentRecordsChunk004Push (acc)))
    _ = SourceJson.array (fuel + 142) (SourceJson.white tail) (momentRecordsBlock001Push acc) := array_moment_records_chunk_007 fuel (tail) (momentRecordsChunk006Push (momentRecordsChunk005Push (momentRecordsChunk004Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_001_before_raw_binding"
  err.flush

theorem moment_records_block_001_prefix :
    (momentRest06 2389).take 2038 = momentRecordsBlock001Chars := by rfl

theorem moment_records_block_001_split :
    momentRest06 2389 = momentRecordsBlock001Chars ++ momentRest06 4427 := by
  calc
    momentRest06 2389 =
        (momentRest06 2389).take 2038 ++ (momentRest06 2389).drop 2038 :=
      (List.take_append_drop 2038 (momentRest06 2389)).symm
    _ = momentRecordsBlock001Chars ++ (momentRest06 2389).drop 2038 :=
      congrArg (fun p => p ++ (momentRest06 2389).drop 2038) moment_records_block_001_prefix
    _ = momentRecordsBlock001Chars ++ momentRest06 4427 :=
      congrArg (fun rest => momentRecordsBlock001Chars ++ rest) (momentRest06_drop 2389 2038)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_001_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_001 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 146)
      (SourceJson.white (momentRest06 2389)) acc =
      SourceJson.array (fuel + 142) (SourceJson.white (momentRest06 4427)) (momentRecordsBlock001Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 146) (SourceJson.white s) acc)
      moment_records_block_001_split).trans (array_moment_records_block_001 fuel (momentRest06 4427) acc)

theorem moment_records_through_block_001 (fuel : Nat) :
    SourceJson.array (fuel + 150)
      (SourceJson.white (momentRest06 364)) [] =
      SourceJson.array (fuel + 142) (SourceJson.white (momentRest06 4427)) momentRecordsAcc008 := by
  exact (moment_records_through_block_000 fuel).trans (array_moment_records_original_block_001 fuel momentRecordsAcc004)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_001_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment06Parsing
