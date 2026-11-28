/- SOURCE_CANDIDATE: original Cell06 source only. No Lean compilation,
independent kernel replay, full-owned audit or formal acceptance is claimed. -/

import ImbalancedChen.P2OriginalSaving19Moment06RecordsBlock001

/-! Original moment records block 2. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment06Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsChunk008Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '4', '2', '7', '6', '9', '5', '3', '1', '8', '9', '1', '3', '5', '2', '1', '5', '9', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '8', '5', '5', '4', '1', '7', '2', '7', '5', '1', '0', '2', '6', '1', '4', '7', '9', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '1', '4', '9', '6', '8', '5', '5', '8', '2', '3', '2', '9', '2', '2', '7', '4', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '2', '3', '4', '3', '1', '5', '4', '0', '9', '5', '6', '5', '3', '5', '1', '8', '9', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '0', '9', '9', '2', '4', '3', '6', '8', '4', '3', '0', '2', '5', '5', '0', '5', '9', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '6', '1', '7', '3', '7', '6', '6', '0', '6', '4', '5', '2', '1', '2', '5', '1', '7', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '7', '0', '6', '8', '8', '9', '5', '5', '5', '8', '4', '7', '6', '1', '4', '7', '1', '7', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '2', '7', '1', '6', '1', '0', '4', '3', '4', '6', '9', '3', '5', '1', '5', '4', '1', '7', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '2', '9', '3', '8', '6', '4', '3', '6', '7', '9', '5', '0', '5', '5', '5', '3', '2', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '6', '9', '4', '5', '7', '1', '1', '7', '4', '3', '2', '0', '6', '1', '9', '9', '3', '5', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '2', '5', '7', '6', '8', '3', '6', '9', '2', '6', '0', '4', '1', '9', '1', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '2', '6', '8', '9', '1', '8', '8', '4', '2', '0', '9', '3', '8', '0', '7', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk008Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['8'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '2', '4', '2', '7', '6', '9', '5', '3', '1', '8', '9', '1', '3', '5', '2', '1', '5', '9', '0', '4']), .str (String.ofList ['2', '7', '7', '8', '5', '5', '4', '1', '7', '2', '7', '5', '1', '0', '2', '6', '1', '4', '7', '9', '7']), .str (String.ofList ['1', '6', '3', '1', '4', '9', '6', '8', '5', '5', '8', '2', '3', '2', '9', '2', '2', '7', '4', '1', '2']), .str (String.ofList ['2', '5', '2', '3', '4', '3', '1', '5', '4', '0', '9', '5', '6', '5', '3', '5', '1', '8', '9', '6', '3']), .str (String.ofList ['3', '1', '0', '9', '9', '2', '4', '3', '6', '8', '4', '3', '0', '2', '5', '5', '0', '5', '9', '0', '8']), .str (String.ofList ['2', '0', '7', '6', '1', '7', '3', '7', '6', '6', '0', '6', '4', '5', '2', '1', '2', '5', '1', '7', '1']), .str (String.ofList ['7', '8', '7', '0', '6', '8', '8', '9', '5', '5', '5', '8', '4', '7', '6', '1', '4', '7', '1', '7', '4']), .str (String.ofList ['2', '6', '2', '7', '1', '6', '1', '0', '4', '3', '4', '6', '9', '3', '5', '1', '5', '4', '1', '7', '7']), .str (String.ofList ['2', '8', '2', '9', '3', '8', '6', '4', '3', '6', '7', '9', '5', '0', '5', '5', '5', '3', '2', '9', '5']), .str (String.ofList ['3', '1', '6', '9', '4', '5', '7', '1', '1', '7', '4', '3', '2', '0', '6', '1', '9', '9', '3', '5', '0'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '2', '5', '7', '6', '8', '3', '6', '9', '2', '6', '0', '4', '1', '9', '1', '9'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '2', '6', '8', '9', '1', '8', '8', '4', '2', '0', '9', '3', '8', '0', '7', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_008_before_generic"
  err.flush

theorem array_moment_records_chunk_008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 142)
      (SourceJson.white (momentRecordsChunk008Chars ++ tail)) acc =
      SourceJson.array (fuel + 141) (SourceJson.white tail) (momentRecordsChunk008Push acc) := by rfl

noncomputable def momentRecordsAcc009 : List SourceJson := momentRecordsChunk008Push momentRecordsAcc008

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_008_generic_complete"
  err.flush

noncomputable def momentRecordsChunk009Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '9', '6', '9', '0', '7', '7', '5', '0', '3', '8', '1', '4', '4', '1', '1', '7', '9', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '9', '0', '4', '9', '5', '9', '2', '6', '7', '8', '5', '3', '5', '2', '5', '4', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '0', '5', '8', '4', '2', '4', '5', '4', '1', '4', '2', '2', '2', '8', '2', '8', '5', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '0', '2', '9', '6', '0', '6', '5', '5', '2', '0', '0', '1', '2', '9', '3', '3', '1', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '8', '0', '4', '4', '6', '3', '5', '8', '4', '5', '0', '5', '2', '1', '0', '5', '7', '9', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '0', '5', '1', '7', '2', '0', '1', '7', '6', '8', '0', '1', '2', '5', '2', '2', '7', '5', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '6', '9', '7', '5', '4', '4', '0', '5', '7', '9', '3', '0', '2', '4', '6', '1', '4', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '6', '1', '0', '9', '5', '1', '4', '5', '0', '5', '2', '0', '1', '4', '2', '0', '2', '9', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '9', '3', '7', '2', '9', '3', '5', '8', '8', '8', '1', '2', '7', '3', '1', '9', '7', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '6', '1', '3', '1', '1', '6', '1', '2', '1', '0', '2', '6', '7', '0', '7', '5', '2', '1', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '7', '1', '7', '5', '0', '1', '9', '0', '1', '3', '2', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '7', '4', '7', '9', '3', '8', '6', '3', '5', '9', '5', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk009Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['9'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '2', '9', '6', '9', '0', '7', '7', '5', '0', '3', '8', '1', '4', '4', '1', '1', '7', '9', '9', '1']), .str (String.ofList ['2', '7', '2', '9', '0', '4', '9', '5', '9', '2', '6', '7', '8', '5', '3', '5', '2', '5', '4', '4', '3']), .str (String.ofList ['1', '5', '0', '5', '8', '4', '2', '4', '5', '4', '1', '4', '2', '2', '2', '8', '2', '8', '5', '5', '9']), .str (String.ofList ['2', '6', '0', '2', '9', '6', '0', '6', '5', '5', '2', '0', '0', '1', '2', '9', '3', '3', '1', '5', '5']), .str (String.ofList ['3', '0', '8', '0', '4', '4', '6', '3', '5', '8', '4', '5', '0', '5', '2', '1', '0', '5', '7', '9', '4']), .str (String.ofList ['2', '3', '0', '5', '1', '7', '2', '0', '1', '7', '6', '8', '0', '1', '2', '5', '2', '2', '7', '5', '3']), .str (String.ofList ['1', '1', '9', '6', '9', '7', '5', '4', '4', '0', '5', '7', '9', '3', '0', '2', '4', '6', '1', '4', '2', '8']), .str (String.ofList ['3', '5', '6', '1', '0', '9', '5', '1', '4', '5', '0', '5', '2', '0', '1', '4', '2', '0', '2', '9', '2']), .str (String.ofList ['3', '4', '9', '3', '7', '2', '9', '3', '5', '8', '8', '8', '1', '2', '7', '3', '1', '9', '7', '1', '7']), .str (String.ofList ['3', '2', '6', '1', '3', '1', '1', '6', '1', '2', '1', '0', '2', '6', '7', '0', '7', '5', '2', '1', '5'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '7', '1', '7', '5', '0', '1', '9', '0', '1', '3', '2', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['9', '7', '4', '7', '9', '3', '8', '6', '3', '5', '9', '5', '8']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_009_before_generic"
  err.flush

theorem array_moment_records_chunk_009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 141)
      (SourceJson.white (momentRecordsChunk009Chars ++ tail)) acc =
      SourceJson.array (fuel + 140) (SourceJson.white tail) (momentRecordsChunk009Push acc) := by rfl

noncomputable def momentRecordsAcc010 : List SourceJson := momentRecordsChunk009Push momentRecordsAcc009

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_009_generic_complete"
  err.flush

noncomputable def momentRecordsChunk010Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '1', '6', '1', '5', '8', '1', '9', '8', '0', '5', '9', '2', '8', '3', '6', '5', '4', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '8', '6', '9', '7', '4', '5', '8', '6', '3', '3', '5', '0', '8', '7', '3', '2', '4', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '1', '6', '5', '0', '7', '0', '1', '7', '4', '5', '0', '8', '8', '6', '3', '9', '7', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '7', '2', '1', '9', '5', '9', '2', '5', '6', '5', '8', '6', '8', '9', '1', '4', '8', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '7', '6', '3', '1', '9', '9', '9', '1', '2', '0', '6', '3', '1', '6', '9', '5', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '1', '5', '8', '7', '6', '0', '8', '8', '8', '5', '4', '3', '6', '9', '9', '8', '4', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '8', '7', '6', '4', '8', '4', '7', '2', '4', '8', '1', '7', '3', '8', '0', '8', '4', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '9', '7', '8', '8', '0', '0', '6', '4', '8', '0', '3', '4', '4', '3', '1', '7', '2', '9', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '8', '3', '4', '4', '1', '2', '6', '6', '6', '0', '8', '8', '3', '6', '2', '9', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '5', '1', '4', '5', '8', '7', '5', '7', '9', '4', '3', '2', '7', '1', '2', '1', '8', '5', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '7', '7', '7', '3', '4', '8', '7', '9', '7', '8', '1', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '7', '9', '4', '7', '6', '7', '2', '7', '8', '4', '6', '2', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk010Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '9', '1', '6', '1', '5', '8', '1', '9', '8', '0', '5', '9', '2', '8', '3', '6', '5', '4', '6', '2']), .str (String.ofList ['3', '5', '8', '6', '9', '7', '4', '5', '8', '6', '3', '3', '5', '0', '8', '7', '3', '2', '4', '1', '3']), .str (String.ofList ['1', '4', '1', '1', '6', '5', '0', '7', '0', '1', '7', '4', '5', '0', '8', '8', '6', '3', '9', '7', '9']), .str (String.ofList ['2', '4', '7', '2', '1', '9', '5', '9', '2', '5', '6', '5', '8', '6', '8', '9', '1', '4', '8', '0', '6']), .str (String.ofList ['2', '8', '5', '9', '7', '6', '3', '1', '9', '9', '9', '1', '2', '0', '6', '3', '1', '6', '9', '5', '7']), .str (String.ofList ['2', '6', '1', '5', '8', '7', '6', '0', '8', '8', '8', '5', '4', '3', '6', '9', '9', '8', '4', '8', '3']), .str (String.ofList ['1', '1', '7', '8', '7', '6', '4', '8', '4', '7', '2', '4', '8', '1', '7', '3', '8', '0', '8', '4', '5', '5']), .str (String.ofList ['5', '0', '9', '7', '8', '8', '0', '0', '6', '4', '8', '0', '3', '4', '4', '3', '1', '7', '2', '9', '5']), .str (String.ofList ['5', '3', '9', '8', '3', '4', '4', '1', '2', '6', '6', '6', '0', '8', '8', '3', '6', '2', '9', '6', '3']), .str (String.ofList ['4', '8', '5', '1', '4', '5', '8', '7', '5', '7', '9', '4', '3', '2', '7', '1', '2', '1', '8', '5', '2'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '7', '7', '7', '3', '4', '8', '7', '9', '7', '8', '1', '0', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['4', '7', '9', '4', '7', '6', '7', '2', '7', '8', '4', '6', '2', '6']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_010_before_generic"
  err.flush

theorem array_moment_records_chunk_010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 140)
      (SourceJson.white (momentRecordsChunk010Chars ++ tail)) acc =
      SourceJson.array (fuel + 139) (SourceJson.white tail) (momentRecordsChunk010Push acc) := by rfl

noncomputable def momentRecordsAcc011 : List SourceJson := momentRecordsChunk010Push momentRecordsAcc010

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_010_generic_complete"
  err.flush

noncomputable def momentRecordsChunk011Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '5', '6', '0', '3', '9', '4', '0', '9', '8', '0', '0', '4', '1', '1', '6', '8', '8', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '8', '0', '8', '9', '4', '2', '3', '7', '1', '5', '6', '2', '5', '1', '5', '7', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '0', '9', '1', '9', '8', '1', '1', '0', '9', '0', '9', '0', '0', '0', '4', '1', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '9', '1', '8', '3', '6', '3', '2', '8', '0', '5', '5', '5', '0', '8', '4', '1', '8', '1', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '6', '6', '8', '5', '0', '3', '8', '9', '9', '1', '0', '0', '9', '6', '3', '5', '6', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '5', '0', '2', '6', '5', '7', '2', '2', '6', '6', '8', '5', '4', '8', '2', '6', '6', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '2', '2', '0', '3', '3', '5', '0', '1', '7', '8', '3', '3', '5', '0', '8', '9', '8', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '6', '6', '0', '0', '9', '7', '0', '0', '0', '6', '0', '9', '8', '9', '9', '2', '8', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '2', '8', '9', '7', '8', '4', '0', '8', '4', '2', '5', '5', '3', '2', '4', '4', '1', '1', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '7', '4', '3', '7', '7', '3', '1', '1', '7', '8', '7', '3', '5', '5', '5', '6', '8', '6', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '6', '6', '3', '3', '5', '5', '6', '0', '6', '1', '8', '3', '9', '2', '0', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '7', '5', '4', '4', '9', '4', '2', '2', '2', '3', '1', '0', '5', '7', '7', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk011Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '2', '0', '5', '6', '0', '3', '9', '4', '0', '9', '8', '0', '0', '4', '1', '1', '6', '8', '8', '0']), .str (String.ofList ['2', '7', '8', '8', '0', '8', '9', '4', '2', '3', '7', '1', '5', '6', '2', '5', '1', '5', '7', '7', '0']), .str (String.ofList ['1', '4', '9', '0', '9', '1', '9', '8', '1', '1', '0', '9', '0', '9', '0', '0', '0', '4', '1', '0', '4']), .str (String.ofList ['2', '5', '9', '1', '8', '3', '6', '3', '2', '8', '0', '5', '5', '5', '0', '8', '4', '1', '8', '1', '4']), .str (String.ofList ['3', '0', '6', '6', '8', '5', '0', '3', '8', '9', '9', '1', '0', '0', '9', '6', '3', '5', '6', '5', '9']), .str (String.ofList ['2', '3', '5', '0', '2', '6', '5', '7', '2', '2', '6', '6', '8', '5', '4', '8', '2', '6', '6', '1', '3']), .str (String.ofList ['8', '0', '2', '2', '0', '3', '3', '5', '0', '1', '7', '8', '3', '3', '5', '0', '8', '9', '8', '0', '0']), .str (String.ofList ['3', '4', '6', '6', '0', '0', '9', '7', '0', '0', '0', '6', '0', '9', '8', '9', '9', '2', '8', '0', '2']), .str (String.ofList ['3', '5', '2', '8', '9', '7', '8', '4', '0', '8', '4', '2', '5', '5', '3', '2', '4', '4', '1', '1', '7']), .str (String.ofList ['3', '1', '7', '4', '3', '7', '7', '3', '1', '1', '7', '8', '7', '3', '5', '5', '5', '6', '8', '6', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '2', '6', '6', '3', '3', '5', '5', '6', '0', '6', '1', '8', '3', '9', '2', '0', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['3', '2', '7', '5', '4', '4', '9', '4', '2', '2', '2', '3', '1', '0', '5', '7', '7', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_011_before_generic"
  err.flush

theorem array_moment_records_chunk_011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 139)
      (SourceJson.white (momentRecordsChunk011Chars ++ tail)) acc =
      SourceJson.array (fuel + 138) (SourceJson.white tail) (momentRecordsChunk011Push acc) := by rfl

noncomputable def momentRecordsAcc012 : List SourceJson := momentRecordsChunk011Push momentRecordsAcc011

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_011_generic_complete"
  err.flush

noncomputable def momentRecordsBlock002Chars : List Char := momentRecordsChunk008Chars ++ momentRecordsChunk009Chars ++ momentRecordsChunk010Chars ++ momentRecordsChunk011Chars
noncomputable def momentRecordsBlock002Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk011Push (momentRecordsChunk010Push (momentRecordsChunk009Push (momentRecordsChunk008Push (acc))))

theorem array_moment_records_block_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 142)
      (SourceJson.white (momentRecordsBlock002Chars ++ tail)) acc =
      SourceJson.array (fuel + 138) (SourceJson.white tail) (momentRecordsBlock002Push acc) := by
  have hinput : momentRecordsBlock002Chars ++ tail = momentRecordsChunk008Chars ++ (momentRecordsChunk009Chars ++ (momentRecordsChunk010Chars ++ (momentRecordsChunk011Chars ++ (tail)))) := by
    simp only [momentRecordsBlock002Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 142) (SourceJson.white (momentRecordsBlock002Chars ++ tail)) acc =
        SourceJson.array (fuel + 142) (SourceJson.white (momentRecordsChunk008Chars ++ (momentRecordsChunk009Chars ++ (momentRecordsChunk010Chars ++ (momentRecordsChunk011Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 142) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 141) (SourceJson.white (momentRecordsChunk009Chars ++ (momentRecordsChunk010Chars ++ (momentRecordsChunk011Chars ++ (tail))))) (momentRecordsChunk008Push (acc)) := array_moment_records_chunk_008 fuel (momentRecordsChunk009Chars ++ (momentRecordsChunk010Chars ++ (momentRecordsChunk011Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 140) (SourceJson.white (momentRecordsChunk010Chars ++ (momentRecordsChunk011Chars ++ (tail)))) (momentRecordsChunk009Push (momentRecordsChunk008Push (acc))) := array_moment_records_chunk_009 fuel (momentRecordsChunk010Chars ++ (momentRecordsChunk011Chars ++ (tail))) (momentRecordsChunk008Push (acc))
    _ = SourceJson.array (fuel + 139) (SourceJson.white (momentRecordsChunk011Chars ++ (tail))) (momentRecordsChunk010Push (momentRecordsChunk009Push (momentRecordsChunk008Push (acc)))) := array_moment_records_chunk_010 fuel (momentRecordsChunk011Chars ++ (tail)) (momentRecordsChunk009Push (momentRecordsChunk008Push (acc)))
    _ = SourceJson.array (fuel + 138) (SourceJson.white tail) (momentRecordsBlock002Push acc) := array_moment_records_chunk_011 fuel (tail) (momentRecordsChunk010Push (momentRecordsChunk009Push (momentRecordsChunk008Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_002_before_raw_binding"
  err.flush

theorem moment_records_block_002_prefix :
    (momentRest06 4427).take 2052 = momentRecordsBlock002Chars := by rfl

theorem moment_records_block_002_split :
    momentRest06 4427 = momentRecordsBlock002Chars ++ momentRest06 6479 := by
  calc
    momentRest06 4427 =
        (momentRest06 4427).take 2052 ++ (momentRest06 4427).drop 2052 :=
      (List.take_append_drop 2052 (momentRest06 4427)).symm
    _ = momentRecordsBlock002Chars ++ (momentRest06 4427).drop 2052 :=
      congrArg (fun p => p ++ (momentRest06 4427).drop 2052) moment_records_block_002_prefix
    _ = momentRecordsBlock002Chars ++ momentRest06 6479 :=
      congrArg (fun rest => momentRecordsBlock002Chars ++ rest) (momentRest06_drop 4427 2052)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_002_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_002 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 142)
      (SourceJson.white (momentRest06 4427)) acc =
      SourceJson.array (fuel + 138) (SourceJson.white (momentRest06 6479)) (momentRecordsBlock002Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 142) (SourceJson.white s) acc)
      moment_records_block_002_split).trans (array_moment_records_block_002 fuel (momentRest06 6479) acc)

theorem moment_records_through_block_002 (fuel : Nat) :
    SourceJson.array (fuel + 150)
      (SourceJson.white (momentRest06 364)) [] =
      SourceJson.array (fuel + 138) (SourceJson.white (momentRest06 6479)) momentRecordsAcc012 := by
  exact (moment_records_through_block_001 fuel).trans (array_moment_records_original_block_002 fuel momentRecordsAcc008)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_002_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment06Parsing
