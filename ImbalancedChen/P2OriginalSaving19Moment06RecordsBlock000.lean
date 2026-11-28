/- SOURCE_CANDIDATE: original Cell06 source only. No Lean compilation,
independent kernel replay, full-owned audit or formal acceptance is claimed. -/

import ImbalancedChen.P2OriginalSaving19Moment06Input

/-! Original moment records block 0. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment06Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsOpenChars : List Char := ['[']
noncomputable def momentRecordsAcc000 : List SourceJson := []

theorem moment_records_open_prefix :
    (momentRest06 363).take 1 = momentRecordsOpenChars := by rfl

theorem moment_records_open_split :
    momentRest06 363 = momentRecordsOpenChars ++ momentRest06 364 := by
  calc
    momentRest06 363 =
        (momentRest06 363).take 1 ++ (momentRest06 363).drop 1 :=
      (List.take_append_drop 1 (momentRest06 363)).symm
    _ = momentRecordsOpenChars ++ (momentRest06 363).drop 1 :=
      congrArg (fun p => p ++ (momentRest06 363).drop 1) moment_records_open_prefix
    _ = momentRecordsOpenChars ++ momentRest06 364 :=
      congrArg (fun rest => momentRecordsOpenChars ++ rest) (momentRest06_drop 363 1)

theorem value_moment_records_open (fuel : Nat) :
    SourceJson.value (fuel + 151) (momentRest06 363) =
      SourceJson.array (fuel + 150)
        (SourceJson.white (momentRest06 364)) [] := by
  calc
    SourceJson.value (fuel + 151) (momentRest06 363) =
        SourceJson.value (fuel + 151)
          (momentRecordsOpenChars ++ momentRest06 364) :=
      congrArg (SourceJson.value (fuel + 151)) moment_records_open_split
    _ = SourceJson.array (fuel + 150)
        (SourceJson.white (momentRest06 364)) [] := by rfl

noncomputable def momentRecordsChunk000Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '3', '9', '6', '1', '3', '1', '2', '6', '8', '6', '5', '8', '0', '5', '9', '3', '0', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '7', '2', '1', '0', '5', '4', '6', '5', '2', '9', '5', '2', '1', '5', '6', '1', '2', '5', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '7', '5', '4', '6', '0', '3', '5', '0', '5', '0', '2', '0', '9', '1', '1', '8', '3', '8', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '1', '0', '8', '9', '9', '1', '6', '6', '9', '8', '9', '0', '6', '2', '5', '0', '4', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '4', '4', '1', '9', '8', '2', '0', '0', '8', '3', '2', '0', '4', '6', '2', '7', '3', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '0', '9', '4', '5', '8', '8', '3', '9', '2', '8', '8', '5', '5', '8', '2', '9', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '9', '9', '7', '2', '4', '0', '4', '7', '4', '5', '5', '2', '3', '3', '4', '7', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '9', '9', '1', '9', '1', '8', '9', '2', '4', '9', '7', '4', '4', '6', '5', '9', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '4', '0', '0', '9', '1', '9', '3', '2', '1', '4', '3', '5', '7', '5', '6', '2', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '5', '9', '6', '7', '7', '6', '1', '6', '3', '6', '9', '8', '1', '1', '1', '0', '9', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '7', '8', '4', '4', '3', '7', '5', '9', '9', '8', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '8', '4', '2', '1', '7', '9', '3', '9', '4', '8', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk000Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['8', '4', '3', '9', '6', '1', '3', '1', '2', '6', '8', '6', '5', '8', '0', '5', '9', '3', '0', '3']), .str (String.ofList ['1', '7', '7', '2', '1', '0', '5', '4', '6', '5', '2', '9', '5', '2', '1', '5', '6', '1', '2', '5', '4']), .str (String.ofList ['1', '8', '7', '5', '4', '6', '0', '3', '5', '0', '5', '0', '2', '0', '9', '1', '1', '8', '3', '8', '5']), .str (String.ofList ['3', '8', '1', '0', '8', '9', '9', '1', '6', '6', '9', '8', '9', '0', '6', '2', '5', '0', '4', '7']), .str (String.ofList ['1', '3', '9', '4', '4', '1', '9', '8', '2', '0', '0', '8', '3', '2', '0', '4', '6', '2', '7', '3', '8']), .str (String.ofList ['9', '2', '0', '9', '4', '5', '8', '8', '3', '9', '2', '8', '8', '5', '5', '8', '2', '9', '3', '4']), .str (String.ofList ['9', '7', '9', '9', '7', '2', '4', '0', '4', '7', '4', '5', '5', '2', '3', '3', '4', '7', '3', '6']), .str (String.ofList ['9', '3', '9', '9', '1', '9', '1', '8', '9', '2', '4', '9', '7', '4', '4', '6', '5', '9', '6', '1']), .str (String.ofList ['1', '0', '9', '4', '0', '0', '9', '1', '9', '3', '2', '1', '4', '3', '5', '7', '5', '6', '2', '9', '1']), .str (String.ofList ['2', '4', '5', '9', '6', '7', '7', '6', '1', '6', '3', '6', '9', '8', '1', '1', '1', '0', '9', '6'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '6', '7', '8', '4', '4', '3', '7', '5', '9', '9', '8', '5'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '6', '8', '4', '2', '1', '7', '9', '3', '9', '4', '8', '5']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_000_before_generic"
  err.flush

theorem array_moment_records_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 150)
      (SourceJson.white (momentRecordsChunk000Chars ++ tail)) acc =
      SourceJson.array (fuel + 149) (SourceJson.white tail) (momentRecordsChunk000Push acc) := by rfl

noncomputable def momentRecordsAcc001 : List SourceJson := momentRecordsChunk000Push momentRecordsAcc000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_000_generic_complete"
  err.flush

noncomputable def momentRecordsChunk001Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '0', '4', '7', '6', '5', '3', '9', '9', '0', '3', '1', '2', '6', '2', '9', '9', '1', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '3', '4', '1', '0', '3', '7', '0', '7', '2', '8', '2', '7', '8', '5', '1', '5', '7', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '1', '5', '9', '3', '1', '4', '9', '1', '0', '2', '2', '2', '6', '4', '5', '8', '9', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '7', '5', '6', '3', '9', '6', '5', '1', '7', '7', '3', '0', '7', '0', '6', '2', '0', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '5', '3', '5', '6', '0', '5', '3', '9', '5', '8', '5', '8', '7', '2', '2', '8', '2', '4', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '7', '5', '5', '9', '3', '8', '0', '1', '3', '6', '1', '0', '5', '7', '1', '9', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '3', '7', '3', '0', '9', '4', '4', '2', '4', '0', '2', '1', '6', '8', '4', '9', '6', '5', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '1', '8', '8', '7', '2', '5', '2', '2', '0', '1', '5', '6', '3', '6', '5', '5', '5', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '0', '9', '0', '1', '8', '9', '5', '8', '2', '0', '0', '6', '0', '8', '4', '7', '0', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '0', '8', '2', '8', '7', '9', '3', '8', '2', '7', '2', '4', '9', '6', '3', '1', '1', '2', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '1', '1', '0', '1', '0', '1', '4', '1', '4', '5', '3', '9', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '1', '2', '1', '2', '1', '6', '2', '4', '3', '7', '2', '8', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk001Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['9', '2', '0', '4', '7', '6', '5', '3', '9', '9', '0', '3', '1', '2', '6', '2', '9', '9', '1', '0']), .str (String.ofList ['1', '7', '8', '3', '4', '1', '0', '3', '7', '0', '7', '2', '8', '2', '7', '8', '5', '1', '5', '7', '6']), .str (String.ofList ['1', '9', '1', '5', '9', '3', '1', '4', '9', '1', '0', '2', '2', '2', '6', '4', '5', '8', '9', '7', '5']), .str (String.ofList ['1', '4', '5', '7', '5', '6', '3', '9', '6', '5', '1', '7', '7', '3', '0', '7', '0', '6', '2', '0', '2']), .str (String.ofList ['2', '3', '5', '3', '5', '6', '0', '5', '3', '9', '5', '8', '5', '8', '7', '2', '2', '8', '2', '4', '0']), .str (String.ofList ['1', '1', '8', '7', '5', '5', '9', '3', '8', '0', '1', '3', '6', '1', '0', '5', '7', '1', '9', '3', '4']), .str (String.ofList ['1', '2', '3', '7', '3', '0', '9', '4', '4', '2', '4', '0', '2', '1', '6', '8', '4', '9', '6', '5', '8']), .str (String.ofList ['1', '2', '4', '1', '8', '8', '7', '2', '5', '2', '2', '0', '1', '5', '6', '3', '6', '5', '5', '5', '1']), .str (String.ofList ['1', '4', '5', '0', '9', '0', '1', '8', '9', '5', '8', '2', '0', '0', '6', '0', '8', '4', '7', '0', '6']), .str (String.ofList ['3', '0', '0', '8', '2', '8', '7', '9', '3', '8', '2', '7', '2', '4', '9', '6', '3', '1', '1', '2', '4'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '1', '1', '0', '1', '0', '1', '4', '1', '4', '5', '3', '9', '3'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '1', '2', '1', '2', '1', '6', '2', '4', '3', '7', '2', '8', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_001_before_generic"
  err.flush

theorem array_moment_records_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 149)
      (SourceJson.white (momentRecordsChunk001Chars ++ tail)) acc =
      SourceJson.array (fuel + 148) (SourceJson.white tail) (momentRecordsChunk001Push acc) := by rfl

noncomputable def momentRecordsAcc002 : List SourceJson := momentRecordsChunk001Push momentRecordsAcc001

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_001_generic_complete"
  err.flush

noncomputable def momentRecordsChunk002Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '5', '4', '2', '8', '0', '1', '0', '1', '5', '5', '6', '7', '5', '7', '9', '1', '1', '3', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '9', '9', '3', '9', '6', '1', '2', '9', '8', '4', '3', '1', '1', '8', '7', '1', '0', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '4', '8', '1', '8', '2', '9', '8', '4', '8', '9', '7', '7', '3', '0', '6', '0', '7', '0', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '2', '6', '6', '1', '0', '0', '7', '6', '9', '6', '5', '4', '7', '7', '9', '1', '9', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '3', '2', '0', '5', '6', '5', '6', '4', '4', '2', '2', '2', '5', '4', '7', '3', '5', '8', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '2', '4', '7', '6', '7', '5', '4', '4', '7', '7', '4', '6', '4', '8', '3', '6', '4', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '0', '9', '2', '3', '0', '7', '8', '9', '1', '5', '8', '4', '3', '2', '4', '4', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '6', '2', '6', '0', '9', '4', '5', '1', '2', '9', '8', '3', '4', '2', '4', '9', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '0', '0', '2', '3', '5', '3', '5', '8', '7', '0', '5', '5', '2', '8', '1', '7', '0', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '2', '2', '3', '7', '7', '7', '9', '9', '3', '5', '5', '7', '3', '7', '2', '0', '0', '7', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '3', '9', '1', '8', '7', '3', '9', '4', '2', '1', '7', '0', '4', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '4', '0', '6', '6', '1', '7', '5', '8', '9', '3', '9', '5', '6', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk002Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['2'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '6', '5', '4', '2', '8', '0', '1', '0', '1', '5', '5', '6', '7', '5', '7', '9', '1', '1', '3', '2']), .str (String.ofList ['2', '5', '9', '9', '3', '9', '6', '1', '2', '9', '8', '4', '3', '1', '1', '8', '7', '1', '0', '8', '3']), .str (String.ofList ['1', '8', '4', '8', '1', '8', '2', '9', '8', '4', '8', '9', '7', '7', '3', '0', '6', '0', '7', '0', '7']), .str (String.ofList ['2', '0', '4', '2', '6', '6', '1', '0', '0', '7', '6', '9', '6', '5', '4', '7', '7', '9', '1', '9', '1']), .str (String.ofList ['2', '8', '3', '2', '0', '5', '6', '5', '6', '4', '4', '2', '2', '2', '5', '4', '7', '3', '5', '8', '5']), .str (String.ofList ['1', '6', '2', '4', '7', '6', '7', '5', '4', '4', '7', '7', '4', '6', '4', '8', '3', '6', '4', '8', '6']), .str (String.ofList ['1', '4', '2', '0', '9', '2', '3', '0', '7', '8', '9', '1', '5', '8', '4', '3', '2', '4', '4', '6', '1']), .str (String.ofList ['1', '3', '9', '6', '2', '6', '0', '9', '4', '5', '1', '2', '9', '8', '3', '4', '2', '4', '9', '2', '1']), .str (String.ofList ['1', '5', '8', '0', '0', '2', '3', '5', '3', '5', '8', '7', '0', '5', '5', '2', '8', '1', '7', '0', '9']), .str (String.ofList ['3', '2', '2', '2', '3', '7', '7', '7', '9', '9', '3', '5', '5', '7', '3', '7', '2', '0', '0', '7', '8'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '3', '9', '1', '8', '7', '3', '9', '4', '2', '1', '7', '0', '4', '2'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['8', '4', '0', '6', '6', '1', '7', '5', '8', '9', '3', '9', '5', '6', '1']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_002_before_generic"
  err.flush

theorem array_moment_records_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 148)
      (SourceJson.white (momentRecordsChunk002Chars ++ tail)) acc =
      SourceJson.array (fuel + 147) (SourceJson.white tail) (momentRecordsChunk002Push acc) := by rfl

noncomputable def momentRecordsAcc003 : List SourceJson := momentRecordsChunk002Push momentRecordsAcc002

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_002_generic_complete"
  err.flush

noncomputable def momentRecordsChunk003Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '7', '8', '5', '6', '1', '9', '8', '4', '8', '6', '0', '8', '9', '5', '7', '0', '8', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '3', '3', '0', '6', '6', '4', '6', '7', '4', '3', '8', '9', '1', '8', '5', '1', '3', '2', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '2', '7', '0', '5', '9', '6', '4', '5', '8', '5', '4', '6', '0', '0', '8', '4', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '6', '8', '5', '3', '3', '4', '6', '9', '4', '1', '4', '9', '5', '2', '7', '5', '8', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '7', '2', '1', '7', '4', '1', '7', '1', '7', '2', '2', '2', '5', '1', '1', '2', '5', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '6', '3', '0', '7', '1', '2', '3', '5', '3', '3', '0', '6', '8', '6', '2', '4', '6', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '2', '0', '8', '7', '3', '9', '3', '0', '1', '2', '6', '0', '4', '7', '4', '8', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '2', '4', '9', '6', '1', '6', '3', '2', '4', '7', '1', '6', '9', '9', '6', '4', '3', '8', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '2', '5', '0', '5', '4', '9', '0', '5', '3', '4', '3', '6', '7', '4', '1', '2', '6', '8', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '6', '3', '1', '8', '9', '6', '5', '8', '8', '1', '5', '1', '2', '4', '3', '2', '0', '9', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '9', '6', '5', '4', '0', '6', '8', '6', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '0', '1', '2', '1', '0', '0', '1', '9', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk003Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['3'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['3', '9', '7', '8', '5', '6', '1', '9', '8', '4', '8', '6', '0', '8', '9', '5', '7', '0', '8', '5', '6']), .str (String.ofList ['3', '2', '3', '3', '0', '6', '6', '4', '6', '7', '4', '3', '8', '9', '1', '8', '5', '1', '3', '2', '8']), .str (String.ofList ['1', '7', '5', '2', '7', '0', '5', '9', '6', '4', '5', '8', '5', '4', '6', '0', '0', '8', '4', '2', '5']), .str (String.ofList ['2', '4', '9', '6', '8', '5', '3', '3', '4', '6', '9', '4', '1', '4', '9', '5', '2', '7', '5', '8', '3']), .str (String.ofList ['3', '1', '7', '2', '1', '7', '4', '1', '7', '1', '7', '2', '2', '2', '5', '1', '1', '2', '5', '2', '7']), .str (String.ofList ['1', '9', '2', '6', '3', '0', '7', '1', '2', '3', '5', '3', '3', '0', '6', '8', '6', '2', '4', '6', '3']), .str (String.ofList ['1', '5', '8', '2', '0', '8', '7', '3', '9', '3', '0', '1', '2', '6', '0', '4', '7', '4', '8', '3', '6']), .str (String.ofList ['1', '5', '2', '4', '9', '6', '1', '6', '3', '2', '4', '7', '1', '6', '9', '9', '6', '4', '3', '8', '6']), .str (String.ofList ['1', '5', '2', '5', '0', '5', '4', '9', '0', '5', '3', '4', '3', '6', '7', '4', '1', '2', '6', '8', '2']), .str (String.ofList ['3', '3', '6', '3', '1', '8', '9', '6', '5', '8', '8', '1', '5', '1', '2', '4', '3', '2', '0', '9', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '2', '9', '6', '5', '4', '0', '6', '8', '6', '0', '8'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['2', '3', '0', '1', '2', '1', '0', '0', '1', '9', '6', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_003_before_generic"
  err.flush

theorem array_moment_records_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 147)
      (SourceJson.white (momentRecordsChunk003Chars ++ tail)) acc =
      SourceJson.array (fuel + 146) (SourceJson.white tail) (momentRecordsChunk003Push acc) := by rfl

noncomputable def momentRecordsAcc004 : List SourceJson := momentRecordsChunk003Push momentRecordsAcc003

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_chunk_003_generic_complete"
  err.flush

noncomputable def momentRecordsBlock000Chars : List Char := momentRecordsChunk000Chars ++ momentRecordsChunk001Chars ++ momentRecordsChunk002Chars ++ momentRecordsChunk003Chars
noncomputable def momentRecordsBlock000Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk003Push (momentRecordsChunk002Push (momentRecordsChunk001Push (momentRecordsChunk000Push (acc))))

theorem array_moment_records_block_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 150)
      (SourceJson.white (momentRecordsBlock000Chars ++ tail)) acc =
      SourceJson.array (fuel + 146) (SourceJson.white tail) (momentRecordsBlock000Push acc) := by
  have hinput : momentRecordsBlock000Chars ++ tail = momentRecordsChunk000Chars ++ (momentRecordsChunk001Chars ++ (momentRecordsChunk002Chars ++ (momentRecordsChunk003Chars ++ (tail)))) := by
    simp only [momentRecordsBlock000Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 150) (SourceJson.white (momentRecordsBlock000Chars ++ tail)) acc =
        SourceJson.array (fuel + 150) (SourceJson.white (momentRecordsChunk000Chars ++ (momentRecordsChunk001Chars ++ (momentRecordsChunk002Chars ++ (momentRecordsChunk003Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 150) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 149) (SourceJson.white (momentRecordsChunk001Chars ++ (momentRecordsChunk002Chars ++ (momentRecordsChunk003Chars ++ (tail))))) (momentRecordsChunk000Push (acc)) := array_moment_records_chunk_000 fuel (momentRecordsChunk001Chars ++ (momentRecordsChunk002Chars ++ (momentRecordsChunk003Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 148) (SourceJson.white (momentRecordsChunk002Chars ++ (momentRecordsChunk003Chars ++ (tail)))) (momentRecordsChunk001Push (momentRecordsChunk000Push (acc))) := array_moment_records_chunk_001 fuel (momentRecordsChunk002Chars ++ (momentRecordsChunk003Chars ++ (tail))) (momentRecordsChunk000Push (acc))
    _ = SourceJson.array (fuel + 147) (SourceJson.white (momentRecordsChunk003Chars ++ (tail))) (momentRecordsChunk002Push (momentRecordsChunk001Push (momentRecordsChunk000Push (acc)))) := array_moment_records_chunk_002 fuel (momentRecordsChunk003Chars ++ (tail)) (momentRecordsChunk001Push (momentRecordsChunk000Push (acc)))
    _ = SourceJson.array (fuel + 146) (SourceJson.white tail) (momentRecordsBlock000Push acc) := array_moment_records_chunk_003 fuel (tail) (momentRecordsChunk002Push (momentRecordsChunk001Push (momentRecordsChunk000Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_000_before_raw_binding"
  err.flush

theorem moment_records_block_000_prefix :
    (momentRest06 364).take 2025 = momentRecordsBlock000Chars := by rfl

theorem moment_records_block_000_split :
    momentRest06 364 = momentRecordsBlock000Chars ++ momentRest06 2389 := by
  calc
    momentRest06 364 =
        (momentRest06 364).take 2025 ++ (momentRest06 364).drop 2025 :=
      (List.take_append_drop 2025 (momentRest06 364)).symm
    _ = momentRecordsBlock000Chars ++ (momentRest06 364).drop 2025 :=
      congrArg (fun p => p ++ (momentRest06 364).drop 2025) moment_records_block_000_prefix
    _ = momentRecordsBlock000Chars ++ momentRest06 2389 :=
      congrArg (fun rest => momentRecordsBlock000Chars ++ rest) (momentRest06_drop 364 2025)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_000_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_000 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 150)
      (SourceJson.white (momentRest06 364)) acc =
      SourceJson.array (fuel + 146) (SourceJson.white (momentRest06 2389)) (momentRecordsBlock000Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 150) (SourceJson.white s) acc)
      moment_records_block_000_split).trans (array_moment_records_block_000 fuel (momentRest06 2389) acc)

theorem moment_records_through_block_000 (fuel : Nat) :
    SourceJson.array (fuel + 150)
      (SourceJson.white (momentRest06 364)) [] =
      SourceJson.array (fuel + 146) (SourceJson.white (momentRest06 2389)) momentRecordsAcc004 := by
  exact array_moment_records_original_block_000 fuel momentRecordsAcc000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 records_block_000_complete"
  err.flush

#print axioms moment_records_open_prefix
#print axioms moment_records_open_split
#print axioms value_moment_records_open
#print axioms array_moment_records_chunk_000
#print axioms array_moment_records_chunk_001
#print axioms array_moment_records_chunk_002
#print axioms array_moment_records_chunk_003
#print axioms array_moment_records_block_000
#print axioms moment_records_block_000_prefix
#print axioms moment_records_block_000_split
#print axioms array_moment_records_original_block_000
#print axioms moment_records_through_block_000

end ImbalancedChen.P2OriginalSaving19Moment06Parsing
