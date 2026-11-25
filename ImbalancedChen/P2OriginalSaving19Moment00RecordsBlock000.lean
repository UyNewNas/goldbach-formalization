import ImbalancedChen.P2OriginalSaving19Moment00Input

/-! Original moment records block 0. Small arbitrary-tail/accumulator parser equations and one exact packed-input binding.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentRecordsOpenChars : List Char := ['[']
noncomputable def momentRecordsAcc000 : List SourceJson := []

theorem moment_records_open_prefix :
    (momentRest00 363).take 1 = momentRecordsOpenChars := by rfl

theorem moment_records_open_split :
    momentRest00 363 = momentRecordsOpenChars ++ momentRest00 364 := by
  calc
    momentRest00 363 =
        (momentRest00 363).take 1 ++ (momentRest00 363).drop 1 :=
      (List.take_append_drop 1 (momentRest00 363)).symm
    _ = momentRecordsOpenChars ++ (momentRest00 363).drop 1 :=
      congrArg (fun p => p ++ (momentRest00 363).drop 1) moment_records_open_prefix
    _ = momentRecordsOpenChars ++ momentRest00 364 :=
      congrArg (fun rest => momentRecordsOpenChars ++ rest) (momentRest00_drop 363 1)

theorem value_moment_records_open (fuel : Nat) :
    SourceJson.value (fuel + 94) (momentRest00 363) =
      SourceJson.array (fuel + 93)
        (SourceJson.white (momentRest00 364)) [] := by
  calc
    SourceJson.value (fuel + 94) (momentRest00 363) =
        SourceJson.value (fuel + 94)
          (momentRecordsOpenChars ++ momentRest00 364) :=
      congrArg (SourceJson.value (fuel + 94)) moment_records_open_split
    _ = SourceJson.array (fuel + 93)
        (SourceJson.white (momentRest00 364)) [] := by rfl

noncomputable def momentRecordsChunk000Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '3', '7', '1', '5', '0', '9', '1', '8', '1', '3', '2', '3', '1', '4', '2', '9', '1', '4', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '3', '8', '3', '6', '7', '2', '5', '0', '1', '4', '7', '2', '0', '4', '2', '9', '7', '6', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '4', '5', '1', '8', '1', '9', '8', '7', '5', '1', '9', '3', '6', '5', '3', '0', '8', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '0', '3', '8', '6', '3', '8', '3', '0', '0', '4', '9', '5', '1', '9', '0', '3', '8', '6', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '6', '8', '1', '1', '8', '7', '5', '9', '7', '5', '2', '8', '5', '0', '8', '0', '9', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '3', '6', '9', '4', '4', '5', '0', '5', '9', '2', '3', '0', '4', '8', '1', '4', '6', '6', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '2', '2', '2', '0', '9', '9', '8', '6', '8', '2', '5', '1', '1', '5', '9', '1', '7', '2', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '2', '7', '8', '3', '1', '8', '9', '8', '7', '1', '4', '1', '5', '7', '0', '1', '9', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '8', '1', '9', '5', '5', '1', '1', '6', '3', '9', '7', '6', '9', '1', '0', '4', '8', '5', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '4', '4', '0', '8', '0', '1', '5', '6', '3', '9', '5', '7', '5', '1', '9', '9', '5', '4', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '7', '0', '8', '4', '4', '9', '4', '8', '5', '9', '2', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '7', '2', '9', '5', '3', '2', '3', '5', '1', '2', '9', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk000Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['0'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['2', '2', '3', '7', '1', '5', '0', '9', '1', '8', '1', '3', '2', '3', '1', '4', '2', '9', '1', '4', '6']), .str (String.ofList ['2', '4', '3', '8', '3', '6', '7', '2', '5', '0', '1', '4', '7', '2', '0', '4', '2', '9', '7', '6', '2']), .str (String.ofList ['1', '7', '5', '4', '5', '1', '8', '1', '9', '8', '7', '5', '1', '9', '3', '6', '5', '3', '0', '8', '1']), .str (String.ofList ['5', '4', '0', '3', '8', '6', '3', '8', '3', '0', '0', '4', '9', '5', '1', '9', '0', '3', '8', '6', '1']), .str (String.ofList ['2', '0', '8', '6', '8', '1', '1', '8', '7', '5', '9', '7', '5', '2', '8', '5', '0', '8', '0', '9', '7']), .str (String.ofList ['4', '4', '3', '6', '9', '4', '4', '5', '0', '5', '9', '2', '3', '0', '4', '8', '1', '4', '6', '6', '6']), .str (String.ofList ['4', '8', '2', '2', '2', '0', '9', '9', '8', '6', '8', '2', '5', '1', '1', '5', '9', '1', '7', '2', '0']), .str (String.ofList ['5', '4', '2', '7', '8', '3', '1', '8', '9', '8', '7', '1', '4', '1', '5', '7', '0', '1', '9', '2', '9']), .str (String.ofList ['5', '0', '8', '1', '9', '5', '5', '1', '1', '6', '3', '9', '7', '6', '9', '1', '0', '4', '8', '5', '5']), .str (String.ofList ['4', '2', '4', '4', '0', '8', '0', '1', '5', '6', '3', '9', '5', '7', '5', '1', '9', '9', '5', '4', '6'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '7', '0', '8', '4', '4', '9', '4', '8', '5', '9', '2', '1'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '7', '2', '9', '5', '3', '2', '3', '5', '1', '2', '9', '7']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_000_before_generic"
  err.flush

theorem array_moment_records_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRecordsChunk000Chars ++ tail)) acc =
      SourceJson.array (fuel + 92) (SourceJson.white tail) (momentRecordsChunk000Push acc) := by rfl

noncomputable def momentRecordsAcc001 : List SourceJson := momentRecordsChunk000Push momentRecordsAcc000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_000_generic_complete"
  err.flush

noncomputable def momentRecordsChunk001Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '4', '5', '9', '7', '2', '5', '6', '9', '7', '9', '5', '7', '9', '9', '8', '6', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '9', '1', '5', '5', '1', '6', '7', '7', '3', '6', '7', '2', '8', '1', '9', '2', '9', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '2', '9', '3', '7', '0', '5', '9', '6', '5', '2', '9', '7', '8', '9', '3', '7', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '1', '3', '3', '2', '7', '9', '0', '2', '1', '2', '7', '3', '2', '9', '1', '8', '0', '4', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '8', '4', '9', '9', '7', '1', '5', '8', '3', '4', '6', '6', '5', '0', '1', '3', '4', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '4', '5', '1', '6', '4', '8', '3', '8', '6', '8', '8', '3', '0', '1', '8', '2', '3', '2', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '0', '2', '7', '2', '3', '6', '6', '9', '6', '8', '6', '6', '1', '6', '6', '0', '3', '3', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '1', '6', '1', '8', '7', '5', '3', '5', '4', '2', '5', '1', '2', '9', '4', '0', '6', '9', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '2', '4', '9', '8', '0', '7', '6', '9', '0', '8', '3', '6', '7', '0', '3', '8', '1', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '2', '4', '9', '2', '2', '8', '6', '3', '7', '2', '1', '1', '8', '0', '1', '0', '3', '3', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '6', '0', '8', '7', '8', '3', '0', '1', '9', '6', '6', '5', '5', '9', '8', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '6', '2', '5', '4', '9', '3', '6', '9', '1', '9', '8', '8', '1', '6', '8', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk001Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '7', '8', '4', '5', '9', '7', '2', '5', '6', '9', '7', '9', '5', '7', '9', '9', '8', '6', '2', '7']), .str (String.ofList ['2', '0', '9', '1', '5', '5', '1', '6', '7', '7', '3', '6', '7', '2', '8', '1', '9', '2', '9', '7', '0']), .str (String.ofList ['1', '6', '9', '2', '9', '3', '7', '0', '5', '9', '6', '5', '2', '9', '7', '8', '9', '3', '7', '0', '0']), .str (String.ofList ['4', '8', '1', '3', '3', '2', '7', '9', '0', '2', '1', '2', '7', '3', '2', '9', '1', '8', '0', '4', '9']), .str (String.ofList ['2', '0', '6', '8', '4', '9', '9', '7', '1', '5', '8', '3', '4', '6', '6', '5', '0', '1', '3', '4', '3']), .str (String.ofList ['4', '0', '4', '5', '1', '6', '4', '8', '3', '8', '6', '8', '8', '3', '0', '1', '8', '2', '3', '2', '7']), .str (String.ofList ['4', '7', '0', '2', '7', '2', '3', '6', '6', '9', '6', '8', '6', '6', '1', '6', '6', '0', '3', '3', '4']), .str (String.ofList ['5', '4', '1', '6', '1', '8', '7', '5', '3', '5', '4', '2', '5', '1', '2', '9', '4', '0', '6', '9', '8']), .str (String.ofList ['5', '2', '2', '4', '9', '8', '0', '7', '6', '9', '0', '8', '3', '6', '7', '0', '3', '8', '1', '9', '6']), .str (String.ofList ['4', '1', '2', '4', '9', '2', '2', '8', '6', '3', '7', '2', '1', '1', '8', '0', '1', '0', '3', '3', '6'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '6', '0', '8', '7', '8', '3', '0', '1', '9', '6', '6', '5', '5', '9', '8', '7'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['5', '6', '2', '5', '4', '9', '3', '6', '9', '1', '9', '8', '8', '1', '6', '8', '0']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_001_before_generic"
  err.flush

theorem array_moment_records_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 92)
      (SourceJson.white (momentRecordsChunk001Chars ++ tail)) acc =
      SourceJson.array (fuel + 91) (SourceJson.white tail) (momentRecordsChunk001Push acc) := by rfl

noncomputable def momentRecordsAcc002 : List SourceJson := momentRecordsChunk001Push momentRecordsAcc001

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_001_generic_complete"
  err.flush

noncomputable def momentRecordsChunk002Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '8', '0', '1', '5', '6', '1', '5', '2', '1', '7', '1', '5', '1', '6', '6', '8', '3', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '2', '0', '0', '1', '7', '8', '1', '0', '3', '9', '5', '4', '7', '6', '2', '4', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '7', '4', '2', '2', '6', '6', '2', '9', '7', '7', '5', '7', '2', '5', '6', '0', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '1', '0', '5', '4', '3', '5', '1', '2', '2', '0', '8', '5', '4', '0', '1', '0', '7', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '0', '1', '6', '2', '6', '4', '6', '1', '9', '3', '1', '0', '2', '4', '5', '7', '4', '3', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '4', '6', '1', '0', '6', '4', '5', '7', '7', '3', '6', '7', '4', '3', '0', '7', '3', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '5', '7', '8', '7', '6', '1', '9', '6', '3', '0', '9', '8', '9', '7', '5', '9', '9', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '9', '5', '4', '2', '6', '2', '8', '4', '6', '6', '7', '4', '9', '1', '7', '7', '4', '2', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '4', '9', '6', '8', '0', '3', '8', '7', '6', '7', '4', '8', '9', '5', '8', '4', '8', '4', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '2', '9', '5', '1', '1', '3', '8', '9', '0', '7', '4', '7', '2', '1', '0', '1', '4', '6', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '3', '4', '9', '7', '0', '0', '1', '3', '9', '2', '3', '4', '3', '7', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '3', '6', '8', '8', '2', '5', '4', '8', '4', '9', '9', '5', '3', '0', '0', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk002Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['2'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '7', '5', '8', '0', '1', '5', '6', '1', '5', '2', '1', '7', '1', '5', '1', '6', '6', '8', '3', '5']), .str (String.ofList ['1', '9', '2', '2', '0', '0', '1', '7', '8', '1', '0', '3', '9', '5', '4', '7', '6', '2', '4', '7', '2']), .str (String.ofList ['1', '6', '8', '7', '4', '2', '2', '6', '6', '2', '9', '7', '7', '5', '7', '2', '5', '6', '0', '2', '2']), .str (String.ofList ['5', '0', '1', '0', '5', '4', '3', '5', '1', '2', '2', '0', '8', '5', '4', '0', '1', '0', '7', '4', '8']), .str (String.ofList ['2', '1', '0', '1', '6', '2', '6', '4', '6', '1', '9', '3', '1', '0', '2', '4', '5', '7', '4', '3', '2']), .str (String.ofList ['4', '0', '4', '6', '1', '0', '6', '4', '5', '7', '7', '3', '6', '7', '4', '3', '0', '7', '3', '3', '6']), .str (String.ofList ['4', '6', '5', '7', '8', '7', '6', '1', '9', '6', '3', '0', '9', '8', '9', '7', '5', '9', '9', '4', '8']), .str (String.ofList ['5', '5', '9', '5', '4', '2', '6', '2', '8', '4', '6', '6', '7', '4', '9', '1', '7', '7', '4', '2', '2']), .str (String.ofList ['5', '4', '4', '9', '6', '8', '0', '3', '8', '7', '6', '7', '4', '8', '9', '5', '8', '4', '8', '4', '1']), .str (String.ofList ['4', '1', '2', '9', '5', '1', '1', '3', '8', '9', '0', '7', '4', '7', '2', '1', '0', '1', '4', '6', '1'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '3', '4', '9', '7', '0', '0', '1', '3', '9', '2', '3', '4', '3', '7', '6', '4'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '3', '6', '8', '8', '2', '5', '4', '8', '4', '9', '9', '5', '3', '0', '0', '9']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_002_before_generic"
  err.flush

theorem array_moment_records_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 91)
      (SourceJson.white (momentRecordsChunk002Chars ++ tail)) acc =
      SourceJson.array (fuel + 90) (SourceJson.white tail) (momentRecordsChunk002Push acc) := by rfl

noncomputable def momentRecordsAcc003 : List SourceJson := momentRecordsChunk002Push momentRecordsAcc002

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_002_generic_complete"
  err.flush

noncomputable def momentRecordsChunk003Chars : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '9', '7', '7', '8', '0', '1', '1', '3', '3', '7', '0', '8', '8', '8', '7', '6', '2', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '4', '1', '3', '8', '5', '8', '7', '5', '9', '0', '0', '7', '0', '6', '5', '7', '2', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '7', '7', '4', '8', '5', '6', '0', '1', '2', '6', '4', '4', '7', '0', '6', '0', '0', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '2', '8', '2', '4', '1', '1', '6', '9', '1', '1', '3', '6', '1', '2', '0', '8', '1', '5', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '8', '3', '5', '9', '6', '9', '2', '6', '4', '1', '6', '3', '5', '9', '1', '6', '5', '6', '7', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '9', '0', '3', '9', '7', '8', '5', '7', '9', '2', '1', '2', '2', '0', '5', '5', '0', '7', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '1', '8', '5', '8', '8', '9', '1', '7', '7', '9', '3', '8', '0', '9', '7', '5', '8', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '6', '5', '5', '2', '7', '9', '6', '6', '7', '8', '7', '1', '1', '9', '6', '4', '0', '9', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '5', '1', '0', '6', '8', '4', '0', '4', '8', '6', '3', '9', '4', '3', '5', '5', '8', '3', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '9', '4', '1', '5', '8', '9', '8', '3', '8', '5', '8', '9', '6', '1', '3', '6', '1', '2', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '5', '9', '3', '9', '1', '6', '8', '9', '2', '5', '5', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '1', '6', '1', '3', '1', '9', '2', '7', '4', '8', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def momentRecordsChunk003Push (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['3'])), (String.ofList ['l', 'o', 'g', '_', 'g', 'a', 'p', '_', 'f', 'a', 'c', 't', 'o', 'r', '_', 'f', 'l', 'o', 'o', 'r', 's', '_', 'Q', '8', '0'], .arr [.str (String.ofList ['1', '9', '0', '9', '7', '7', '8', '0', '1', '1', '3', '3', '7', '0', '8', '8', '8', '7', '6', '2', '9']), .str (String.ofList ['2', '2', '4', '1', '3', '8', '5', '8', '7', '5', '9', '0', '0', '7', '0', '6', '5', '7', '2', '5', '9']), .str (String.ofList ['1', '6', '7', '7', '7', '4', '8', '5', '6', '0', '1', '2', '6', '4', '4', '7', '0', '6', '0', '0', '8']), .str (String.ofList ['5', '7', '2', '8', '2', '4', '1', '1', '6', '9', '1', '1', '3', '6', '1', '2', '0', '8', '1', '5', '6']), .str (String.ofList ['2', '1', '8', '3', '5', '9', '6', '9', '2', '6', '4', '1', '6', '3', '5', '9', '1', '6', '5', '6', '7']), .str (String.ofList ['4', '1', '9', '0', '3', '9', '7', '8', '5', '7', '9', '2', '1', '2', '2', '0', '5', '5', '0', '7', '0']), .str (String.ofList ['4', '7', '1', '8', '5', '8', '8', '9', '1', '7', '7', '9', '3', '8', '0', '9', '7', '5', '8', '4', '8']), .str (String.ofList ['6', '0', '6', '5', '5', '2', '7', '9', '6', '6', '7', '8', '7', '1', '1', '9', '6', '4', '0', '9', '6']), .str (String.ofList ['6', '1', '5', '1', '0', '6', '8', '4', '0', '4', '8', '6', '3', '9', '4', '3', '5', '5', '8', '3', '3']), .str (String.ofList ['5', '7', '9', '4', '1', '5', '8', '9', '8', '3', '8', '5', '8', '9', '6', '1', '3', '6', '1', '2', '7'])]), (String.ofList ['o', 'l', 'd', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '5', '9', '3', '9', '1', '6', '8', '9', '2', '5', '5', '9'])), (String.ofList ['n', 'e', 'w', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6'], .str (String.ofList ['6', '6', '1', '6', '1', '3', '1', '9', '2', '7', '4', '8', '4']))]) :: (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_003_before_generic"
  err.flush

theorem array_moment_records_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 90)
      (SourceJson.white (momentRecordsChunk003Chars ++ tail)) acc =
      SourceJson.array (fuel + 89) (SourceJson.white tail) (momentRecordsChunk003Push acc) := by rfl

noncomputable def momentRecordsAcc004 : List SourceJson := momentRecordsChunk003Push momentRecordsAcc003

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_chunk_003_generic_complete"
  err.flush

noncomputable def momentRecordsBlock000Chars : List Char := momentRecordsChunk000Chars ++ momentRecordsChunk001Chars ++ momentRecordsChunk002Chars ++ momentRecordsChunk003Chars
noncomputable def momentRecordsBlock000Push (acc : List SourceJson) : List SourceJson := momentRecordsChunk003Push (momentRecordsChunk002Push (momentRecordsChunk001Push (momentRecordsChunk000Push (acc))))

theorem array_moment_records_block_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRecordsBlock000Chars ++ tail)) acc =
      SourceJson.array (fuel + 89) (SourceJson.white tail) (momentRecordsBlock000Push acc) := by
  have hinput : momentRecordsBlock000Chars ++ tail = momentRecordsChunk000Chars ++ (momentRecordsChunk001Chars ++ (momentRecordsChunk002Chars ++ (momentRecordsChunk003Chars ++ (tail)))) := by
    simp only [momentRecordsBlock000Chars, List.append_assoc]
  calc
    SourceJson.array (fuel + 93) (SourceJson.white (momentRecordsBlock000Chars ++ tail)) acc =
        SourceJson.array (fuel + 93) (SourceJson.white (momentRecordsChunk000Chars ++ (momentRecordsChunk001Chars ++ (momentRecordsChunk002Chars ++ (momentRecordsChunk003Chars ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 93) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 92) (SourceJson.white (momentRecordsChunk001Chars ++ (momentRecordsChunk002Chars ++ (momentRecordsChunk003Chars ++ (tail))))) (momentRecordsChunk000Push (acc)) := array_moment_records_chunk_000 fuel (momentRecordsChunk001Chars ++ (momentRecordsChunk002Chars ++ (momentRecordsChunk003Chars ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 91) (SourceJson.white (momentRecordsChunk002Chars ++ (momentRecordsChunk003Chars ++ (tail)))) (momentRecordsChunk001Push (momentRecordsChunk000Push (acc))) := array_moment_records_chunk_001 fuel (momentRecordsChunk002Chars ++ (momentRecordsChunk003Chars ++ (tail))) (momentRecordsChunk000Push (acc))
    _ = SourceJson.array (fuel + 90) (SourceJson.white (momentRecordsChunk003Chars ++ (tail))) (momentRecordsChunk002Push (momentRecordsChunk001Push (momentRecordsChunk000Push (acc)))) := array_moment_records_chunk_002 fuel (momentRecordsChunk003Chars ++ (tail)) (momentRecordsChunk001Push (momentRecordsChunk000Push (acc)))
    _ = SourceJson.array (fuel + 89) (SourceJson.white tail) (momentRecordsBlock000Push acc) := array_moment_records_chunk_003 fuel (tail) (momentRecordsChunk002Push (momentRecordsChunk001Push (momentRecordsChunk000Push (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_block_000_before_raw_binding"
  err.flush

theorem moment_records_block_000_prefix :
    (momentRest00 364).take 2044 = momentRecordsBlock000Chars := by rfl

theorem moment_records_block_000_split :
    momentRest00 364 = momentRecordsBlock000Chars ++ momentRest00 2408 := by
  calc
    momentRest00 364 =
        (momentRest00 364).take 2044 ++ (momentRest00 364).drop 2044 :=
      (List.take_append_drop 2044 (momentRest00 364)).symm
    _ = momentRecordsBlock000Chars ++ (momentRest00 364).drop 2044 :=
      congrArg (fun p => p ++ (momentRest00 364).drop 2044) moment_records_block_000_prefix
    _ = momentRecordsBlock000Chars ++ momentRest00 2408 :=
      congrArg (fun rest => momentRecordsBlock000Chars ++ rest) (momentRest00_drop 364 2044)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_block_000_after_raw_binding"
  err.flush

theorem array_moment_records_original_block_000 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRest00 364)) acc =
      SourceJson.array (fuel + 89) (SourceJson.white (momentRest00 2408)) (momentRecordsBlock000Push acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 93) (SourceJson.white s) acc)
      moment_records_block_000_split).trans (array_moment_records_block_000 fuel (momentRest00 2408) acc)

theorem moment_records_through_block_000 (fuel : Nat) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (momentRest00 364)) [] =
      SourceJson.array (fuel + 89) (SourceJson.white (momentRest00 2408)) momentRecordsAcc004 := by
  exact array_moment_records_original_block_000 fuel momentRecordsAcc000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 records_block_000_complete"
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

end ImbalancedChen.P2OriginalSaving19Moment00Parsing
