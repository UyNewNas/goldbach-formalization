import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00400

/-! Original active8_enumeration array block 5/20; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

def active8Chunk020Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk020Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: (acc))
def active8ArrayAcc02100 : List SourceJson := active8Chunk020Push00 active8ArrayAcc02000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_020_before"
  err.flush

theorem geometryChars00_active8_chunk_020_prefix :
    (geometryChars00.drop 10223).take 378 = active8Chunk020Chars00 := by rfl

theorem geometryChars00_active8_chunk_020_split :
    geometryChars00.drop 10223 = active8Chunk020Chars00 ++ geometryChars00.drop 10601 := by
  calc
    geometryChars00.drop 10223 =
        (geometryChars00.drop 10223).take 378 ++ (geometryChars00.drop 10223).drop 378 :=
      (List.take_append_drop 378 (geometryChars00.drop 10223)).symm
    _ = active8Chunk020Chars00 ++ (geometryChars00.drop 10223).drop 378 :=
      congrArg (fun p => p ++ (geometryChars00.drop 10223).drop 378) geometryChars00_active8_chunk_020_prefix
    _ = active8Chunk020Chars00 ++ geometryChars00.drop 10601 := by rw [List.drop_drop]

theorem array_active8_chunk_020 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 153)
      (SourceJson.white (active8Chunk020Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 151) (SourceJson.white tail)
        (active8Chunk020Push00 acc) := by rfl

theorem array_active8_original_chunk_020 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 153)
      (SourceJson.white (geometryChars00.drop 10223)) acc =
      SourceJson.array (fuel + 151)
        (SourceJson.white (geometryChars00.drop 10601)) (active8Chunk020Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 153) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_020_split).trans
    (array_active8_chunk_020 fuel (geometryChars00.drop 10601) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_020_complete"
  err.flush

def active8Chunk021Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk021Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7', '5'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc02200 : List SourceJson := active8Chunk021Push00 active8ArrayAcc02100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_021_before"
  err.flush

theorem geometryChars00_active8_chunk_021_prefix :
    (geometryChars00.drop 10601).take 448 = active8Chunk021Chars00 := by rfl

theorem geometryChars00_active8_chunk_021_split :
    geometryChars00.drop 10601 = active8Chunk021Chars00 ++ geometryChars00.drop 11049 := by
  calc
    geometryChars00.drop 10601 =
        (geometryChars00.drop 10601).take 448 ++ (geometryChars00.drop 10601).drop 448 :=
      (List.take_append_drop 448 (geometryChars00.drop 10601)).symm
    _ = active8Chunk021Chars00 ++ (geometryChars00.drop 10601).drop 448 :=
      congrArg (fun p => p ++ (geometryChars00.drop 10601).drop 448) geometryChars00_active8_chunk_021_prefix
    _ = active8Chunk021Chars00 ++ geometryChars00.drop 11049 := by rw [List.drop_drop]

theorem array_active8_chunk_021 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 151)
      (SourceJson.white (active8Chunk021Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 149) (SourceJson.white tail)
        (active8Chunk021Push00 acc) := by rfl

theorem array_active8_original_chunk_021 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 151)
      (SourceJson.white (geometryChars00.drop 10601)) acc =
      SourceJson.array (fuel + 149)
        (SourceJson.white (geometryChars00.drop 11049)) (active8Chunk021Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 151) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_021_split).trans
    (array_active8_chunk_021 fuel (geometryChars00.drop 11049) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_021_complete"
  err.flush

def active8Chunk022Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk022Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: (acc))
def active8ArrayAcc02300 : List SourceJson := active8Chunk022Push00 active8ArrayAcc02200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_022_before"
  err.flush

theorem geometryChars00_active8_chunk_022_prefix :
    (geometryChars00.drop 11049).take 448 = active8Chunk022Chars00 := by rfl

theorem geometryChars00_active8_chunk_022_split :
    geometryChars00.drop 11049 = active8Chunk022Chars00 ++ geometryChars00.drop 11497 := by
  calc
    geometryChars00.drop 11049 =
        (geometryChars00.drop 11049).take 448 ++ (geometryChars00.drop 11049).drop 448 :=
      (List.take_append_drop 448 (geometryChars00.drop 11049)).symm
    _ = active8Chunk022Chars00 ++ (geometryChars00.drop 11049).drop 448 :=
      congrArg (fun p => p ++ (geometryChars00.drop 11049).drop 448) geometryChars00_active8_chunk_022_prefix
    _ = active8Chunk022Chars00 ++ geometryChars00.drop 11497 := by rw [List.drop_drop]

theorem array_active8_chunk_022 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 149)
      (SourceJson.white (active8Chunk022Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 147) (SourceJson.white tail)
        (active8Chunk022Push00 acc) := by rfl

theorem array_active8_original_chunk_022 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 149)
      (SourceJson.white (geometryChars00.drop 11049)) acc =
      SourceJson.array (fuel + 147)
        (SourceJson.white (geometryChars00.drop 11497)) (active8Chunk022Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 149) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_022_split).trans
    (array_active8_chunk_022 fuel (geometryChars00.drop 11497) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_022_complete"
  err.flush

def active8Chunk023Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '8', '2', '0', '2', '3', '9', '/', '4', '4', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk023Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7', '5'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '8', '2', '0', '2', '3', '9', '/', '4', '4', '5', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc02400 : List SourceJson := active8Chunk023Push00 active8ArrayAcc02300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_023_before"
  err.flush

theorem geometryChars00_active8_chunk_023_prefix :
    (geometryChars00.drop 11497).take 524 = active8Chunk023Chars00 := by rfl

theorem geometryChars00_active8_chunk_023_split :
    geometryChars00.drop 11497 = active8Chunk023Chars00 ++ geometryChars00.drop 12021 := by
  calc
    geometryChars00.drop 11497 =
        (geometryChars00.drop 11497).take 524 ++ (geometryChars00.drop 11497).drop 524 :=
      (List.take_append_drop 524 (geometryChars00.drop 11497)).symm
    _ = active8Chunk023Chars00 ++ (geometryChars00.drop 11497).drop 524 :=
      congrArg (fun p => p ++ (geometryChars00.drop 11497).drop 524) geometryChars00_active8_chunk_023_prefix
    _ = active8Chunk023Chars00 ++ geometryChars00.drop 12021 := by rw [List.drop_drop]

theorem array_active8_chunk_023 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 147)
      (SourceJson.white (active8Chunk023Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 145) (SourceJson.white tail)
        (active8Chunk023Push00 acc) := by rfl

theorem array_active8_original_chunk_023 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 147)
      (SourceJson.white (geometryChars00.drop 11497)) acc =
      SourceJson.array (fuel + 145)
        (SourceJson.white (geometryChars00.drop 12021)) (active8Chunk023Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 147) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_023_split).trans
    (array_active8_chunk_023 fuel (geometryChars00.drop 12021) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_023_complete"
  err.flush

theorem active8_array_through_block_005 (fuel : Nat) :
    SourceJson.array (fuel + 193)
      (SourceJson.white (geometryChars00.drop 408)) [] =
      SourceJson.array (fuel + 145)
        (SourceJson.white (geometryChars00.drop 12021)) active8ArrayAcc02400 := by
  calc
    SourceJson.array (fuel + 193)
        (SourceJson.white (geometryChars00.drop 408)) [] =
      SourceJson.array (fuel + 153)
        (SourceJson.white (geometryChars00.drop 10223)) active8ArrayAcc02000 :=
      active8_array_through_block_004 fuel
    _ =
      SourceJson.array (fuel + 151)
        (SourceJson.white (geometryChars00.drop 10601)) active8ArrayAcc02100 :=
      array_active8_original_chunk_020 fuel active8ArrayAcc02000
    _ =
      SourceJson.array (fuel + 149)
        (SourceJson.white (geometryChars00.drop 11049)) active8ArrayAcc02200 :=
      array_active8_original_chunk_021 fuel active8ArrayAcc02100
    _ =
      SourceJson.array (fuel + 147)
        (SourceJson.white (geometryChars00.drop 11497)) active8ArrayAcc02300 :=
      array_active8_original_chunk_022 fuel active8ArrayAcc02200
    _ =
      SourceJson.array (fuel + 145)
        (SourceJson.white (geometryChars00.drop 12021)) active8ArrayAcc02400 :=
      array_active8_original_chunk_023 fuel active8ArrayAcc02300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_block_005_complete"
  err.flush

#print axioms geometryChars00_active8_chunk_020_prefix
#print axioms geometryChars00_active8_chunk_020_split
#print axioms array_active8_chunk_020
#print axioms array_active8_original_chunk_020
#print axioms geometryChars00_active8_chunk_021_prefix
#print axioms geometryChars00_active8_chunk_021_split
#print axioms array_active8_chunk_021
#print axioms array_active8_original_chunk_021
#print axioms geometryChars00_active8_chunk_022_prefix
#print axioms geometryChars00_active8_chunk_022_split
#print axioms array_active8_chunk_022
#print axioms array_active8_original_chunk_022
#print axioms geometryChars00_active8_chunk_023_prefix
#print axioms geometryChars00_active8_chunk_023_split
#print axioms array_active8_chunk_023
#print axioms array_active8_original_chunk_023
#print axioms active8_array_through_block_005

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
