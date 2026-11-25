import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00000

/-! Original active8_enumeration array block 1/20; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

def active8Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7', '5'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc00500 : List SourceJson := active8Chunk004Push00 active8ArrayAcc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_004_before"
  err.flush

theorem geometryChars00_active8_chunk_004_prefix :
    (geometryChars00.drop 2214).take 448 = active8Chunk004Chars00 := by rfl

theorem geometryChars00_active8_chunk_004_split :
    geometryChars00.drop 2214 = active8Chunk004Chars00 ++ geometryChars00.drop 2662 := by
  calc
    geometryChars00.drop 2214 =
        (geometryChars00.drop 2214).take 448 ++ (geometryChars00.drop 2214).drop 448 :=
      (List.take_append_drop 448 (geometryChars00.drop 2214)).symm
    _ = active8Chunk004Chars00 ++ (geometryChars00.drop 2214).drop 448 :=
      congrArg (fun p => p ++ (geometryChars00.drop 2214).drop 448) geometryChars00_active8_chunk_004_prefix
    _ = active8Chunk004Chars00 ++ geometryChars00.drop 2662 := by rw [List.drop_drop]

theorem array_active8_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 185)
      (SourceJson.white (active8Chunk004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 183) (SourceJson.white tail)
        (active8Chunk004Push00 acc) := by rfl

theorem array_active8_original_chunk_004 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 185)
      (SourceJson.white (geometryChars00.drop 2214)) acc =
      SourceJson.array (fuel + 183)
        (SourceJson.white (geometryChars00.drop 2662)) (active8Chunk004Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 185) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_004_split).trans
    (array_active8_chunk_004 fuel (geometryChars00.drop 2662) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_004_complete"
  err.flush

def active8Chunk005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '2', '4', '2', '0', '3', '3', '/', '2', '3', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk005Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7', '5'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '2', '4', '2', '0', '3', '3', '/', '2', '3', '5', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc00600 : List SourceJson := active8Chunk005Push00 active8ArrayAcc00500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_005_before"
  err.flush

theorem geometryChars00_active8_chunk_005_prefix :
    (geometryChars00.drop 2662).take 455 = active8Chunk005Chars00 := by rfl

theorem geometryChars00_active8_chunk_005_split :
    geometryChars00.drop 2662 = active8Chunk005Chars00 ++ geometryChars00.drop 3117 := by
  calc
    geometryChars00.drop 2662 =
        (geometryChars00.drop 2662).take 455 ++ (geometryChars00.drop 2662).drop 455 :=
      (List.take_append_drop 455 (geometryChars00.drop 2662)).symm
    _ = active8Chunk005Chars00 ++ (geometryChars00.drop 2662).drop 455 :=
      congrArg (fun p => p ++ (geometryChars00.drop 2662).drop 455) geometryChars00_active8_chunk_005_prefix
    _ = active8Chunk005Chars00 ++ geometryChars00.drop 3117 := by rw [List.drop_drop]

theorem array_active8_chunk_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 183)
      (SourceJson.white (active8Chunk005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 181) (SourceJson.white tail)
        (active8Chunk005Push00 acc) := by rfl

theorem array_active8_original_chunk_005 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 183)
      (SourceJson.white (geometryChars00.drop 2662)) acc =
      SourceJson.array (fuel + 181)
        (SourceJson.white (geometryChars00.drop 3117)) (active8Chunk005Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 183) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_005_split).trans
    (array_active8_chunk_005 fuel (geometryChars00.drop 3117) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_005_complete"
  err.flush

def active8Chunk006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '9', '9', '9', '8', '5', '7', '/', '4', '7', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk006Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['6', '1'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '9', '9', '9', '8', '5', '7', '/', '4', '7', '0', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc00700 : List SourceJson := active8Chunk006Push00 active8ArrayAcc00600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_006_before"
  err.flush

theorem geometryChars00_active8_chunk_006_prefix :
    (geometryChars00.drop 3117).take 524 = active8Chunk006Chars00 := by rfl

theorem geometryChars00_active8_chunk_006_split :
    geometryChars00.drop 3117 = active8Chunk006Chars00 ++ geometryChars00.drop 3641 := by
  calc
    geometryChars00.drop 3117 =
        (geometryChars00.drop 3117).take 524 ++ (geometryChars00.drop 3117).drop 524 :=
      (List.take_append_drop 524 (geometryChars00.drop 3117)).symm
    _ = active8Chunk006Chars00 ++ (geometryChars00.drop 3117).drop 524 :=
      congrArg (fun p => p ++ (geometryChars00.drop 3117).drop 524) geometryChars00_active8_chunk_006_prefix
    _ = active8Chunk006Chars00 ++ geometryChars00.drop 3641 := by rw [List.drop_drop]

theorem array_active8_chunk_006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (active8Chunk006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 179) (SourceJson.white tail)
        (active8Chunk006Push00 acc) := by rfl

theorem array_active8_original_chunk_006 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 181)
      (SourceJson.white (geometryChars00.drop 3117)) acc =
      SourceJson.array (fuel + 179)
        (SourceJson.white (geometryChars00.drop 3641)) (active8Chunk006Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 181) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_006_split).trans
    (array_active8_chunk_006 fuel (geometryChars00.drop 3641) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_006_complete"
  err.flush

def active8Chunk007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '2', '4', '9', '9', '/', '8', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk007Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['6', '1']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7', '5'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '2', '4', '9', '9', '/', '8', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc00800 : List SourceJson := active8Chunk007Push00 active8ArrayAcc00700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_007_before"
  err.flush

theorem geometryChars00_active8_chunk_007_prefix :
    (geometryChars00.drop 3641).take 521 = active8Chunk007Chars00 := by rfl

theorem geometryChars00_active8_chunk_007_split :
    geometryChars00.drop 3641 = active8Chunk007Chars00 ++ geometryChars00.drop 4162 := by
  calc
    geometryChars00.drop 3641 =
        (geometryChars00.drop 3641).take 521 ++ (geometryChars00.drop 3641).drop 521 :=
      (List.take_append_drop 521 (geometryChars00.drop 3641)).symm
    _ = active8Chunk007Chars00 ++ (geometryChars00.drop 3641).drop 521 :=
      congrArg (fun p => p ++ (geometryChars00.drop 3641).drop 521) geometryChars00_active8_chunk_007_prefix
    _ = active8Chunk007Chars00 ++ geometryChars00.drop 4162 := by rw [List.drop_drop]

theorem array_active8_chunk_007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 179)
      (SourceJson.white (active8Chunk007Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 177) (SourceJson.white tail)
        (active8Chunk007Push00 acc) := by rfl

theorem array_active8_original_chunk_007 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 179)
      (SourceJson.white (geometryChars00.drop 3641)) acc =
      SourceJson.array (fuel + 177)
        (SourceJson.white (geometryChars00.drop 4162)) (active8Chunk007Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 179) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_007_split).trans
    (array_active8_chunk_007 fuel (geometryChars00.drop 4162) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_007_complete"
  err.flush

theorem active8_array_through_block_001 (fuel : Nat) :
    SourceJson.array (fuel + 193)
      (SourceJson.white (geometryChars00.drop 408)) [] =
      SourceJson.array (fuel + 177)
        (SourceJson.white (geometryChars00.drop 4162)) active8ArrayAcc00800 := by
  calc
    SourceJson.array (fuel + 193)
        (SourceJson.white (geometryChars00.drop 408)) [] =
      SourceJson.array (fuel + 185)
        (SourceJson.white (geometryChars00.drop 2214)) active8ArrayAcc00400 :=
      active8_array_through_block_000 fuel
    _ =
      SourceJson.array (fuel + 183)
        (SourceJson.white (geometryChars00.drop 2662)) active8ArrayAcc00500 :=
      array_active8_original_chunk_004 fuel active8ArrayAcc00400
    _ =
      SourceJson.array (fuel + 181)
        (SourceJson.white (geometryChars00.drop 3117)) active8ArrayAcc00600 :=
      array_active8_original_chunk_005 fuel active8ArrayAcc00500
    _ =
      SourceJson.array (fuel + 179)
        (SourceJson.white (geometryChars00.drop 3641)) active8ArrayAcc00700 :=
      array_active8_original_chunk_006 fuel active8ArrayAcc00600
    _ =
      SourceJson.array (fuel + 177)
        (SourceJson.white (geometryChars00.drop 4162)) active8ArrayAcc00800 :=
      array_active8_original_chunk_007 fuel active8ArrayAcc00700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_block_001_complete"
  err.flush

#print axioms geometryChars00_active8_chunk_004_prefix
#print axioms geometryChars00_active8_chunk_004_split
#print axioms array_active8_chunk_004
#print axioms array_active8_original_chunk_004
#print axioms geometryChars00_active8_chunk_005_prefix
#print axioms geometryChars00_active8_chunk_005_split
#print axioms array_active8_chunk_005
#print axioms array_active8_original_chunk_005
#print axioms geometryChars00_active8_chunk_006_prefix
#print axioms geometryChars00_active8_chunk_006_split
#print axioms array_active8_chunk_006
#print axioms array_active8_original_chunk_006
#print axioms geometryChars00_active8_chunk_007_prefix
#print axioms geometryChars00_active8_chunk_007_split
#print axioms array_active8_chunk_007
#print axioms array_active8_original_chunk_007
#print axioms active8_array_through_block_001

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
