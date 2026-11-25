import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01200

/-! Original active8_enumeration array block 13/20; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

def active8Chunk052Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '6', '2', '4', '5', '3', '/', '2', '1', '1', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk052Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '6', '2', '4', '5', '3', '/', '2', '1', '1', '5', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc05300 : List SourceJson := active8Chunk052Push00 active8ArrayAcc05200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_052_before"
  err.flush

theorem geometryChars00_active8_chunk_052_prefix :
    (geometryChars00.drop 25796).take 478 = active8Chunk052Chars00 := by rfl

theorem geometryChars00_active8_chunk_052_split :
    geometryChars00.drop 25796 = active8Chunk052Chars00 ++ geometryChars00.drop 26274 := by
  calc
    geometryChars00.drop 25796 =
        (geometryChars00.drop 25796).take 478 ++ (geometryChars00.drop 25796).drop 478 :=
      (List.take_append_drop 478 (geometryChars00.drop 25796)).symm
    _ = active8Chunk052Chars00 ++ (geometryChars00.drop 25796).drop 478 :=
      congrArg (fun p => p ++ (geometryChars00.drop 25796).drop 478) geometryChars00_active8_chunk_052_prefix
    _ = active8Chunk052Chars00 ++ geometryChars00.drop 26274 := by rw [List.drop_drop]

theorem array_active8_chunk_052 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 89)
      (SourceJson.white (active8Chunk052Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 87) (SourceJson.white tail)
        (active8Chunk052Push00 acc) := by rfl

theorem array_active8_original_chunk_052 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 89)
      (SourceJson.white (geometryChars00.drop 25796)) acc =
      SourceJson.array (fuel + 87)
        (SourceJson.white (geometryChars00.drop 26274)) (active8Chunk052Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 89) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_052_split).trans
    (array_active8_chunk_052 fuel (geometryChars00.drop 26274) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_052_complete"
  err.flush

def active8Chunk053Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk053Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '4']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['8']))]) :: (acc))
def active8ArrayAcc05400 : List SourceJson := active8Chunk053Push00 active8ArrayAcc05300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_053_before"
  err.flush

theorem geometryChars00_active8_chunk_053_prefix :
    (geometryChars00.drop 26274).take 427 = active8Chunk053Chars00 := by rfl

theorem geometryChars00_active8_chunk_053_split :
    geometryChars00.drop 26274 = active8Chunk053Chars00 ++ geometryChars00.drop 26701 := by
  calc
    geometryChars00.drop 26274 =
        (geometryChars00.drop 26274).take 427 ++ (geometryChars00.drop 26274).drop 427 :=
      (List.take_append_drop 427 (geometryChars00.drop 26274)).symm
    _ = active8Chunk053Chars00 ++ (geometryChars00.drop 26274).drop 427 :=
      congrArg (fun p => p ++ (geometryChars00.drop 26274).drop 427) geometryChars00_active8_chunk_053_prefix
    _ = active8Chunk053Chars00 ++ geometryChars00.drop 26701 := by rw [List.drop_drop]

theorem array_active8_chunk_053 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 87)
      (SourceJson.white (active8Chunk053Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 85) (SourceJson.white tail)
        (active8Chunk053Push00 acc) := by rfl

theorem array_active8_original_chunk_053 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 87)
      (SourceJson.white (geometryChars00.drop 26274)) acc =
      SourceJson.array (fuel + 85)
        (SourceJson.white (geometryChars00.drop 26701)) (active8Chunk053Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 87) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_053_split).trans
    (array_active8_chunk_053 fuel (geometryChars00.drop 26701) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_053_complete"
  err.flush

def active8Chunk054Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '3', '7', '4', '9', '/', '6', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk054Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['6']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '4'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '3', '7', '4', '9', '/', '6', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc05500 : List SourceJson := active8Chunk054Push00 active8ArrayAcc05400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_054_before"
  err.flush

theorem geometryChars00_active8_chunk_054_prefix :
    (geometryChars00.drop 26701).take 474 = active8Chunk054Chars00 := by rfl

theorem geometryChars00_active8_chunk_054_split :
    geometryChars00.drop 26701 = active8Chunk054Chars00 ++ geometryChars00.drop 27175 := by
  calc
    geometryChars00.drop 26701 =
        (geometryChars00.drop 26701).take 474 ++ (geometryChars00.drop 26701).drop 474 :=
      (List.take_append_drop 474 (geometryChars00.drop 26701)).symm
    _ = active8Chunk054Chars00 ++ (geometryChars00.drop 26701).drop 474 :=
      congrArg (fun p => p ++ (geometryChars00.drop 26701).drop 474) geometryChars00_active8_chunk_054_prefix
    _ = active8Chunk054Chars00 ++ geometryChars00.drop 27175 := by rw [List.drop_drop]

theorem array_active8_chunk_054 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 85)
      (SourceJson.white (active8Chunk054Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 83) (SourceJson.white tail)
        (active8Chunk054Push00 acc) := by rfl

theorem array_active8_original_chunk_054 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 85)
      (SourceJson.white (geometryChars00.drop 26701)) acc =
      SourceJson.array (fuel + 83)
        (SourceJson.white (geometryChars00.drop 27175)) (active8Chunk054Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 85) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_054_split).trans
    (array_active8_chunk_054 fuel (geometryChars00.drop 27175) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_054_complete"
  err.flush

def active8Chunk055Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk055Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['3']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['5']))]) :: (acc))
def active8ArrayAcc05600 : List SourceJson := active8Chunk055Push00 active8ArrayAcc05500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_055_before"
  err.flush

theorem geometryChars00_active8_chunk_055_prefix :
    (geometryChars00.drop 27175).take 426 = active8Chunk055Chars00 := by rfl

theorem geometryChars00_active8_chunk_055_split :
    geometryChars00.drop 27175 = active8Chunk055Chars00 ++ geometryChars00.drop 27601 := by
  calc
    geometryChars00.drop 27175 =
        (geometryChars00.drop 27175).take 426 ++ (geometryChars00.drop 27175).drop 426 :=
      (List.take_append_drop 426 (geometryChars00.drop 27175)).symm
    _ = active8Chunk055Chars00 ++ (geometryChars00.drop 27175).drop 426 :=
      congrArg (fun p => p ++ (geometryChars00.drop 27175).drop 426) geometryChars00_active8_chunk_055_prefix
    _ = active8Chunk055Chars00 ++ geometryChars00.drop 27601 := by rw [List.drop_drop]

theorem array_active8_chunk_055 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 83)
      (SourceJson.white (active8Chunk055Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 81) (SourceJson.white tail)
        (active8Chunk055Push00 acc) := by rfl

theorem array_active8_original_chunk_055 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 83)
      (SourceJson.white (geometryChars00.drop 27175)) acc =
      SourceJson.array (fuel + 81)
        (SourceJson.white (geometryChars00.drop 27601)) (active8Chunk055Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 83) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_055_split).trans
    (array_active8_chunk_055 fuel (geometryChars00.drop 27601) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_055_complete"
  err.flush

theorem active8_array_through_block_013 (fuel : Nat) :
    SourceJson.array (fuel + 193)
      (SourceJson.white (geometryChars00.drop 408)) [] =
      SourceJson.array (fuel + 81)
        (SourceJson.white (geometryChars00.drop 27601)) active8ArrayAcc05600 := by
  calc
    SourceJson.array (fuel + 193)
        (SourceJson.white (geometryChars00.drop 408)) [] =
      SourceJson.array (fuel + 89)
        (SourceJson.white (geometryChars00.drop 25796)) active8ArrayAcc05200 :=
      active8_array_through_block_012 fuel
    _ =
      SourceJson.array (fuel + 87)
        (SourceJson.white (geometryChars00.drop 26274)) active8ArrayAcc05300 :=
      array_active8_original_chunk_052 fuel active8ArrayAcc05200
    _ =
      SourceJson.array (fuel + 85)
        (SourceJson.white (geometryChars00.drop 26701)) active8ArrayAcc05400 :=
      array_active8_original_chunk_053 fuel active8ArrayAcc05300
    _ =
      SourceJson.array (fuel + 83)
        (SourceJson.white (geometryChars00.drop 27175)) active8ArrayAcc05500 :=
      array_active8_original_chunk_054 fuel active8ArrayAcc05400
    _ =
      SourceJson.array (fuel + 81)
        (SourceJson.white (geometryChars00.drop 27601)) active8ArrayAcc05600 :=
      array_active8_original_chunk_055 fuel active8ArrayAcc05500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_block_013_complete"
  err.flush

#print axioms geometryChars00_active8_chunk_052_prefix
#print axioms geometryChars00_active8_chunk_052_split
#print axioms array_active8_chunk_052
#print axioms array_active8_original_chunk_052
#print axioms geometryChars00_active8_chunk_053_prefix
#print axioms geometryChars00_active8_chunk_053_split
#print axioms array_active8_chunk_053
#print axioms array_active8_original_chunk_053
#print axioms geometryChars00_active8_chunk_054_prefix
#print axioms geometryChars00_active8_chunk_054_split
#print axioms array_active8_chunk_054
#print axioms array_active8_original_chunk_054
#print axioms geometryChars00_active8_chunk_055_prefix
#print axioms geometryChars00_active8_chunk_055_split
#print axioms array_active8_chunk_055
#print axioms array_active8_original_chunk_055
#print axioms active8_array_through_block_013

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
