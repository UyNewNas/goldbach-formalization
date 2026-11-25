import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00800

/-! Original active8_enumeration array block 9/20; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

def active8Chunk036Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '2', '9', '6', '8', '3', '3', '/', '8', '9', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '2', '9', '8', '4', '1', '8', '7', '/', '3', '6', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk036Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['6', '1'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '2', '9', '8', '4', '1', '8', '7', '/', '3', '6', '8', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '2', '9', '6', '8', '3', '3', '/', '8', '9', '0', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc03700 : List SourceJson := active8Chunk036Push00 active8ArrayAcc03600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_036_before"
  err.flush

theorem geometryChars00_active8_chunk_036_prefix :
    (geometryChars00.drop 18039).take 533 = active8Chunk036Chars00 := by rfl

theorem geometryChars00_active8_chunk_036_split :
    geometryChars00.drop 18039 = active8Chunk036Chars00 ++ geometryChars00.drop 18572 := by
  calc
    geometryChars00.drop 18039 =
        (geometryChars00.drop 18039).take 533 ++ (geometryChars00.drop 18039).drop 533 :=
      (List.take_append_drop 533 (geometryChars00.drop 18039)).symm
    _ = active8Chunk036Chars00 ++ (geometryChars00.drop 18039).drop 533 :=
      congrArg (fun p => p ++ (geometryChars00.drop 18039).drop 533) geometryChars00_active8_chunk_036_prefix
    _ = active8Chunk036Chars00 ++ geometryChars00.drop 18572 := by rw [List.drop_drop]

theorem array_active8_chunk_036 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 121)
      (SourceJson.white (active8Chunk036Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 119) (SourceJson.white tail)
        (active8Chunk036Push00 acc) := by rfl

theorem array_active8_original_chunk_036 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 121)
      (SourceJson.white (geometryChars00.drop 18039)) acc =
      SourceJson.array (fuel + 119)
        (SourceJson.white (geometryChars00.drop 18572)) (active8Chunk036Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 121) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_036_split).trans
    (array_active8_chunk_036 fuel (geometryChars00.drop 18572) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_036_complete"
  err.flush

def active8Chunk037Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '2', '9', '8', '4', '1', '8', '7', '/', '1', '8', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk037Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['3', '4'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '2', '9', '8', '4', '1', '8', '7', '/', '1', '8', '8', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '2']))]) :: (acc))
def active8ArrayAcc03800 : List SourceJson := active8Chunk037Push00 active8ArrayAcc03700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_037_before"
  err.flush

theorem geometryChars00_active8_chunk_037_prefix :
    (geometryChars00.drop 18572).take 482 = active8Chunk037Chars00 := by rfl

theorem geometryChars00_active8_chunk_037_split :
    geometryChars00.drop 18572 = active8Chunk037Chars00 ++ geometryChars00.drop 19054 := by
  calc
    geometryChars00.drop 18572 =
        (geometryChars00.drop 18572).take 482 ++ (geometryChars00.drop 18572).drop 482 :=
      (List.take_append_drop 482 (geometryChars00.drop 18572)).symm
    _ = active8Chunk037Chars00 ++ (geometryChars00.drop 18572).drop 482 :=
      congrArg (fun p => p ++ (geometryChars00.drop 18572).drop 482) geometryChars00_active8_chunk_037_prefix
    _ = active8Chunk037Chars00 ++ geometryChars00.drop 19054 := by rw [List.drop_drop]

theorem array_active8_chunk_037 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 119)
      (SourceJson.white (active8Chunk037Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 117) (SourceJson.white tail)
        (active8Chunk037Push00 acc) := by rfl

theorem array_active8_original_chunk_037 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 119)
      (SourceJson.white (geometryChars00.drop 18572)) acc =
      SourceJson.array (fuel + 117)
        (SourceJson.white (geometryChars00.drop 19054)) (active8Chunk037Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 119) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_037_split).trans
    (array_active8_chunk_037 fuel (geometryChars00.drop 19054) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_037_complete"
  err.flush

def active8Chunk038Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '6', '2', '4', '5', '3', '/', '1', '6', '4', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk038Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '6', '2', '4', '5', '3', '/', '1', '6', '4', '5', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc03900 : List SourceJson := active8Chunk038Push00 active8ArrayAcc03800

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_038_before"
  err.flush

theorem geometryChars00_active8_chunk_038_prefix :
    (geometryChars00.drop 19054).take 478 = active8Chunk038Chars00 := by rfl

theorem geometryChars00_active8_chunk_038_split :
    geometryChars00.drop 19054 = active8Chunk038Chars00 ++ geometryChars00.drop 19532 := by
  calc
    geometryChars00.drop 19054 =
        (geometryChars00.drop 19054).take 478 ++ (geometryChars00.drop 19054).drop 478 :=
      (List.take_append_drop 478 (geometryChars00.drop 19054)).symm
    _ = active8Chunk038Chars00 ++ (geometryChars00.drop 19054).drop 478 :=
      congrArg (fun p => p ++ (geometryChars00.drop 19054).drop 478) geometryChars00_active8_chunk_038_prefix
    _ = active8Chunk038Chars00 ++ geometryChars00.drop 19532 := by rw [List.drop_drop]

theorem array_active8_chunk_038 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 117)
      (SourceJson.white (active8Chunk038Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 115) (SourceJson.white tail)
        (active8Chunk038Push00 acc) := by rfl

theorem array_active8_original_chunk_038 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 117)
      (SourceJson.white (geometryChars00.drop 19054)) acc =
      SourceJson.array (fuel + 115)
        (SourceJson.white (geometryChars00.drop 19532)) (active8Chunk038Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 117) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_038_split).trans
    (array_active8_chunk_038 fuel (geometryChars00.drop 19532) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_038_complete"
  err.flush

def active8Chunk039Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk039Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '5']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['9']))]) :: (acc))
def active8ArrayAcc04000 : List SourceJson := active8Chunk039Push00 active8ArrayAcc03900

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_039_before"
  err.flush

theorem geometryChars00_active8_chunk_039_prefix :
    (geometryChars00.drop 19532).take 427 = active8Chunk039Chars00 := by rfl

theorem geometryChars00_active8_chunk_039_split :
    geometryChars00.drop 19532 = active8Chunk039Chars00 ++ geometryChars00.drop 19959 := by
  calc
    geometryChars00.drop 19532 =
        (geometryChars00.drop 19532).take 427 ++ (geometryChars00.drop 19532).drop 427 :=
      (List.take_append_drop 427 (geometryChars00.drop 19532)).symm
    _ = active8Chunk039Chars00 ++ (geometryChars00.drop 19532).drop 427 :=
      congrArg (fun p => p ++ (geometryChars00.drop 19532).drop 427) geometryChars00_active8_chunk_039_prefix
    _ = active8Chunk039Chars00 ++ geometryChars00.drop 19959 := by rw [List.drop_drop]

theorem array_active8_chunk_039 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 115)
      (SourceJson.white (active8Chunk039Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 113) (SourceJson.white tail)
        (active8Chunk039Push00 acc) := by rfl

theorem array_active8_original_chunk_039 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 115)
      (SourceJson.white (geometryChars00.drop 19532)) acc =
      SourceJson.array (fuel + 113)
        (SourceJson.white (geometryChars00.drop 19959)) (active8Chunk039Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 115) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_039_split).trans
    (array_active8_chunk_039 fuel (geometryChars00.drop 19959) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_039_complete"
  err.flush

theorem active8_array_through_block_009 (fuel : Nat) :
    SourceJson.array (fuel + 193)
      (SourceJson.white (geometryChars00.drop 408)) [] =
      SourceJson.array (fuel + 113)
        (SourceJson.white (geometryChars00.drop 19959)) active8ArrayAcc04000 := by
  calc
    SourceJson.array (fuel + 193)
        (SourceJson.white (geometryChars00.drop 408)) [] =
      SourceJson.array (fuel + 121)
        (SourceJson.white (geometryChars00.drop 18039)) active8ArrayAcc03600 :=
      active8_array_through_block_008 fuel
    _ =
      SourceJson.array (fuel + 119)
        (SourceJson.white (geometryChars00.drop 18572)) active8ArrayAcc03700 :=
      array_active8_original_chunk_036 fuel active8ArrayAcc03600
    _ =
      SourceJson.array (fuel + 117)
        (SourceJson.white (geometryChars00.drop 19054)) active8ArrayAcc03800 :=
      array_active8_original_chunk_037 fuel active8ArrayAcc03700
    _ =
      SourceJson.array (fuel + 115)
        (SourceJson.white (geometryChars00.drop 19532)) active8ArrayAcc03900 :=
      array_active8_original_chunk_038 fuel active8ArrayAcc03800
    _ =
      SourceJson.array (fuel + 113)
        (SourceJson.white (geometryChars00.drop 19959)) active8ArrayAcc04000 :=
      array_active8_original_chunk_039 fuel active8ArrayAcc03900

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_block_009_complete"
  err.flush

#print axioms geometryChars00_active8_chunk_036_prefix
#print axioms geometryChars00_active8_chunk_036_split
#print axioms array_active8_chunk_036
#print axioms array_active8_original_chunk_036
#print axioms geometryChars00_active8_chunk_037_prefix
#print axioms geometryChars00_active8_chunk_037_split
#print axioms array_active8_chunk_037
#print axioms array_active8_original_chunk_037
#print axioms geometryChars00_active8_chunk_038_prefix
#print axioms geometryChars00_active8_chunk_038_split
#print axioms array_active8_chunk_038
#print axioms array_active8_original_chunk_038
#print axioms geometryChars00_active8_chunk_039_prefix
#print axioms geometryChars00_active8_chunk_039_split
#print axioms array_active8_chunk_039
#print axioms array_active8_original_chunk_039
#print axioms active8_array_through_block_009

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
