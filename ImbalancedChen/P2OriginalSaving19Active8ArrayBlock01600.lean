import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01500

/-! Original active8_enumeration array block 16/20; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

def active8Chunk064Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk064Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: (acc))
def active8ArrayAcc06500 : List SourceJson := active8Chunk064Push00 active8ArrayAcc06400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_064_before"
  err.flush

theorem geometryChars00_active8_chunk_064_prefix :
    (geometryChars00.drop 31463).take 380 = active8Chunk064Chars00 := by rfl

theorem geometryChars00_active8_chunk_064_split :
    geometryChars00.drop 31463 = active8Chunk064Chars00 ++ geometryChars00.drop 31843 := by
  calc
    geometryChars00.drop 31463 =
        (geometryChars00.drop 31463).take 380 ++ (geometryChars00.drop 31463).drop 380 :=
      (List.take_append_drop 380 (geometryChars00.drop 31463)).symm
    _ = active8Chunk064Chars00 ++ (geometryChars00.drop 31463).drop 380 :=
      congrArg (fun p => p ++ (geometryChars00.drop 31463).drop 380) geometryChars00_active8_chunk_064_prefix
    _ = active8Chunk064Chars00 ++ geometryChars00.drop 31843 := by rw [List.drop_drop]

theorem array_active8_chunk_064 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 65)
      (SourceJson.white (active8Chunk064Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 63) (SourceJson.white tail)
        (active8Chunk064Push00 acc) := by rfl

theorem array_active8_original_chunk_064 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 65)
      (SourceJson.white (geometryChars00.drop 31463)) acc =
      SourceJson.array (fuel + 63)
        (SourceJson.white (geometryChars00.drop 31843)) (active8Chunk064Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 65) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_064_split).trans
    (array_active8_chunk_064 fuel (geometryChars00.drop 31843) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_064_complete"
  err.flush

def active8Chunk065Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '9', '9', '9', '8', '5', '7', '/', '4', '3', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk065Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '9', '9', '9', '8', '5', '7', '/', '4', '3', '5', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc06600 : List SourceJson := active8Chunk065Push00 active8ArrayAcc06500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_065_before"
  err.flush

theorem geometryChars00_active8_chunk_065_prefix :
    (geometryChars00.drop 31843).take 525 = active8Chunk065Chars00 := by rfl

theorem geometryChars00_active8_chunk_065_split :
    geometryChars00.drop 31843 = active8Chunk065Chars00 ++ geometryChars00.drop 32368 := by
  calc
    geometryChars00.drop 31843 =
        (geometryChars00.drop 31843).take 525 ++ (geometryChars00.drop 31843).drop 525 :=
      (List.take_append_drop 525 (geometryChars00.drop 31843)).symm
    _ = active8Chunk065Chars00 ++ (geometryChars00.drop 31843).drop 525 :=
      congrArg (fun p => p ++ (geometryChars00.drop 31843).drop 525) geometryChars00_active8_chunk_065_prefix
    _ = active8Chunk065Chars00 ++ geometryChars00.drop 32368 := by rw [List.drop_drop]

theorem array_active8_chunk_065 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 63)
      (SourceJson.white (active8Chunk065Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 61) (SourceJson.white tail)
        (active8Chunk065Push00 acc) := by rfl

theorem array_active8_original_chunk_065 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 63)
      (SourceJson.white (geometryChars00.drop 31843)) acc =
      SourceJson.array (fuel + 61)
        (SourceJson.white (geometryChars00.drop 32368)) (active8Chunk065Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 63) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_065_split).trans
    (array_active8_chunk_065 fuel (geometryChars00.drop 32368) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_065_complete"
  err.flush

def active8Chunk066Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk066Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc06700 : List SourceJson := active8Chunk066Push00 active8ArrayAcc06600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_066_before"
  err.flush

theorem geometryChars00_active8_chunk_066_prefix :
    (geometryChars00.drop 32368).take 520 = active8Chunk066Chars00 := by rfl

theorem geometryChars00_active8_chunk_066_split :
    geometryChars00.drop 32368 = active8Chunk066Chars00 ++ geometryChars00.drop 32888 := by
  calc
    geometryChars00.drop 32368 =
        (geometryChars00.drop 32368).take 520 ++ (geometryChars00.drop 32368).drop 520 :=
      (List.take_append_drop 520 (geometryChars00.drop 32368)).symm
    _ = active8Chunk066Chars00 ++ (geometryChars00.drop 32368).drop 520 :=
      congrArg (fun p => p ++ (geometryChars00.drop 32368).drop 520) geometryChars00_active8_chunk_066_prefix
    _ = active8Chunk066Chars00 ++ geometryChars00.drop 32888 := by rw [List.drop_drop]

theorem array_active8_chunk_066 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 61)
      (SourceJson.white (active8Chunk066Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 59) (SourceJson.white tail)
        (active8Chunk066Push00 acc) := by rfl

theorem array_active8_original_chunk_066 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 61)
      (SourceJson.white (geometryChars00.drop 32368)) acc =
      SourceJson.array (fuel + 59)
        (SourceJson.white (geometryChars00.drop 32888)) (active8Chunk066Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 61) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_066_split).trans
    (array_active8_chunk_066 fuel (geometryChars00.drop 32888) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_066_complete"
  err.flush

def active8Chunk067Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk067Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc06800 : List SourceJson := active8Chunk067Push00 active8ArrayAcc06700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_067_before"
  err.flush

theorem geometryChars00_active8_chunk_067_prefix :
    (geometryChars00.drop 32888).take 520 = active8Chunk067Chars00 := by rfl

theorem geometryChars00_active8_chunk_067_split :
    geometryChars00.drop 32888 = active8Chunk067Chars00 ++ geometryChars00.drop 33408 := by
  calc
    geometryChars00.drop 32888 =
        (geometryChars00.drop 32888).take 520 ++ (geometryChars00.drop 32888).drop 520 :=
      (List.take_append_drop 520 (geometryChars00.drop 32888)).symm
    _ = active8Chunk067Chars00 ++ (geometryChars00.drop 32888).drop 520 :=
      congrArg (fun p => p ++ (geometryChars00.drop 32888).drop 520) geometryChars00_active8_chunk_067_prefix
    _ = active8Chunk067Chars00 ++ geometryChars00.drop 33408 := by rw [List.drop_drop]

theorem array_active8_chunk_067 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 59)
      (SourceJson.white (active8Chunk067Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 57) (SourceJson.white tail)
        (active8Chunk067Push00 acc) := by rfl

theorem array_active8_original_chunk_067 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 59)
      (SourceJson.white (geometryChars00.drop 32888)) acc =
      SourceJson.array (fuel + 57)
        (SourceJson.white (geometryChars00.drop 33408)) (active8Chunk067Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 59) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_067_split).trans
    (array_active8_chunk_067 fuel (geometryChars00.drop 33408) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_067_complete"
  err.flush

theorem active8_array_through_block_016 (fuel : Nat) :
    SourceJson.array (fuel + 193)
      (SourceJson.white (geometryChars00.drop 408)) [] =
      SourceJson.array (fuel + 57)
        (SourceJson.white (geometryChars00.drop 33408)) active8ArrayAcc06800 := by
  calc
    SourceJson.array (fuel + 193)
        (SourceJson.white (geometryChars00.drop 408)) [] =
      SourceJson.array (fuel + 65)
        (SourceJson.white (geometryChars00.drop 31463)) active8ArrayAcc06400 :=
      active8_array_through_block_015 fuel
    _ =
      SourceJson.array (fuel + 63)
        (SourceJson.white (geometryChars00.drop 31843)) active8ArrayAcc06500 :=
      array_active8_original_chunk_064 fuel active8ArrayAcc06400
    _ =
      SourceJson.array (fuel + 61)
        (SourceJson.white (geometryChars00.drop 32368)) active8ArrayAcc06600 :=
      array_active8_original_chunk_065 fuel active8ArrayAcc06500
    _ =
      SourceJson.array (fuel + 59)
        (SourceJson.white (geometryChars00.drop 32888)) active8ArrayAcc06700 :=
      array_active8_original_chunk_066 fuel active8ArrayAcc06600
    _ =
      SourceJson.array (fuel + 57)
        (SourceJson.white (geometryChars00.drop 33408)) active8ArrayAcc06800 :=
      array_active8_original_chunk_067 fuel active8ArrayAcc06700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_block_016_complete"
  err.flush

#print axioms geometryChars00_active8_chunk_064_prefix
#print axioms geometryChars00_active8_chunk_064_split
#print axioms array_active8_chunk_064
#print axioms array_active8_original_chunk_064
#print axioms geometryChars00_active8_chunk_065_prefix
#print axioms geometryChars00_active8_chunk_065_split
#print axioms array_active8_chunk_065
#print axioms array_active8_original_chunk_065
#print axioms geometryChars00_active8_chunk_066_prefix
#print axioms geometryChars00_active8_chunk_066_split
#print axioms array_active8_chunk_066
#print axioms array_active8_original_chunk_066
#print axioms geometryChars00_active8_chunk_067_prefix
#print axioms geometryChars00_active8_chunk_067_split
#print axioms array_active8_chunk_067
#print axioms array_active8_original_chunk_067
#print axioms active8_array_through_block_016

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
