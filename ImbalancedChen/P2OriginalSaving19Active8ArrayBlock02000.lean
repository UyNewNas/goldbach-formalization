import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01900

/-! Original active8_enumeration array block 20/20; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

def active8Chunk080Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '0', '2', '1', '7', '2', '7', '/', '7', '2', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '7', '1', '5', '5', '3', '1', '/', '9', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk080Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '7', '1', '5', '5', '3', '1', '/', '9', '5', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['3', '4'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '0', '2', '1', '7', '2', '7', '/', '7', '2', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc08100 : List SourceJson := active8Chunk080Push00 active8ArrayAcc08000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_080_before"
  err.flush

theorem geometryChars00_active8_chunk_080_prefix :
    (geometryChars00.drop 39310).take 532 = active8Chunk080Chars00 := by rfl

theorem geometryChars00_active8_chunk_080_split :
    geometryChars00.drop 39310 = active8Chunk080Chars00 ++ geometryChars00.drop 39842 := by
  calc
    geometryChars00.drop 39310 =
        (geometryChars00.drop 39310).take 532 ++ (geometryChars00.drop 39310).drop 532 :=
      (List.take_append_drop 532 (geometryChars00.drop 39310)).symm
    _ = active8Chunk080Chars00 ++ (geometryChars00.drop 39310).drop 532 :=
      congrArg (fun p => p ++ (geometryChars00.drop 39310).drop 532) geometryChars00_active8_chunk_080_prefix
    _ = active8Chunk080Chars00 ++ geometryChars00.drop 39842 := by rw [List.drop_drop]

theorem array_active8_chunk_080 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 33)
      (SourceJson.white (active8Chunk080Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 31) (SourceJson.white tail)
        (active8Chunk080Push00 acc) := by rfl

theorem array_active8_original_chunk_080 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 33)
      (SourceJson.white (geometryChars00.drop 39310)) acc =
      SourceJson.array (fuel + 31)
        (SourceJson.white (geometryChars00.drop 39842)) (active8Chunk080Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 33) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_080_split).trans
    (array_active8_chunk_080 fuel (geometryChars00.drop 39842) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_080_complete"
  err.flush

def active8Chunk081Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '3', '7', '6', '5', '4', '3', '7', '/', '3', '5', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk081Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '3', '7', '6', '5', '4', '3', '7', '/', '3', '5', '2', '0', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc08200 : List SourceJson := active8Chunk081Push00 active8ArrayAcc08100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_081_before"
  err.flush

theorem geometryChars00_active8_chunk_081_prefix :
    (geometryChars00.drop 39842).take 483 = active8Chunk081Chars00 := by rfl

theorem geometryChars00_active8_chunk_081_split :
    geometryChars00.drop 39842 = active8Chunk081Chars00 ++ geometryChars00.drop 40325 := by
  calc
    geometryChars00.drop 39842 =
        (geometryChars00.drop 39842).take 483 ++ (geometryChars00.drop 39842).drop 483 :=
      (List.take_append_drop 483 (geometryChars00.drop 39842)).symm
    _ = active8Chunk081Chars00 ++ (geometryChars00.drop 39842).drop 483 :=
      congrArg (fun p => p ++ (geometryChars00.drop 39842).drop 483) geometryChars00_active8_chunk_081_prefix
    _ = active8Chunk081Chars00 ++ geometryChars00.drop 40325 := by rw [List.drop_drop]

theorem array_active8_chunk_081 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 31)
      (SourceJson.white (active8Chunk081Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 29) (SourceJson.white tail)
        (active8Chunk081Push00 acc) := by rfl

theorem array_active8_original_chunk_081 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 31)
      (SourceJson.white (geometryChars00.drop 39842)) acc =
      SourceJson.array (fuel + 29)
        (SourceJson.white (geometryChars00.drop 40325)) (active8Chunk081Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 31) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_081_split).trans
    (array_active8_chunk_081 fuel (geometryChars00.drop 40325) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_081_complete"
  err.flush

def active8Chunk082Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '5', '1', '0', '8', '6', '1', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', '\r', '\n', ' ', ' ', ']']
def active8Chunk082Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '5', '1', '0', '8', '6', '1', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0']))]) :: (acc)
def active8ArrayAcc08300 : List SourceJson := active8Chunk082Push00 active8ArrayAcc08200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_082_before"
  err.flush

theorem geometryChars00_active8_chunk_082_prefix :
    (geometryChars00.drop 40325).take 272 = active8Chunk082Chars00 := by rfl

theorem geometryChars00_active8_chunk_082_split :
    geometryChars00.drop 40325 = active8Chunk082Chars00 ++ geometryChars00.drop 40597 := by
  calc
    geometryChars00.drop 40325 =
        (geometryChars00.drop 40325).take 272 ++ (geometryChars00.drop 40325).drop 272 :=
      (List.take_append_drop 272 (geometryChars00.drop 40325)).symm
    _ = active8Chunk082Chars00 ++ (geometryChars00.drop 40325).drop 272 :=
      congrArg (fun p => p ++ (geometryChars00.drop 40325).drop 272) geometryChars00_active8_chunk_082_prefix
    _ = active8Chunk082Chars00 ++ geometryChars00.drop 40597 := by rw [List.drop_drop]

theorem array_active8_chunk_082 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 29)
      (SourceJson.white (active8Chunk082Chars00 ++ tail)) acc =
      .ok (.arr ((active8Chunk082Push00 acc).reverse), tail) := by rfl

theorem array_active8_original_chunk_082 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 29)
      (SourceJson.white (geometryChars00.drop 40325)) acc =
      .ok (.arr ((active8Chunk082Push00 acc).reverse), geometryChars00.drop 40597) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 29) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_082_split).trans
    (array_active8_chunk_082 fuel (geometryChars00.drop 40597) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_082_complete"
  err.flush

def active8ArrayValue00 : SourceJson := .arr (active8ArrayAcc08300.reverse)

theorem active8_array_through_block_020 (fuel : Nat) :
    SourceJson.array (fuel + 193)
      (SourceJson.white (geometryChars00.drop 408)) [] =
      .ok (active8ArrayValue00, geometryChars00.drop 40597) := by
  calc
    SourceJson.array (fuel + 193)
        (SourceJson.white (geometryChars00.drop 408)) [] =
      SourceJson.array (fuel + 33)
        (SourceJson.white (geometryChars00.drop 39310)) active8ArrayAcc08000 :=
      active8_array_through_block_019 fuel
    _ =
      SourceJson.array (fuel + 31)
        (SourceJson.white (geometryChars00.drop 39842)) active8ArrayAcc08100 :=
      array_active8_original_chunk_080 fuel active8ArrayAcc08000
    _ =
      SourceJson.array (fuel + 29)
        (SourceJson.white (geometryChars00.drop 40325)) active8ArrayAcc08200 :=
      array_active8_original_chunk_081 fuel active8ArrayAcc08100
    _ =
      .ok (active8ArrayValue00, geometryChars00.drop 40597) :=
      array_active8_original_chunk_082 fuel active8ArrayAcc08200

theorem value_active8_original (fuel : Nat) :
    SourceJson.value (fuel + 194) (geometryChars00.drop 407) =
      .ok (active8ArrayValue00, geometryChars00.drop 40597) := by
  exact (value_active8_open fuel).trans (active8_array_through_block_020 fuel)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_block_020_complete"
  err.flush

#print axioms geometryChars00_active8_chunk_080_prefix
#print axioms geometryChars00_active8_chunk_080_split
#print axioms array_active8_chunk_080
#print axioms array_active8_original_chunk_080
#print axioms geometryChars00_active8_chunk_081_prefix
#print axioms geometryChars00_active8_chunk_081_split
#print axioms array_active8_chunk_081
#print axioms array_active8_original_chunk_081
#print axioms geometryChars00_active8_chunk_082_prefix
#print axioms geometryChars00_active8_chunk_082_split
#print axioms array_active8_chunk_082
#print axioms array_active8_original_chunk_082
#print axioms active8_array_through_block_020
#print axioms value_active8_original

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
