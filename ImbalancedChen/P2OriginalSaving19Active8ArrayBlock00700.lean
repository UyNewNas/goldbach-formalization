import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00600

/-! Original active8_enumeration array block 7/20; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

def active8Chunk028Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '8', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '5', '3', '8', '9', '8', '5', '3', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk028Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['8', '2'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '5', '3', '8', '9', '8', '5', '3', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc02900 : List SourceJson := active8Chunk028Push00 active8ArrayAcc02800

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_028_before"
  err.flush

theorem geometryChars00_active8_chunk_028_prefix :
    (geometryChars00.drop 14112).take 458 = active8Chunk028Chars00 := by rfl

theorem geometryChars00_active8_chunk_028_split :
    geometryChars00.drop 14112 = active8Chunk028Chars00 ++ geometryChars00.drop 14570 := by
  calc
    geometryChars00.drop 14112 =
        (geometryChars00.drop 14112).take 458 ++ (geometryChars00.drop 14112).drop 458 :=
      (List.take_append_drop 458 (geometryChars00.drop 14112)).symm
    _ = active8Chunk028Chars00 ++ (geometryChars00.drop 14112).drop 458 :=
      congrArg (fun p => p ++ (geometryChars00.drop 14112).drop 458) geometryChars00_active8_chunk_028_prefix
    _ = active8Chunk028Chars00 ++ geometryChars00.drop 14570 := by rw [List.drop_drop]

theorem array_active8_chunk_028 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 137)
      (SourceJson.white (active8Chunk028Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 135) (SourceJson.white tail)
        (active8Chunk028Push00 acc) := by rfl

theorem array_active8_original_chunk_028 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 137)
      (SourceJson.white (geometryChars00.drop 14112)) acc =
      SourceJson.array (fuel + 135)
        (SourceJson.white (geometryChars00.drop 14570)) (active8Chunk028Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 137) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_028_split).trans
    (array_active8_chunk_028 fuel (geometryChars00.drop 14570) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_028_complete"
  err.flush

def active8Chunk029Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '5', '3', '8', '9', '8', '5', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk029Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['1', '7']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['6', '1'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '5', '3', '8', '9', '8', '5', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc03000 : List SourceJson := active8Chunk029Push00 active8ArrayAcc02900

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_029_before"
  err.flush

theorem geometryChars00_active8_chunk_029_prefix :
    (geometryChars00.drop 14570).take 481 = active8Chunk029Chars00 := by rfl

theorem geometryChars00_active8_chunk_029_split :
    geometryChars00.drop 14570 = active8Chunk029Chars00 ++ geometryChars00.drop 15051 := by
  calc
    geometryChars00.drop 14570 =
        (geometryChars00.drop 14570).take 481 ++ (geometryChars00.drop 14570).drop 481 :=
      (List.take_append_drop 481 (geometryChars00.drop 14570)).symm
    _ = active8Chunk029Chars00 ++ (geometryChars00.drop 14570).drop 481 :=
      congrArg (fun p => p ++ (geometryChars00.drop 14570).drop 481) geometryChars00_active8_chunk_029_prefix
    _ = active8Chunk029Chars00 ++ geometryChars00.drop 15051 := by rw [List.drop_drop]

theorem array_active8_chunk_029 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 135)
      (SourceJson.white (active8Chunk029Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 133) (SourceJson.white tail)
        (active8Chunk029Push00 acc) := by rfl

theorem array_active8_original_chunk_029 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 135)
      (SourceJson.white (geometryChars00.drop 14570)) acc =
      SourceJson.array (fuel + 133)
        (SourceJson.white (geometryChars00.drop 15051)) (active8Chunk029Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 135) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_029_split).trans
    (array_active8_chunk_029 fuel (geometryChars00.drop 15051) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_029_complete"
  err.flush

def active8Chunk030Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk030Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['2', '7']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['6', '1']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd'], .number (String.ofList ['2', '0']))]) :: (acc))
def active8ArrayAcc03100 : List SourceJson := active8Chunk030Push00 active8ArrayAcc03000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_030_before"
  err.flush

theorem geometryChars00_active8_chunk_030_prefix :
    (geometryChars00.drop 15051).take 428 = active8Chunk030Chars00 := by rfl

theorem geometryChars00_active8_chunk_030_split :
    geometryChars00.drop 15051 = active8Chunk030Chars00 ++ geometryChars00.drop 15479 := by
  calc
    geometryChars00.drop 15051 =
        (geometryChars00.drop 15051).take 428 ++ (geometryChars00.drop 15051).drop 428 :=
      (List.take_append_drop 428 (geometryChars00.drop 15051)).symm
    _ = active8Chunk030Chars00 ++ (geometryChars00.drop 15051).drop 428 :=
      congrArg (fun p => p ++ (geometryChars00.drop 15051).drop 428) geometryChars00_active8_chunk_030_prefix
    _ = active8Chunk030Chars00 ++ geometryChars00.drop 15479 := by rw [List.drop_drop]

theorem array_active8_chunk_030 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 133)
      (SourceJson.white (active8Chunk030Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 131) (SourceJson.white tail)
        (active8Chunk030Push00 acc) := by rfl

theorem array_active8_original_chunk_030 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 133)
      (SourceJson.white (geometryChars00.drop 15051)) acc =
      SourceJson.array (fuel + 131)
        (SourceJson.white (geometryChars00.drop 15479)) (active8Chunk030Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 133) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_030_split).trans
    (array_active8_chunk_030 fuel (geometryChars00.drop 15479) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_030_complete"
  err.flush

def active8Chunk031Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '4', '9', '6', '7', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '5', '3', '8', '9', '8', '5', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
def active8Chunk031Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['3', '4'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '5', '3', '8', '9', '8', '5', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['3', '4'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '4', '9', '6', '7', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0']))]) :: (acc))
def active8ArrayAcc03200 : List SourceJson := active8Chunk031Push00 active8ArrayAcc03100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_031_before"
  err.flush

theorem geometryChars00_active8_chunk_031_prefix :
    (geometryChars00.drop 15479).take 532 = active8Chunk031Chars00 := by rfl

theorem geometryChars00_active8_chunk_031_split :
    geometryChars00.drop 15479 = active8Chunk031Chars00 ++ geometryChars00.drop 16011 := by
  calc
    geometryChars00.drop 15479 =
        (geometryChars00.drop 15479).take 532 ++ (geometryChars00.drop 15479).drop 532 :=
      (List.take_append_drop 532 (geometryChars00.drop 15479)).symm
    _ = active8Chunk031Chars00 ++ (geometryChars00.drop 15479).drop 532 :=
      congrArg (fun p => p ++ (geometryChars00.drop 15479).drop 532) geometryChars00_active8_chunk_031_prefix
    _ = active8Chunk031Chars00 ++ geometryChars00.drop 16011 := by rw [List.drop_drop]

theorem array_active8_chunk_031 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 131)
      (SourceJson.white (active8Chunk031Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 129) (SourceJson.white tail)
        (active8Chunk031Push00 acc) := by rfl

theorem array_active8_original_chunk_031 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 131)
      (SourceJson.white (geometryChars00.drop 15479)) acc =
      SourceJson.array (fuel + 129)
        (SourceJson.white (geometryChars00.drop 16011)) (active8Chunk031Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 131) (SourceJson.white s) acc)
      geometryChars00_active8_chunk_031_split).trans
    (array_active8_chunk_031 fuel (geometryChars00.drop 16011) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_chunk_031_complete"
  err.flush

theorem active8_array_through_block_007 (fuel : Nat) :
    SourceJson.array (fuel + 193)
      (SourceJson.white (geometryChars00.drop 408)) [] =
      SourceJson.array (fuel + 129)
        (SourceJson.white (geometryChars00.drop 16011)) active8ArrayAcc03200 := by
  calc
    SourceJson.array (fuel + 193)
        (SourceJson.white (geometryChars00.drop 408)) [] =
      SourceJson.array (fuel + 137)
        (SourceJson.white (geometryChars00.drop 14112)) active8ArrayAcc02800 :=
      active8_array_through_block_006 fuel
    _ =
      SourceJson.array (fuel + 135)
        (SourceJson.white (geometryChars00.drop 14570)) active8ArrayAcc02900 :=
      array_active8_original_chunk_028 fuel active8ArrayAcc02800
    _ =
      SourceJson.array (fuel + 133)
        (SourceJson.white (geometryChars00.drop 15051)) active8ArrayAcc03000 :=
      array_active8_original_chunk_029 fuel active8ArrayAcc02900
    _ =
      SourceJson.array (fuel + 131)
        (SourceJson.white (geometryChars00.drop 15479)) active8ArrayAcc03100 :=
      array_active8_original_chunk_030 fuel active8ArrayAcc03000
    _ =
      SourceJson.array (fuel + 129)
        (SourceJson.white (geometryChars00.drop 16011)) active8ArrayAcc03200 :=
      array_active8_original_chunk_031 fuel active8ArrayAcc03100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_block_007_complete"
  err.flush

#print axioms geometryChars00_active8_chunk_028_prefix
#print axioms geometryChars00_active8_chunk_028_split
#print axioms array_active8_chunk_028
#print axioms array_active8_original_chunk_028
#print axioms geometryChars00_active8_chunk_029_prefix
#print axioms geometryChars00_active8_chunk_029_split
#print axioms array_active8_chunk_029
#print axioms array_active8_original_chunk_029
#print axioms geometryChars00_active8_chunk_030_prefix
#print axioms geometryChars00_active8_chunk_030_split
#print axioms array_active8_chunk_030
#print axioms array_active8_original_chunk_030
#print axioms geometryChars00_active8_chunk_031_prefix
#print axioms geometryChars00_active8_chunk_031_split
#print axioms array_active8_chunk_031
#print axioms array_active8_original_chunk_031
#print axioms active8_array_through_block_007

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
