import ImbalancedChen.P2OriginalSaving19Geometry05ScalableInput

/-! Original active8_enumeration grouped chunk transitions, including exact compact-input binding.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace Active8EnumerationBlock003

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0024_before_reader"
  err.flush

noncomputable def chunk0024Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0024Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['7', '7']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['7', '7']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0024 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 145) (SourceJson.white (chunk0024Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 143) (SourceJson.white tail) (chunk0024Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0024_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0025_before_reader"
  err.flush

noncomputable def chunk0025Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '8', '2', '8', '1', '2', '1', '/', '1', '0', '7', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '7', '0', '3', '1', '1', '3', '/', '2', '1', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0025Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '7', '0', '3', '1', '1', '3', '/', '2', '1', '1', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['7', '7'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '8', '2', '8', '1', '2', '1', '/', '1', '0', '7', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0025 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 143) (SourceJson.white (chunk0025Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 141) (SourceJson.white tail) (chunk0025Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0025_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0026_before_reader"
  err.flush

noncomputable def chunk0026Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '4', '6', '8', '7', '3', '/', '1', '8', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '5', '4', '6', '8', '7', '/', '6', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0026Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['7', '7']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '5', '4', '6', '8', '7', '/', '6', '5', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '7']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '4', '6', '8', '7', '3', '/', '1', '8', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0026 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 141) (SourceJson.white (chunk0026Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 139) (SourceJson.white tail) (chunk0026Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0026_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0027_before_reader"
  err.flush

noncomputable def chunk0027Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '6', '2', '5', '0', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '5', '/', '7', '0', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0027Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['7', '7']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '5', '/', '7', '0', '4']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['7', '7']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '6', '2', '5', '0', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0027 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 139) (SourceJson.white (chunk0027Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 137) (SourceJson.white tail) (chunk0027Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0027_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0028_before_reader"
  err.flush

noncomputable def chunk0028Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0028Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '7'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7', '5'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: (acc))

theorem array_chunk0028 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 137) (SourceJson.white (chunk0028Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 135) (SourceJson.white tail) (chunk0028Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0028_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0029_before_reader"
  err.flush

noncomputable def chunk0029Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0029Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['7', '7'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['6', '1']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7', '5'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0029 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 135) (SourceJson.white (chunk0029Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 133) (SourceJson.white tail) (chunk0029Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0029_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0030_before_reader"
  err.flush

noncomputable def chunk0030Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0030Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '7']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7', '5'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: (acc))

theorem array_chunk0030 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 133) (SourceJson.white (chunk0030Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 131) (SourceJson.white tail) (chunk0030Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0030_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0031_before_reader"
  err.flush

noncomputable def chunk0031Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0031Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '2'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['6', '1']), .number (String.ofList ['7', '5']), .number (String.ofList ['7', '7'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: (acc))

theorem array_chunk0031 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 131) (SourceJson.white (chunk0031Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 129) (SourceJson.white tail) (chunk0031Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0031_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0024Chars00 ++ chunk0025Chars00 ++ chunk0026Chars00 ++ chunk0027Chars00 ++ chunk0028Chars00 ++ chunk0029Chars00 ++ chunk0030Chars00 ++ chunk0031Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0031Push00 (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 145) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 129) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0024Chars00 ++ (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 145) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 145) (SourceJson.white (chunk0024Chars00 ++ (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 145) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 143) (SourceJson.white (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))))) (chunk0024Push00 (acc)) := array_chunk0024 fuel (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 141) (SourceJson.white (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) (chunk0025Push00 (chunk0024Push00 (acc))) := array_chunk0025 fuel (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))) (chunk0024Push00 (acc))
    _ = SourceJson.array (fuel + 139) (SourceJson.white (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))) (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))) := array_chunk0026 fuel (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))) (chunk0025Push00 (chunk0024Push00 (acc)))
    _ = SourceJson.array (fuel + 137) (SourceJson.white (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))) (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))) := array_chunk0027 fuel (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))) (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))
    _ = SourceJson.array (fuel + 135) (SourceJson.white (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))) (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))) := array_chunk0028 fuel (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))) (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))
    _ = SourceJson.array (fuel + 133) (SourceJson.white (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))) (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))) := array_chunk0029 fuel (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))) (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))
    _ = SourceJson.array (fuel + 131) (SourceJson.white (chunk0031Chars00 ++ (tail))) (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))))) := array_chunk0030 fuel (chunk0031Chars00 ++ (tail)) (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))))
    _ = SourceJson.array (fuel + 129) (SourceJson.white tail) (blockPush acc) := array_chunk0031 fuel (tail) (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 12276).take 3834 = blockChars := by rfl

theorem block_original_split : sourceRest 12276 = blockChars ++ sourceRest 16110 := by
  calc
    sourceRest 12276 = (sourceRest 12276).take 3834 ++ (sourceRest 12276).drop 3834 :=
      (List.take_append_drop 3834 (sourceRest 12276)).symm
    _ = blockChars ++ (sourceRest 12276).drop 3834 :=
      congrArg (fun part => part ++ (sourceRest 12276).drop 3834) block_original_prefix
    _ = blockChars ++ sourceRest 16110 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 12276 3834)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 145) (SourceJson.white (sourceRest 12276)) acc =
      SourceJson.array (fuel + 129) (SourceJson.white (sourceRest 16110)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 145) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 16110) acc)

#print axioms array_chunk0024
#print axioms array_chunk0025
#print axioms array_chunk0026
#print axioms array_chunk0027
#print axioms array_chunk0028
#print axioms array_chunk0029
#print axioms array_chunk0030
#print axioms array_chunk0031
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end Active8EnumerationBlock003

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
