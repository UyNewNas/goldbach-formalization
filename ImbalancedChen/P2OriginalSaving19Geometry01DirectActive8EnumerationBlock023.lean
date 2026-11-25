import ImbalancedChen.P2OriginalSaving19Geometry01DirectInput

/-! Original active8_enumeration grouped chunk transitions, including exact compact-input binding.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace Active8EnumerationBlock023

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0177_before_reader"
  err.flush

noncomputable def chunk0177Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '7', '0', '3', '1', '7', '7', '/', '3', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0177Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '7', '0', '3', '1', '7', '7', '/', '3', '2', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['7', '5']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0177 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 169) (SourceJson.white (chunk0177Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 167) (SourceJson.white tail) (chunk0177Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0177_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0178_before_reader"
  err.flush

noncomputable def chunk0178Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0178Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0178 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 167) (SourceJson.white (chunk0178Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 165) (SourceJson.white tail) (chunk0178Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0178_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0179_before_reader"
  err.flush

noncomputable def chunk0179Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '8', '1', '/', '1', '6', '1', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '3', '/', '5', '1', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0179Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '3', '/', '5', '1', '2']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '8', '1', '/', '1', '6', '1', '6']))]) :: (acc))

theorem array_chunk0179 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 165) (SourceJson.white (chunk0179Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 163) (SourceJson.white tail) (chunk0179Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0179_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0180_before_reader"
  err.flush

noncomputable def chunk0180Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '8', '7', '5', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '8', '7', '5', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0180Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '8', '7', '5', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '8', '7', '5', '0', '0', '0']))]) :: (acc))

theorem array_chunk0180 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 163) (SourceJson.white (chunk0180Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 161) (SourceJson.white tail) (chunk0180Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0180_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0181_before_reader"
  err.flush

noncomputable def chunk0181Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '2', '0', '2', '7', '5', '4', '9', '/', '7', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '2', '8', '3', '8', '6', '1', '/', '3', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0181Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '2', '8', '3', '8', '6', '1', '/', '3', '5', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '2', '0', '2', '7', '5', '4', '9', '/', '7', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0181 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 161) (SourceJson.white (chunk0181Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 159) (SourceJson.white tail) (chunk0181Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0181_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0182_before_reader"
  err.flush

noncomputable def chunk0182Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '7', '9', '/', '3', '8', '0', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0182Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '7', '9', '/', '3', '8', '0', '8']))]) :: (acc))

theorem array_chunk0182 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 159) (SourceJson.white (chunk0182Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 157) (SourceJson.white tail) (chunk0182Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0182_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0183_before_reader"
  err.flush

noncomputable def chunk0183Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0183Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '4'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '7', '/', '2', '2', '5', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['8', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '4'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '7', '/', '2', '2', '5', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0183 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 157) (SourceJson.white (chunk0183Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 155) (SourceJson.white tail) (chunk0183Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0183_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0184_before_reader"
  err.flush

noncomputable def chunk0184Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0184Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['7', '5']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: (acc))

theorem array_chunk0184 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 155) (SourceJson.white (chunk0184Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 153) (SourceJson.white tail) (chunk0184Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0184_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0177Chars00 ++ chunk0178Chars00 ++ chunk0179Chars00 ++ chunk0180Chars00 ++ chunk0181Chars00 ++ chunk0182Chars00 ++ chunk0183Chars00 ++ chunk0184Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0184Push00 (chunk0183Push00 (chunk0182Push00 (chunk0181Push00 (chunk0180Push00 (chunk0179Push00 (chunk0178Push00 (chunk0177Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 169) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 153) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0177Chars00 ++ (chunk0178Chars00 ++ (chunk0179Chars00 ++ (chunk0180Chars00 ++ (chunk0181Chars00 ++ (chunk0182Chars00 ++ (chunk0183Chars00 ++ (chunk0184Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 169) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 169) (SourceJson.white (chunk0177Chars00 ++ (chunk0178Chars00 ++ (chunk0179Chars00 ++ (chunk0180Chars00 ++ (chunk0181Chars00 ++ (chunk0182Chars00 ++ (chunk0183Chars00 ++ (chunk0184Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 169) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 167) (SourceJson.white (chunk0178Chars00 ++ (chunk0179Chars00 ++ (chunk0180Chars00 ++ (chunk0181Chars00 ++ (chunk0182Chars00 ++ (chunk0183Chars00 ++ (chunk0184Chars00 ++ (tail))))))))) (chunk0177Push00 (acc)) := array_chunk0177 fuel (chunk0178Chars00 ++ (chunk0179Chars00 ++ (chunk0180Chars00 ++ (chunk0181Chars00 ++ (chunk0182Chars00 ++ (chunk0183Chars00 ++ (chunk0184Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 165) (SourceJson.white (chunk0179Chars00 ++ (chunk0180Chars00 ++ (chunk0181Chars00 ++ (chunk0182Chars00 ++ (chunk0183Chars00 ++ (chunk0184Chars00 ++ (tail)))))))) (chunk0178Push00 (chunk0177Push00 (acc))) := array_chunk0178 fuel (chunk0179Chars00 ++ (chunk0180Chars00 ++ (chunk0181Chars00 ++ (chunk0182Chars00 ++ (chunk0183Chars00 ++ (chunk0184Chars00 ++ (tail))))))) (chunk0177Push00 (acc))
    _ = SourceJson.array (fuel + 163) (SourceJson.white (chunk0180Chars00 ++ (chunk0181Chars00 ++ (chunk0182Chars00 ++ (chunk0183Chars00 ++ (chunk0184Chars00 ++ (tail))))))) (chunk0179Push00 (chunk0178Push00 (chunk0177Push00 (acc)))) := array_chunk0179 fuel (chunk0180Chars00 ++ (chunk0181Chars00 ++ (chunk0182Chars00 ++ (chunk0183Chars00 ++ (chunk0184Chars00 ++ (tail)))))) (chunk0178Push00 (chunk0177Push00 (acc)))
    _ = SourceJson.array (fuel + 161) (SourceJson.white (chunk0181Chars00 ++ (chunk0182Chars00 ++ (chunk0183Chars00 ++ (chunk0184Chars00 ++ (tail)))))) (chunk0180Push00 (chunk0179Push00 (chunk0178Push00 (chunk0177Push00 (acc))))) := array_chunk0180 fuel (chunk0181Chars00 ++ (chunk0182Chars00 ++ (chunk0183Chars00 ++ (chunk0184Chars00 ++ (tail))))) (chunk0179Push00 (chunk0178Push00 (chunk0177Push00 (acc))))
    _ = SourceJson.array (fuel + 159) (SourceJson.white (chunk0182Chars00 ++ (chunk0183Chars00 ++ (chunk0184Chars00 ++ (tail))))) (chunk0181Push00 (chunk0180Push00 (chunk0179Push00 (chunk0178Push00 (chunk0177Push00 (acc)))))) := array_chunk0181 fuel (chunk0182Chars00 ++ (chunk0183Chars00 ++ (chunk0184Chars00 ++ (tail)))) (chunk0180Push00 (chunk0179Push00 (chunk0178Push00 (chunk0177Push00 (acc)))))
    _ = SourceJson.array (fuel + 157) (SourceJson.white (chunk0183Chars00 ++ (chunk0184Chars00 ++ (tail)))) (chunk0182Push00 (chunk0181Push00 (chunk0180Push00 (chunk0179Push00 (chunk0178Push00 (chunk0177Push00 (acc))))))) := array_chunk0182 fuel (chunk0183Chars00 ++ (chunk0184Chars00 ++ (tail))) (chunk0181Push00 (chunk0180Push00 (chunk0179Push00 (chunk0178Push00 (chunk0177Push00 (acc))))))
    _ = SourceJson.array (fuel + 155) (SourceJson.white (chunk0184Chars00 ++ (tail))) (chunk0183Push00 (chunk0182Push00 (chunk0181Push00 (chunk0180Push00 (chunk0179Push00 (chunk0178Push00 (chunk0177Push00 (acc)))))))) := array_chunk0183 fuel (chunk0184Chars00 ++ (tail)) (chunk0182Push00 (chunk0181Push00 (chunk0180Push00 (chunk0179Push00 (chunk0178Push00 (chunk0177Push00 (acc)))))))
    _ = SourceJson.array (fuel + 153) (SourceJson.white tail) (blockPush acc) := array_chunk0184 fuel (tail) (chunk0183Push00 (chunk0182Push00 (chunk0181Push00 (chunk0180Push00 (chunk0179Push00 (chunk0178Push00 (chunk0177Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 88053).take 3956 = blockChars := by rfl

theorem block_original_split : sourceRest 88053 = blockChars ++ sourceRest 92009 := by
  calc
    sourceRest 88053 = (sourceRest 88053).take 3956 ++ (sourceRest 88053).drop 3956 :=
      (List.take_append_drop 3956 (sourceRest 88053)).symm
    _ = blockChars ++ (sourceRest 88053).drop 3956 :=
      congrArg (fun part => part ++ (sourceRest 88053).drop 3956) block_original_prefix
    _ = blockChars ++ sourceRest 92009 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 88053 3956)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 169) (SourceJson.white (sourceRest 88053)) acc =
      SourceJson.array (fuel + 153) (SourceJson.white (sourceRest 92009)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 169) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 92009) acc)

#print axioms array_chunk0177
#print axioms array_chunk0178
#print axioms array_chunk0179
#print axioms array_chunk0180
#print axioms array_chunk0181
#print axioms array_chunk0182
#print axioms array_chunk0183
#print axioms array_chunk0184
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end Active8EnumerationBlock023

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
