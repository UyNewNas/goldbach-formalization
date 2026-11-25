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

namespace Active8EnumerationBlock021

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0161_before_reader"
  err.flush

noncomputable def chunk0161Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '4', '9', '6', '7', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '4', '9', '6', '7', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0161Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '4', '9', '6', '7', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '4', '9', '6', '7', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0161 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 201) (SourceJson.white (chunk0161Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 199) (SourceJson.white tail) (chunk0161Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0161_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0162_before_reader"
  err.flush

noncomputable def chunk0162Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '0', '9', '3', '5', '9', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '3', '9', '8', '3', '6', '0', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0162Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '3', '9', '8', '3', '6', '0', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '0', '9', '3', '5', '9', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0162 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 199) (SourceJson.white (chunk0162Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 197) (SourceJson.white tail) (chunk0162Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0162_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0163_before_reader"
  err.flush

noncomputable def chunk0163Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '2', '7', '9', '6', '4', '9', '9', '/', '4', '7', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0163Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '2', '7', '9', '6', '4', '9', '9', '/', '4', '7', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: (acc))

theorem array_chunk0163 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 197) (SourceJson.white (chunk0163Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 195) (SourceJson.white tail) (chunk0163Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0163_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0164_before_reader"
  err.flush

noncomputable def chunk0164Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '2', '9', '8', '4', '1', '8', '7', '/', '1', '8', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '7', '1', '8', '4', '3', '/', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0164Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '7', '1', '8', '4', '3', '/', '2', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '2', '9', '8', '4', '1', '8', '7', '/', '1', '8', '8', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0164 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 195) (SourceJson.white (chunk0164Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 193) (SourceJson.white tail) (chunk0164Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0164_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0165_before_reader"
  err.flush

noncomputable def chunk0165Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0165Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: (acc))

theorem array_chunk0165 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 193) (SourceJson.white (chunk0165Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 191) (SourceJson.white tail) (chunk0165Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0165_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0166_before_reader"
  err.flush

noncomputable def chunk0166Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '7', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '7', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0166Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['3', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '7', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['8', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['3', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '7', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0166 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 191) (SourceJson.white (chunk0166Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 189) (SourceJson.white tail) (chunk0166Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0166_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0167_before_reader"
  err.flush

noncomputable def chunk0167Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0167Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['8', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7', '5'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: (acc))

theorem array_chunk0167 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 189) (SourceJson.white (chunk0167Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 187) (SourceJson.white tail) (chunk0167Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0167_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0168_before_reader"
  err.flush

noncomputable def chunk0168Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0168Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7', '5'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0168 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 187) (SourceJson.white (chunk0168Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 185) (SourceJson.white tail) (chunk0168Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0168_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0161Chars00 ++ chunk0162Chars00 ++ chunk0163Chars00 ++ chunk0164Chars00 ++ chunk0165Chars00 ++ chunk0166Chars00 ++ chunk0167Chars00 ++ chunk0168Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0168Push00 (chunk0167Push00 (chunk0166Push00 (chunk0165Push00 (chunk0164Push00 (chunk0163Push00 (chunk0162Push00 (chunk0161Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 201) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 185) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0161Chars00 ++ (chunk0162Chars00 ++ (chunk0163Chars00 ++ (chunk0164Chars00 ++ (chunk0165Chars00 ++ (chunk0166Chars00 ++ (chunk0167Chars00 ++ (chunk0168Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 201) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 201) (SourceJson.white (chunk0161Chars00 ++ (chunk0162Chars00 ++ (chunk0163Chars00 ++ (chunk0164Chars00 ++ (chunk0165Chars00 ++ (chunk0166Chars00 ++ (chunk0167Chars00 ++ (chunk0168Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 201) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 199) (SourceJson.white (chunk0162Chars00 ++ (chunk0163Chars00 ++ (chunk0164Chars00 ++ (chunk0165Chars00 ++ (chunk0166Chars00 ++ (chunk0167Chars00 ++ (chunk0168Chars00 ++ (tail))))))))) (chunk0161Push00 (acc)) := array_chunk0161 fuel (chunk0162Chars00 ++ (chunk0163Chars00 ++ (chunk0164Chars00 ++ (chunk0165Chars00 ++ (chunk0166Chars00 ++ (chunk0167Chars00 ++ (chunk0168Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 197) (SourceJson.white (chunk0163Chars00 ++ (chunk0164Chars00 ++ (chunk0165Chars00 ++ (chunk0166Chars00 ++ (chunk0167Chars00 ++ (chunk0168Chars00 ++ (tail)))))))) (chunk0162Push00 (chunk0161Push00 (acc))) := array_chunk0162 fuel (chunk0163Chars00 ++ (chunk0164Chars00 ++ (chunk0165Chars00 ++ (chunk0166Chars00 ++ (chunk0167Chars00 ++ (chunk0168Chars00 ++ (tail))))))) (chunk0161Push00 (acc))
    _ = SourceJson.array (fuel + 195) (SourceJson.white (chunk0164Chars00 ++ (chunk0165Chars00 ++ (chunk0166Chars00 ++ (chunk0167Chars00 ++ (chunk0168Chars00 ++ (tail))))))) (chunk0163Push00 (chunk0162Push00 (chunk0161Push00 (acc)))) := array_chunk0163 fuel (chunk0164Chars00 ++ (chunk0165Chars00 ++ (chunk0166Chars00 ++ (chunk0167Chars00 ++ (chunk0168Chars00 ++ (tail)))))) (chunk0162Push00 (chunk0161Push00 (acc)))
    _ = SourceJson.array (fuel + 193) (SourceJson.white (chunk0165Chars00 ++ (chunk0166Chars00 ++ (chunk0167Chars00 ++ (chunk0168Chars00 ++ (tail)))))) (chunk0164Push00 (chunk0163Push00 (chunk0162Push00 (chunk0161Push00 (acc))))) := array_chunk0164 fuel (chunk0165Chars00 ++ (chunk0166Chars00 ++ (chunk0167Chars00 ++ (chunk0168Chars00 ++ (tail))))) (chunk0163Push00 (chunk0162Push00 (chunk0161Push00 (acc))))
    _ = SourceJson.array (fuel + 191) (SourceJson.white (chunk0166Chars00 ++ (chunk0167Chars00 ++ (chunk0168Chars00 ++ (tail))))) (chunk0165Push00 (chunk0164Push00 (chunk0163Push00 (chunk0162Push00 (chunk0161Push00 (acc)))))) := array_chunk0165 fuel (chunk0166Chars00 ++ (chunk0167Chars00 ++ (chunk0168Chars00 ++ (tail)))) (chunk0164Push00 (chunk0163Push00 (chunk0162Push00 (chunk0161Push00 (acc)))))
    _ = SourceJson.array (fuel + 189) (SourceJson.white (chunk0167Chars00 ++ (chunk0168Chars00 ++ (tail)))) (chunk0166Push00 (chunk0165Push00 (chunk0164Push00 (chunk0163Push00 (chunk0162Push00 (chunk0161Push00 (acc))))))) := array_chunk0166 fuel (chunk0167Chars00 ++ (chunk0168Chars00 ++ (tail))) (chunk0165Push00 (chunk0164Push00 (chunk0163Push00 (chunk0162Push00 (chunk0161Push00 (acc))))))
    _ = SourceJson.array (fuel + 187) (SourceJson.white (chunk0168Chars00 ++ (tail))) (chunk0167Push00 (chunk0166Push00 (chunk0165Push00 (chunk0164Push00 (chunk0163Push00 (chunk0162Push00 (chunk0161Push00 (acc)))))))) := array_chunk0167 fuel (chunk0168Chars00 ++ (tail)) (chunk0166Push00 (chunk0165Push00 (chunk0164Push00 (chunk0163Push00 (chunk0162Push00 (chunk0161Push00 (acc)))))))
    _ = SourceJson.array (fuel + 185) (SourceJson.white tail) (blockPush acc) := array_chunk0168 fuel (tail) (chunk0167Push00 (chunk0166Push00 (chunk0165Push00 (chunk0164Push00 (chunk0163Push00 (chunk0162Push00 (chunk0161Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 80231).take 3853 = blockChars := by rfl

theorem block_original_split : sourceRest 80231 = blockChars ++ sourceRest 84084 := by
  calc
    sourceRest 80231 = (sourceRest 80231).take 3853 ++ (sourceRest 80231).drop 3853 :=
      (List.take_append_drop 3853 (sourceRest 80231)).symm
    _ = blockChars ++ (sourceRest 80231).drop 3853 :=
      congrArg (fun part => part ++ (sourceRest 80231).drop 3853) block_original_prefix
    _ = blockChars ++ sourceRest 84084 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 80231 3853)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 201) (SourceJson.white (sourceRest 80231)) acc =
      SourceJson.array (fuel + 185) (SourceJson.white (sourceRest 84084)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 201) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 84084) acc)

#print axioms array_chunk0161
#print axioms array_chunk0162
#print axioms array_chunk0163
#print axioms array_chunk0164
#print axioms array_chunk0165
#print axioms array_chunk0166
#print axioms array_chunk0167
#print axioms array_chunk0168
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end Active8EnumerationBlock021

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
