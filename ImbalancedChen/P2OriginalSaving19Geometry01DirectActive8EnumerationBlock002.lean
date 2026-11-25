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

namespace Active8EnumerationBlock002

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0012_before_reader"
  err.flush

noncomputable def chunk0012Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '4', '6', '9', '0', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0012Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '4', '6', '9', '0', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 499) (SourceJson.white (chunk0012Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 497) (SourceJson.white tail) (chunk0012Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0012_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0013_before_reader"
  err.flush

noncomputable def chunk0013Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '2', '0', '7', '0', '3', '3', '6', '9', '/', '6', '7', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '2', '0', '7', '0', '3', '3', '6', '9', '/', '6', '7', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0013Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '2', '0', '7', '0', '3', '3', '6', '9', '/', '6', '7', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['8', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '2', '0', '7', '0', '3', '3', '6', '9', '/', '6', '7', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0013 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 497) (SourceJson.white (chunk0013Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 495) (SourceJson.white tail) (chunk0013Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0013_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_before_reader"
  err.flush

noncomputable def chunk0014Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '6', '5', '6', '2', '7', '/', '2', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '6', '5', '6', '2', '7', '/', '2', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0014Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['7', '5']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '6', '5', '6', '2', '7', '/', '2', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '6', '5', '6', '2', '7', '/', '2', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0014 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 495) (SourceJson.white (chunk0014Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 493) (SourceJson.white tail) (chunk0014Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_before_reader"
  err.flush

noncomputable def chunk0015Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '2', '3', '0', '9', '4', '0', '3', '/', '7', '4', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '5', '3', '/', '4', '5', '4', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0015Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '5', '3', '/', '4', '5', '4', '4']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '4']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '2', '3', '0', '9', '4', '0', '3', '/', '7', '4', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0015 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 493) (SourceJson.white (chunk0015Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 491) (SourceJson.white tail) (chunk0015Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_before_reader"
  err.flush

noncomputable def chunk0016Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '5', '3', '/', '4', '5', '4', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '8', '1', '/', '3', '5', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0016Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '8', '1', '/', '3', '5', '2']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '5', '3', '/', '4', '5', '4', '4']))]) :: (acc))

theorem array_chunk0016 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 491) (SourceJson.white (chunk0016Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 489) (SourceJson.white tail) (chunk0016Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0017_before_reader"
  err.flush

noncomputable def chunk0017Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '2', '3', '4', '4', '9', '/', '1', '1', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0017Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '8'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '2', '3', '4', '4', '9', '/', '1', '1', '5', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0017 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 489) (SourceJson.white (chunk0017Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 487) (SourceJson.white tail) (chunk0017Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0017_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_before_reader"
  err.flush

noncomputable def chunk0018Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '2', '4', '8', '4', '4', '6', '7', '/', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0018Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['8', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['3', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '2', '4', '8', '4', '4', '6', '7', '/', '8', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: (acc))

theorem array_chunk0018 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 487) (SourceJson.white (chunk0018Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 485) (SourceJson.white tail) (chunk0018Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_before_reader"
  err.flush

noncomputable def chunk0019Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '2', '4', '8', '4', '4', '6', '7', '/', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0019Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['3', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '2', '4', '8', '4', '4', '6', '7', '/', '8', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0019 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 485) (SourceJson.white (chunk0019Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 483) (SourceJson.white tail) (chunk0019Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0012Chars00 ++ chunk0013Chars00 ++ chunk0014Chars00 ++ chunk0015Chars00 ++ chunk0016Chars00 ++ chunk0017Chars00 ++ chunk0018Chars00 ++ chunk0019Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (chunk0015Push00 (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 499) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 483) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 499) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 499) (SourceJson.white (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 499) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 497) (SourceJson.white (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail))))))))) (chunk0012Push00 (acc)) := array_chunk0012 fuel (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 495) (SourceJson.white (chunk0014Chars00 ++ (chunk0015Chars00 ++ (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail)))))))) (chunk0013Push00 (chunk0012Push00 (acc))) := array_chunk0013 fuel (chunk0014Chars00 ++ (chunk0015Chars00 ++ (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail))))))) (chunk0012Push00 (acc))
    _ = SourceJson.array (fuel + 493) (SourceJson.white (chunk0015Chars00 ++ (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail))))))) (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (acc)))) := array_chunk0014 fuel (chunk0015Chars00 ++ (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail)))))) (chunk0013Push00 (chunk0012Push00 (acc)))
    _ = SourceJson.array (fuel + 491) (SourceJson.white (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail)))))) (chunk0015Push00 (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (acc))))) := array_chunk0015 fuel (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail))))) (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (acc))))
    _ = SourceJson.array (fuel + 489) (SourceJson.white (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail))))) (chunk0016Push00 (chunk0015Push00 (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (acc)))))) := array_chunk0016 fuel (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail)))) (chunk0015Push00 (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (acc)))))
    _ = SourceJson.array (fuel + 487) (SourceJson.white (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail)))) (chunk0017Push00 (chunk0016Push00 (chunk0015Push00 (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (acc))))))) := array_chunk0017 fuel (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail))) (chunk0016Push00 (chunk0015Push00 (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (acc))))))
    _ = SourceJson.array (fuel + 485) (SourceJson.white (chunk0019Chars00 ++ (tail))) (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (chunk0015Push00 (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (acc)))))))) := array_chunk0018 fuel (chunk0019Chars00 ++ (tail)) (chunk0017Push00 (chunk0016Push00 (chunk0015Push00 (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (acc)))))))
    _ = SourceJson.array (fuel + 483) (SourceJson.white tail) (blockPush acc) := array_chunk0019 fuel (tail) (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (chunk0015Push00 (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 6046).take 3909 = blockChars := by rfl

theorem block_original_split : sourceRest 6046 = blockChars ++ sourceRest 9955 := by
  calc
    sourceRest 6046 = (sourceRest 6046).take 3909 ++ (sourceRest 6046).drop 3909 :=
      (List.take_append_drop 3909 (sourceRest 6046)).symm
    _ = blockChars ++ (sourceRest 6046).drop 3909 :=
      congrArg (fun part => part ++ (sourceRest 6046).drop 3909) block_original_prefix
    _ = blockChars ++ sourceRest 9955 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 6046 3909)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 499) (SourceJson.white (sourceRest 6046)) acc =
      SourceJson.array (fuel + 483) (SourceJson.white (sourceRest 9955)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 499) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 9955) acc)

#print axioms array_chunk0012
#print axioms array_chunk0013
#print axioms array_chunk0014
#print axioms array_chunk0015
#print axioms array_chunk0016
#print axioms array_chunk0017
#print axioms array_chunk0018
#print axioms array_chunk0019
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end Active8EnumerationBlock002

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
