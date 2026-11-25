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

namespace Active8EnumerationBlock000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_before_reader"
  err.flush

noncomputable def chunk0000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0000Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '9'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: (acc))

theorem array_chunk0000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 523) (SourceJson.white (chunk0000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 521) (SourceJson.white tail) (chunk0000Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_before_reader"
  err.flush

noncomputable def chunk0001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0001Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['8', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7', '5'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: (acc))

theorem array_chunk0001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 521) (SourceJson.white (chunk0001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 519) (SourceJson.white tail) (chunk0001Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_before_reader"
  err.flush

noncomputable def chunk0002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '1', '/', '1', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0002Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['9', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['7', '5'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '1', '/', '1', '0', '0', '0', '0', '0', '0']))]) :: (acc))

theorem array_chunk0002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 519) (SourceJson.white (chunk0002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 517) (SourceJson.white tail) (chunk0002Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_before_reader"
  err.flush

noncomputable def chunk0003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'S', 'I', 'N', 'G', 'U', 'L', 'A', 'R', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 't', 'a', 't', 'u', 's', '"', ':', ' ', '"', 'I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'l', 'a', 'c', 'k', '"', ':', ' ', '"', '-', '8', '2', '8', '1', '3', '7', '/', '3', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0003Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['8', '3'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['I', 'N', 'F', 'E', 'A', 'S', 'I', 'B', 'L', 'E'])), (String.ofList ['v', 'i', 'o', 'l', 'a', 't', 'e', 'd', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'e', 'x'], .number (String.ofList ['1', '9'])), (String.ofList ['s', 'l', 'a', 'c', 'k'], .str (String.ofList ['-', '8', '2', '8', '1', '3', '7', '/', '3', '0', '0', '0', '0', '0', '0']))]) :: ((.obj [(String.ofList ['a', 'c', 't', 'i', 'v', 'e', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['7', '5'])]), (String.ofList ['s', 't', 'a', 't', 'u', 's'], .str (String.ofList ['S', 'I', 'N', 'G', 'U', 'L', 'A', 'R']))]) :: (acc))

theorem array_chunk0003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 517) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 515) (SourceJson.white tail) (chunk0003Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0000Chars00 ++ chunk0001Chars00 ++ chunk0002Chars00 ++ chunk0003Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 523) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 515) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0000Chars00 ++ (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (tail)))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 523) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 523) (SourceJson.white (chunk0000Chars00 ++ (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (tail)))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 523) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 521) (SourceJson.white (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (tail))))) (chunk0000Push00 (acc)) := array_chunk0000 fuel (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 519) (SourceJson.white (chunk0002Chars00 ++ (chunk0003Chars00 ++ (tail)))) (chunk0001Push00 (chunk0000Push00 (acc))) := array_chunk0001 fuel (chunk0002Chars00 ++ (chunk0003Chars00 ++ (tail))) (chunk0000Push00 (acc))
    _ = SourceJson.array (fuel + 517) (SourceJson.white (chunk0003Chars00 ++ (tail))) (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))) := array_chunk0002 fuel (chunk0003Chars00 ++ (tail)) (chunk0001Push00 (chunk0000Push00 (acc)))
    _ = SourceJson.array (fuel + 515) (SourceJson.white tail) (blockPush acc) := array_chunk0003 fuel (tail) (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 422).take 1727 = blockChars := by rfl

theorem block_original_split : sourceRest 422 = blockChars ++ sourceRest 2149 := by
  calc
    sourceRest 422 = (sourceRest 422).take 1727 ++ (sourceRest 422).drop 1727 :=
      (List.take_append_drop 1727 (sourceRest 422)).symm
    _ = blockChars ++ (sourceRest 422).drop 1727 :=
      congrArg (fun part => part ++ (sourceRest 422).drop 1727) block_original_prefix
    _ = blockChars ++ sourceRest 2149 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 422 1727)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 523) (SourceJson.white (sourceRest 422)) acc =
      SourceJson.array (fuel + 515) (SourceJson.white (sourceRest 2149)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 523) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 2149) acc)

#print axioms array_chunk0000
#print axioms array_chunk0001
#print axioms array_chunk0002
#print axioms array_chunk0003
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end Active8EnumerationBlock000

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
