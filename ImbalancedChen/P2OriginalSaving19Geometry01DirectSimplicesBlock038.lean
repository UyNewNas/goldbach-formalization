import ImbalancedChen.P2OriginalSaving19Geometry01DirectInput

/-! Original simplices grouped chunk transitions, including exact compact-input binding.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesBlock038

noncomputable def fragment0353711Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0353711Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0353711Field000Value00 : SourceJson := .number (String.ofList ['7', '5'])
noncomputable def fragment0353711Acc00100 : List (String × SourceJson) := (fragment0353711Field000Key00, fragment0353711Field000Value00) :: fragment0353711Acc00000
noncomputable def fragment0353711Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '5', ',']

theorem object_fragment0353711_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0353711Field000Chars00 ++ tail)) fragment0353711Acc00000 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0353711Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0353711_object_field_000"
  err.flush

noncomputable def fragment0353711Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0353711Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '4'])]
noncomputable def fragment0353711Acc00200 : List (String × SourceJson) := (fragment0353711Field001Key00, fragment0353711Field001Value00) :: fragment0353711Acc00100
noncomputable def fragment0353711Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0353711_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0353711Field001Chars00 ++ tail)) fragment0353711Acc00100 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0353711Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0353711_object_field_001"
  err.flush

noncomputable def fragment0353711Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0353711Field002Value00 : SourceJson := .str (String.ofList ['5', '2', '0', '9', '8', '5', '2', '8', '4', '8', '2', '9', '9', '2', '5', '4', '4', '7', '2', '7', '2', '7', '4', '2', '2', '8', '2', '2', '0', '0', '9', '5', '5', '2', '0', '1', '2', '3', '4', '1', '/', '1', '3', '5', '3', '5', '2', '8', '1', '6', '9', '0', '6', '5', '6', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0353711Acc00300 : List (String × SourceJson) := (fragment0353711Field002Key00, fragment0353711Field002Value00) :: fragment0353711Acc00200
noncomputable def fragment0353711Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '2', '0', '9', '8', '5', '2', '8', '4', '8', '2', '9', '9', '2', '5', '4', '4', '7', '2', '7', '2', '7', '4', '2', '2', '8', '2', '2', '0', '0', '9', '5', '5', '2', '0', '1', '2', '3', '4', '1', '/', '1', '3', '5', '3', '5', '2', '8', '1', '6', '9', '0', '6', '5', '6', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0353711_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0353711Field002Chars00 ++ tail)) fragment0353711Acc00200 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0353711Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0353711_object_field_002"
  err.flush

noncomputable def fragment0353711Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0353711Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0353711Acc00400 : List (String × SourceJson) := (fragment0353711Field003Key00, fragment0353711Field003Value00) :: fragment0353711Acc00300
noncomputable def fragment0353711Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0353711_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0353711Field003Chars00 ++ tail)) fragment0353711Acc00300 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0353711Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0353711_object_field_003"
  err.flush

noncomputable def fragment0353711Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0353711Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '3', '1', '/', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '6', '3', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0353711Acc00500 : List (String × SourceJson) := (fragment0353711Field004Key00, fragment0353711Field004Value00) :: fragment0353711Acc00400
noncomputable def fragment0353711Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '3', '1', '/', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '6', '3', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0353711_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0353711Field004Chars00 ++ tail)) fragment0353711Acc00400 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0353711Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0353711_object_field_004"
  err.flush

noncomputable def fragment0353711Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0353711Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '5', '9', '9', '4', '0', '6', '2', '4', '6', '3', '3', '/', '2', '3', '7', '6', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '2', '3', '0', '5', '8', '2', '4', '3', '9', '/', '1', '1', '8', '8', '4', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '3', '1', '3', '3', '8', '7', '7', '6', '9', '/', '1', '7', '8', '2', '6', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '3', '7', '6', '8', '8', '6', '9', '0', '3', '7', '/', '1', '1', '0', '9', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '0', '6', '0', '8', '9', '5', '8', '6', '2', '9', '7', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '0', '7', '6', '2', '1', '6', '9', '0', '6', '9', '/', '7', '1', '3', '0', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '7', '1', '6', '1', '0', '5', '7', '3', '4', '3', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '5', '3', '8', '5', '0', '9', '8', '0', '8', '7', '3', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '5', '3', '8', '4', '7', '6', '5', '3', '2', '1', '3', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '9', '1', '5', '5', '4', '9', '3', '3', '9', '1', '1', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0353711Acc00600 : List (String × SourceJson) := (fragment0353711Field005Key00, fragment0353711Field005Value00) :: fragment0353711Acc00500
noncomputable def fragment0353711Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '9', '4', '0', '6', '2', '4', '6', '3', '3', '/', '2', '3', '7', '6', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '2', '3', '0', '5', '8', '2', '4', '3', '9', '/', '1', '1', '8', '8', '4', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '3', '1', '3', '3', '8', '7', '7', '6', '9', '/', '1', '7', '8', '2', '6', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '3', '7', '6', '8', '8', '6', '9', '0', '3', '7', '/', '1', '1', '0', '9', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '0', '6', '0', '8', '9', '5', '8', '6', '2', '9', '7', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '0', '7', '6', '2', '1', '6', '9', '0', '6', '9', '/', '7', '1', '3', '0', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '0', '7', '1', '6', '1', '0', '5', '7', '3', '4', '3', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '5', '3', '8', '5', '0', '9', '8', '0', '8', '7', '3', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '5', '3', '8', '4', '7', '6', '5', '3', '2', '1', '3', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '9', '1', '5', '5', '4', '9', '3', '3', '9', '1', '1', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0353711_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0353711Field005Chars00 ++ tail)) fragment0353711Acc00500 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0353711Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0353711_object_field_005"
  err.flush

noncomputable def fragment0353711Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0353711Field006Value00 : SourceJson := .str (String.ofList ['5', '3', '5', '9', '3', '4', '5', '2', '6', '4', '1', '7', '8', '8', '4', '4', '3', '6', '6', '6', '4', '6', '2', '2', '0', '8', '5', '9', '2', '6', '1', '3', '3', '2', '3', '7', '5', '2', '9', '2', '0', '8', '0', '2', '9', '9', '/', '1', '0', '2', '0', '9', '2', '3', '0', '2', '0', '2', '9', '3', '2', '7', '3', '1', '5', '5', '8', '8', '0', '6', '7', '9', '9', '9', '2', '9', '9', '4', '3', '7', '3', '6', '1', '5', '7', '8', '4', '8', '3', '8', '5', '0', '9', '1', '9', '4', '2', '9', '4', '7', '2', '3', '9', '5', '3', '1', '2', '5', '0', '0', '0', '0'])
noncomputable def fragment0353711Acc00700 : List (String × SourceJson) := (fragment0353711Field006Key00, fragment0353711Field006Value00) :: fragment0353711Acc00600
noncomputable def fragment0353711Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '3', '5', '9', '3', '4', '5', '2', '6', '4', '1', '7', '8', '8', '4', '4', '3', '6', '6', '6', '4', '6', '2', '2', '0', '8', '5', '9', '2', '6', '1', '3', '3', '2', '3', '7', '5', '2', '9', '2', '0', '8', '0', '2', '9', '9', '/', '1', '0', '2', '0', '9', '2', '3', '0', '2', '0', '2', '9', '3', '2', '7', '3', '1', '5', '5', '8', '8', '0', '6', '7', '9', '9', '9', '2', '9', '9', '4', '3', '7', '3', '6', '1', '5', '7', '8', '4', '8', '3', '8', '5', '0', '9', '1', '9', '4', '2', '9', '4', '7', '2', '3', '9', '5', '3', '1', '2', '5', '0', '0', '0', '0', '"', ',']

theorem object_fragment0353711_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0353711Field006Chars00 ++ tail)) fragment0353711Acc00600 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0353711Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0353711_object_field_006"
  err.flush

noncomputable def fragment0353711Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0353711Field007Value00 : SourceJson := .str (String.ofList ['1', '3', '2', '1', '0', '3', '9', '7', '3', '5', '3', '7', '4', '3', '4', '8', '4', '6', '4', '7', '6', '8', '4', '6', '7', '7', '4', '0', '2', '8', '7', '2', '3', '1', '8', '0', '9', '0', '7', '5', '6', '4', '0', '6', '3', '5', '6', '1', '2', '1', '5', '6', '7', '2', '6', '9', '2', '8', '0', '5', '8', '3', '2', '9', '8', '4', '4', '8', '1', '3', '7', '2', '9', '6', '2', '7', '8', '4', '8', '2', '8', '5', '5', '2', '2', '4', '6', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '5', '6', '4', '5', '9', '7', '1', '4', '6', '5', '4', '2', '1', '0', '2', '6', '2', '4', '6', '4', '9', '7', '4', '7', '2', '4', '7', '1', '8', '8', '3', '1', '8', '9', '4', '8', '5', '3', '5', '7', '4', '9', '4', '5', '7', '7', '2', '4', '9', '6', '9', '7', '4', '1', '5', '9', '6', '3', '0', '7', '0', '6', '9', '4', '7', '6', '3', '6', '2', '6', '5', '3', '7', '8', '8', '2', '8', '1', '6', '3', '0', '1', '5', '2', '9', '5', '8', '8', '8', '8', '9', '1', '3', '6', '3', '3', '0', '6', '3', '6', '3', '2', '4', '9', '5', '5', '7', '0', '9', '4', '5', '8', '8', '5', '6', '2', '5', '3'])
noncomputable def fragment0353711Acc00800 : List (String × SourceJson) := (fragment0353711Field007Key00, fragment0353711Field007Value00) :: fragment0353711Acc00700
noncomputable def fragment0353711Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '2', '1', '0', '3', '9', '7', '3', '5', '3', '7', '4', '3', '4', '8', '4', '6', '4', '7', '6', '8', '4', '6', '7', '7', '4', '0', '2', '8', '7', '2', '3', '1', '8', '0', '9', '0', '7', '5', '6', '4', '0', '6', '3', '5', '6', '1', '2', '1', '5', '6', '7', '2', '6', '9', '2', '8', '0', '5', '8', '3', '2', '9', '8', '4', '4', '8', '1', '3', '7', '2', '9', '6', '2', '7', '8', '4', '8', '2', '8', '5', '5', '2', '2', '4', '6', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '5', '6', '4', '5', '9', '7', '1', '4', '6', '5', '4', '2', '1', '0', '2', '6', '2', '4', '6', '4', '9', '7', '4', '7', '2', '4', '7', '1', '8', '8', '3', '1', '8', '9', '4', '8', '5', '3', '5', '7', '4', '9', '4', '5', '7', '7', '2', '4', '9', '6', '9', '7', '4', '1', '5', '9', '6', '3', '0', '7', '0', '6', '9', '4', '7', '6', '3', '6', '2', '6', '5', '3', '7', '8', '8', '2', '8', '1', '6', '3', '0', '1', '5', '2', '9', '5', '8', '8', '8', '8', '9', '1', '3', '6', '3', '3', '0', '6', '3', '6', '3', '2', '4', '9', '5', '5', '7', '0', '9', '4', '5', '8', '8', '5', '6', '2', '5', '3', '"', ',']

theorem object_fragment0353711_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0353711Field007Chars00 ++ tail)) fragment0353711Acc00700 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0353711Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0353711_object_field_007"
  err.flush

noncomputable def fragment0353711Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0353711Field008Value00 : SourceJson := .str (String.ofList ['4', '1', '5', '9', '0', '9', '0', '0', '5', '0', '0'])
noncomputable def fragment0353711Acc00900 : List (String × SourceJson) := (fragment0353711Field008Key00, fragment0353711Field008Value00) :: fragment0353711Acc00800
noncomputable def fragment0353711Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '1', '5', '9', '0', '9', '0', '0', '5', '0', '0', '"', ',']

theorem object_fragment0353711_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0353711Field008Chars00 ++ tail)) fragment0353711Acc00800 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0353711Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0353711_object_field_008"
  err.flush

noncomputable def fragment0353711Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0353711Field009Value00 : SourceJson := .str (String.ofList ['2', '2', '9', '2', '9', '4', '1', '6', '8', '7', '5', '5'])
noncomputable def fragment0353711Acc01000 : List (String × SourceJson) := (fragment0353711Field009Key00, fragment0353711Field009Value00) :: fragment0353711Acc00900
noncomputable def fragment0353711Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '9', '2', '9', '4', '1', '6', '8', '7', '5', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0353711_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0353711Field009Chars00 ++ tail)) fragment0353711Acc00900 =
      .ok (.obj (fragment0353711Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0353711_object_field_009"
  err.flush

noncomputable def fragment0353711Chars : List Char := '{' :: (fragment0353711Field000Chars00 ++ fragment0353711Field001Chars00 ++ fragment0353711Field002Chars00 ++ fragment0353711Field003Chars00 ++ fragment0353711Field004Chars00 ++ fragment0353711Field005Chars00 ++ fragment0353711Field006Chars00 ++ fragment0353711Field007Chars00 ++ fragment0353711Field008Chars00 ++ fragment0353711Field009Chars00)
noncomputable def fragment0353711Value : SourceJson := .obj (fragment0353711Acc01000.reverse)

theorem value_fragment0353711 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 233) (fragment0353711Chars ++ tail) =
      .ok (fragment0353711Value, tail) := by
  have hinput : fragment0353711Chars ++ tail = '{' :: (fragment0353711Field000Chars00 ++ (fragment0353711Field001Chars00 ++ (fragment0353711Field002Chars00 ++ (fragment0353711Field003Chars00 ++ (fragment0353711Field004Chars00 ++ (fragment0353711Field005Chars00 ++ (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0353711Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 233) (fragment0353711Chars ++ tail) =
        SourceJson.value (fuel + 233) ('{' :: (fragment0353711Field000Chars00 ++ (fragment0353711Field001Chars00 ++ (fragment0353711Field002Chars00 ++ (fragment0353711Field003Chars00 ++ (fragment0353711Field004Chars00 ++ (fragment0353711Field005Chars00 ++ (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 233)) hinput
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0353711Field000Chars00 ++ (fragment0353711Field001Chars00 ++ (fragment0353711Field002Chars00 ++ (fragment0353711Field003Chars00 ++ (fragment0353711Field004Chars00 ++ (fragment0353711Field005Chars00 ++ (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail)))))))))))) fragment0353711Acc00000 := by rfl
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0353711Field001Chars00 ++ (fragment0353711Field002Chars00 ++ (fragment0353711Field003Chars00 ++ (fragment0353711Field004Chars00 ++ (fragment0353711Field005Chars00 ++ (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail))))))))))) fragment0353711Acc00100 := object_fragment0353711_field_000 fuel (fragment0353711Field001Chars00 ++ (fragment0353711Field002Chars00 ++ (fragment0353711Field003Chars00 ++ (fragment0353711Field004Chars00 ++ (fragment0353711Field005Chars00 ++ (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0353711Field002Chars00 ++ (fragment0353711Field003Chars00 ++ (fragment0353711Field004Chars00 ++ (fragment0353711Field005Chars00 ++ (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail)))))))))) fragment0353711Acc00200 := object_fragment0353711_field_001 fuel (fragment0353711Field002Chars00 ++ (fragment0353711Field003Chars00 ++ (fragment0353711Field004Chars00 ++ (fragment0353711Field005Chars00 ++ (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0353711Field003Chars00 ++ (fragment0353711Field004Chars00 ++ (fragment0353711Field005Chars00 ++ (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail))))))))) fragment0353711Acc00300 := object_fragment0353711_field_002 fuel (fragment0353711Field003Chars00 ++ (fragment0353711Field004Chars00 ++ (fragment0353711Field005Chars00 ++ (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0353711Field004Chars00 ++ (fragment0353711Field005Chars00 ++ (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail)))))))) fragment0353711Acc00400 := object_fragment0353711_field_003 fuel (fragment0353711Field004Chars00 ++ (fragment0353711Field005Chars00 ++ (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0353711Field005Chars00 ++ (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail))))))) fragment0353711Acc00500 := object_fragment0353711_field_004 fuel (fragment0353711Field005Chars00 ++ (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail)))))) fragment0353711Acc00600 := object_fragment0353711_field_005 fuel (fragment0353711Field006Chars00 ++ (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail))))) fragment0353711Acc00700 := object_fragment0353711_field_006 fuel (fragment0353711Field007Chars00 ++ (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail)))) fragment0353711Acc00800 := object_fragment0353711_field_007 fuel (fragment0353711Field008Chars00 ++ (fragment0353711Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0353711Field009Chars00 ++ (tail))) fragment0353711Acc00900 := object_fragment0353711_field_008 fuel (fragment0353711Field009Chars00 ++ (tail))
    _ = .ok (fragment0353711Value, tail) := object_fragment0353711_field_009 fuel (tail)

noncomputable def fragment0355293Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0355293Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0355293Field000Value00 : SourceJson := .number (String.ofList ['7', '6'])
noncomputable def fragment0355293Acc00100 : List (String × SourceJson) := (fragment0355293Field000Key00, fragment0355293Field000Value00) :: fragment0355293Acc00000
noncomputable def fragment0355293Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '6', ',']

theorem object_fragment0355293_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 269) (SourceJson.white (fragment0355293Field000Chars00 ++ tail)) fragment0355293Acc00000 =
      SourceJson.object (fuel + 268) (SourceJson.white tail) fragment0355293Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0355293_object_field_000"
  err.flush

noncomputable def fragment0355293Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0355293Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6'])]
noncomputable def fragment0355293Acc00200 : List (String × SourceJson) := (fragment0355293Field001Key00, fragment0355293Field001Value00) :: fragment0355293Acc00100
noncomputable def fragment0355293Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0355293_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 268) (SourceJson.white (fragment0355293Field001Chars00 ++ tail)) fragment0355293Acc00100 =
      SourceJson.object (fuel + 267) (SourceJson.white tail) fragment0355293Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0355293_object_field_001"
  err.flush

noncomputable def fragment0355293Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0355293Field002Value00 : SourceJson := .str (String.ofList ['5', '2', '0', '5', '7', '4', '6', '6', '3', '4', '7', '1', '2', '2', '1', '2', '2', '1', '4', '5', '2', '1', '0', '4', '2', '7', '2', '8', '8', '6', '4', '3', '1', '6', '8', '4', '1', '2', '3', '7', '/', '7', '2', '8', '3', '6', '4', '4', '2', '4', '9', '4', '4', '8', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0355293Acc00300 : List (String × SourceJson) := (fragment0355293Field002Key00, fragment0355293Field002Value00) :: fragment0355293Acc00200
noncomputable def fragment0355293Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '2', '0', '5', '7', '4', '6', '6', '3', '4', '7', '1', '2', '2', '1', '2', '2', '1', '4', '5', '2', '1', '0', '4', '2', '7', '2', '8', '8', '6', '4', '3', '1', '6', '8', '4', '1', '2', '3', '7', '/', '7', '2', '8', '3', '6', '4', '4', '2', '4', '9', '4', '4', '8', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0355293_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 267) (SourceJson.white (fragment0355293Field002Chars00 ++ tail)) fragment0355293Acc00200 =
      SourceJson.object (fuel + 266) (SourceJson.white tail) fragment0355293Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0355293_object_field_002"
  err.flush

noncomputable def fragment0355293Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0355293Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0355293Acc00400 : List (String × SourceJson) := (fragment0355293Field003Key00, fragment0355293Field003Value00) :: fragment0355293Acc00300
noncomputable def fragment0355293Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0355293_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 266) (SourceJson.white (fragment0355293Field003Chars00 ++ tail)) fragment0355293Acc00300 =
      SourceJson.object (fuel + 265) (SourceJson.white tail) fragment0355293Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0355293_object_field_003"
  err.flush

noncomputable def fragment0355293Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0355293Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '7', '7', '8', '1', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0355293Acc00500 : List (String × SourceJson) := (fragment0355293Field004Key00, fragment0355293Field004Value00) :: fragment0355293Acc00400
noncomputable def fragment0355293Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '7', '7', '8', '1', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0355293_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 265) (SourceJson.white (fragment0355293Field004Chars00 ++ tail)) fragment0355293Acc00400 =
      SourceJson.object (fuel + 264) (SourceJson.white tail) fragment0355293Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0355293_object_field_004"
  err.flush

noncomputable def fragment0355293Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0355293Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '0', '0', '4', '4', '9', '7', '4', '5', '9', '8', '7', '6', '1', '/', '1', '8', '3', '4', '0', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '3', '8', '7', '4', '3', '6', '0', '7', '1', '3', '3', '1', '/', '1', '8', '3', '4', '0', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '0', '7', '4', '6', '2', '5', '0', '0', '9', '4', '1', '5', '1', '/', '2', '7', '5', '1', '0', '6', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '5', '5', '8', '8', '2', '2', '6', '6', '6', '7', '3', '/', '1', '2', '2', '2', '6', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '8', '3', '1', '6', '9', '6', '3', '3', '8', '4', '5', '1', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '1', '8', '1', '9', '6', '0', '0', '4', '1', '9', '3', '/', '2', '7', '5', '1', '0', '6', '5', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '6', '3', '4', '6', '2', '1', '4', '3', '5', '9', '/', '1', '8', '0', '9', '9', '1', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '9', '5', '7', '5', '6', '4', '5', '1', '0', '8', '1', '2', '3', '/', '2', '7', '5', '1', '0', '6', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '6', '0', '4', '4', '6', '7', '1', '7', '0', '9', '8', '7', '7', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '6', '0', '4', '3', '5', '7', '1', '2', '8', '3', '8', '3', '7', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0355293Acc00600 : List (String × SourceJson) := (fragment0355293Field005Key00, fragment0355293Field005Value00) :: fragment0355293Acc00500
noncomputable def fragment0355293Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '0', '4', '4', '9', '7', '4', '5', '9', '8', '7', '6', '1', '/', '1', '8', '3', '4', '0', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '3', '8', '7', '4', '3', '6', '0', '7', '1', '3', '3', '1', '/', '1', '8', '3', '4', '0', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '0', '7', '4', '6', '2', '5', '0', '0', '9', '4', '1', '5', '1', '/', '2', '7', '5', '1', '0', '6', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '5', '5', '8', '8', '2', '2', '6', '6', '6', '7', '3', '/', '1', '2', '2', '2', '6', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '8', '3', '1', '6', '9', '6', '3', '3', '8', '4', '5', '1', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '1', '8', '1', '9', '6', '0', '0', '4', '1', '9', '3', '/', '2', '7', '5', '1', '0', '6', '5', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '6', '3', '4', '6', '2', '1', '4', '3', '5', '9', '/', '1', '8', '0', '9', '9', '1', '1', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '5', '7', '5', '6', '4', '5', '1', '0', '8', '1', '2', '3', '/', '2', '7', '5', '1', '0', '6', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '6', '0', '4', '4', '6', '7', '1', '7', '0', '9', '8', '7', '7', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '6', '0', '4', '3', '5', '7', '1', '2', '8', '3', '8', '3', '7', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0355293_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment0355293Field005Chars00 ++ tail)) fragment0355293Acc00500 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment0355293Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0355293_object_field_005"
  err.flush

noncomputable def fragment0355293Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0355293Field006Value00 : SourceJson := .str (String.ofList ['1', '5', '8', '4', '4', '2', '8', '8', '5', '4', '3', '6', '0', '9', '6', '0', '9', '7', '7', '9', '2', '9', '9', '4', '6', '3', '4', '6', '5', '2', '1', '2', '3', '6', '7', '7', '0', '2', '7', '4', '1', '5', '5', '1', '7', '5', '5', '0', '0', '/', '1', '9', '3', '0', '8', '5', '9', '4', '2', '4', '8', '7', '3', '5', '0', '9', '0', '8', '1', '9', '4', '3', '6', '1', '4', '7', '1', '8', '0', '5', '3', '0', '1', '9', '3', '2', '0', '0', '8', '7', '4', '0', '0', '7', '4', '7', '0', '0', '7', '0', '3', '6', '3', '8', '4', '3', '4', '5', '0', '3', '8', '0', '5', '8', '6', '4', '7', '1'])
noncomputable def fragment0355293Acc00700 : List (String × SourceJson) := (fragment0355293Field006Key00, fragment0355293Field006Value00) :: fragment0355293Acc00600
noncomputable def fragment0355293Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '8', '4', '4', '2', '8', '8', '5', '4', '3', '6', '0', '9', '6', '0', '9', '7', '7', '9', '2', '9', '9', '4', '6', '3', '4', '6', '5', '2', '1', '2', '3', '6', '7', '7', '0', '2', '7', '4', '1', '5', '5', '1', '7', '5', '5', '0', '0', '/', '1', '9', '3', '0', '8', '5', '9', '4', '2', '4', '8', '7', '3', '5', '0', '9', '0', '8', '1', '9', '4', '3', '6', '1', '4', '7', '1', '8', '0', '5', '3', '0', '1', '9', '3', '2', '0', '0', '8', '7', '4', '0', '0', '7', '4', '7', '0', '0', '7', '0', '3', '6', '3', '8', '4', '3', '4', '5', '0', '3', '8', '0', '5', '8', '6', '4', '7', '1', '"', ',']

theorem object_fragment0355293_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0355293Field006Chars00 ++ tail)) fragment0355293Acc00600 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0355293Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0355293_object_field_006"
  err.flush

noncomputable def fragment0355293Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0355293Field007Value00 : SourceJson := .str (String.ofList ['1', '5', '3', '1', '2', '4', '2', '3', '5', '0', '4', '6', '2', '0', '1', '7', '2', '2', '0', '3', '4', '4', '8', '6', '9', '0', '2', '9', '5', '4', '4', '4', '7', '5', '3', '9', '6', '8', '7', '2', '4', '9', '3', '1', '5', '3', '9', '7', '1', '5', '1', '6', '6', '6', '2', '9', '9', '3', '0', '5', '9', '9', '0', '2', '8', '9', '3', '1', '1', '3', '5', '1', '6', '4', '5', '8', '6', '6', '0', '1', '9', '1', '2', '4', '4', '9', '1', '8', '1', '7', '3', '5', '2', '9', '0', '3', '3', '2', '5', '7', '3', '5', '5', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '2', '3', '4', '1', '2', '3', '0', '8', '6', '6', '7', '1', '1', '5', '6', '1', '2', '6', '1', '7', '9', '5', '0', '3', '5', '9', '0', '6', '6', '5', '1', '3', '9', '0', '5', '2', '6', '9', '2', '8', '3', '3', '3', '0', '3', '4', '0', '7', '4', '5', '1', '8', '3', '7', '7', '0', '6', '0', '6', '4', '1', '8', '4', '9', '1', '7', '2', '9', '6', '4', '0', '2', '2', '8', '2', '3', '7', '9', '7', '9', '6', '6', '1', '6', '7', '3', '2', '4', '3', '7', '6', '3', '8', '5', '7', '6', '4', '9', '6', '0', '4', '7', '1', '9', '1', '9', '1', '4', '9', '9', '2', '0', '8', '9', '5', '1', '3', '3', '7', '0', '1', '4', '7', '6', '3', '5', '9', '3', '0', '2', '4', '1', '6', '7', '3', '0', '7'])
noncomputable def fragment0355293Acc00800 : List (String × SourceJson) := (fragment0355293Field007Key00, fragment0355293Field007Value00) :: fragment0355293Acc00700
noncomputable def fragment0355293Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '3', '1', '2', '4', '2', '3', '5', '0', '4', '6', '2', '0', '1', '7', '2', '2', '0', '3', '4', '4', '8', '6', '9', '0', '2', '9', '5', '4', '4', '4', '7', '5', '3', '9', '6', '8', '7', '2', '4', '9', '3', '1', '5', '3', '9', '7', '1', '5', '1', '6', '6', '6', '2', '9', '9', '3', '0', '5', '9', '9', '0', '2', '8', '9', '3', '1', '1', '3', '5', '1', '6', '4', '5', '8', '6', '6', '0', '1', '9', '1', '2', '4', '4', '9', '1', '8', '1', '7', '3', '5', '2', '9', '0', '3', '3', '2', '5', '7', '3', '5', '5', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '2', '3', '4', '1', '2', '3', '0', '8', '6', '6', '7', '1', '1', '5', '6', '1', '2', '6', '1', '7', '9', '5', '0', '3', '5', '9', '0', '6', '6', '5', '1', '3', '9', '0', '5', '2', '6', '9', '2', '8', '3', '3', '3', '0', '3', '4', '0', '7', '4', '5', '1', '8', '3', '7', '7', '0', '6', '0', '6', '4', '1', '8', '4', '9', '1', '7', '2', '9', '6', '4', '0', '2', '2', '8', '2', '3', '7', '9', '7', '9', '6', '6', '1', '6', '7', '3', '2', '4', '3', '7', '6', '3', '8', '5', '7', '6', '4', '9', '6', '0', '4', '7', '1', '9', '1', '9', '1', '4', '9', '9', '2', '0', '8', '9', '5', '1', '3', '3', '7', '0', '1', '4', '7', '6', '3', '5', '9', '3', '0', '2', '4', '1', '6', '7', '3', '0', '7', '"', ',']

theorem object_fragment0355293_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0355293Field007Chars00 ++ tail)) fragment0355293Acc00700 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0355293Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0355293_object_field_007"
  err.flush

noncomputable def fragment0355293Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0355293Field008Value00 : SourceJson := .str (String.ofList ['6', '5', '0', '1', '3', '2', '1', '9', '0', '6'])
noncomputable def fragment0355293Acc00900 : List (String × SourceJson) := (fragment0355293Field008Key00, fragment0355293Field008Value00) :: fragment0355293Acc00800
noncomputable def fragment0355293Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '5', '0', '1', '3', '2', '1', '9', '0', '6', '"', ',']

theorem object_fragment0355293_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0355293Field008Chars00 ++ tail)) fragment0355293Acc00800 =
      SourceJson.object (fuel + 260) (SourceJson.white tail) fragment0355293Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0355293_object_field_008"
  err.flush

noncomputable def fragment0355293Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0355293Field009Value00 : SourceJson := .str (String.ofList ['3', '7', '5', '1', '1', '7', '1', '9', '4', '1', '8'])
noncomputable def fragment0355293Acc01000 : List (String × SourceJson) := (fragment0355293Field009Key00, fragment0355293Field009Value00) :: fragment0355293Acc00900
noncomputable def fragment0355293Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '7', '5', '1', '1', '7', '1', '9', '4', '1', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0355293_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0355293Field009Chars00 ++ tail)) fragment0355293Acc00900 =
      .ok (.obj (fragment0355293Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0355293_object_field_009"
  err.flush

noncomputable def fragment0355293Chars : List Char := '{' :: (fragment0355293Field000Chars00 ++ fragment0355293Field001Chars00 ++ fragment0355293Field002Chars00 ++ fragment0355293Field003Chars00 ++ fragment0355293Field004Chars00 ++ fragment0355293Field005Chars00 ++ fragment0355293Field006Chars00 ++ fragment0355293Field007Chars00 ++ fragment0355293Field008Chars00 ++ fragment0355293Field009Chars00)
noncomputable def fragment0355293Value : SourceJson := .obj (fragment0355293Acc01000.reverse)

theorem value_fragment0355293 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 270) (fragment0355293Chars ++ tail) =
      .ok (fragment0355293Value, tail) := by
  have hinput : fragment0355293Chars ++ tail = '{' :: (fragment0355293Field000Chars00 ++ (fragment0355293Field001Chars00 ++ (fragment0355293Field002Chars00 ++ (fragment0355293Field003Chars00 ++ (fragment0355293Field004Chars00 ++ (fragment0355293Field005Chars00 ++ (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0355293Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 270) (fragment0355293Chars ++ tail) =
        SourceJson.value (fuel + 270) ('{' :: (fragment0355293Field000Chars00 ++ (fragment0355293Field001Chars00 ++ (fragment0355293Field002Chars00 ++ (fragment0355293Field003Chars00 ++ (fragment0355293Field004Chars00 ++ (fragment0355293Field005Chars00 ++ (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 270)) hinput
    _ = SourceJson.object (fuel + 269) (SourceJson.white (fragment0355293Field000Chars00 ++ (fragment0355293Field001Chars00 ++ (fragment0355293Field002Chars00 ++ (fragment0355293Field003Chars00 ++ (fragment0355293Field004Chars00 ++ (fragment0355293Field005Chars00 ++ (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail)))))))))))) fragment0355293Acc00000 := by rfl
    _ = SourceJson.object (fuel + 268) (SourceJson.white (fragment0355293Field001Chars00 ++ (fragment0355293Field002Chars00 ++ (fragment0355293Field003Chars00 ++ (fragment0355293Field004Chars00 ++ (fragment0355293Field005Chars00 ++ (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail))))))))))) fragment0355293Acc00100 := object_fragment0355293_field_000 fuel (fragment0355293Field001Chars00 ++ (fragment0355293Field002Chars00 ++ (fragment0355293Field003Chars00 ++ (fragment0355293Field004Chars00 ++ (fragment0355293Field005Chars00 ++ (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 267) (SourceJson.white (fragment0355293Field002Chars00 ++ (fragment0355293Field003Chars00 ++ (fragment0355293Field004Chars00 ++ (fragment0355293Field005Chars00 ++ (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail)))))))))) fragment0355293Acc00200 := object_fragment0355293_field_001 fuel (fragment0355293Field002Chars00 ++ (fragment0355293Field003Chars00 ++ (fragment0355293Field004Chars00 ++ (fragment0355293Field005Chars00 ++ (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 266) (SourceJson.white (fragment0355293Field003Chars00 ++ (fragment0355293Field004Chars00 ++ (fragment0355293Field005Chars00 ++ (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail))))))))) fragment0355293Acc00300 := object_fragment0355293_field_002 fuel (fragment0355293Field003Chars00 ++ (fragment0355293Field004Chars00 ++ (fragment0355293Field005Chars00 ++ (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 265) (SourceJson.white (fragment0355293Field004Chars00 ++ (fragment0355293Field005Chars00 ++ (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail)))))))) fragment0355293Acc00400 := object_fragment0355293_field_003 fuel (fragment0355293Field004Chars00 ++ (fragment0355293Field005Chars00 ++ (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment0355293Field005Chars00 ++ (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail))))))) fragment0355293Acc00500 := object_fragment0355293_field_004 fuel (fragment0355293Field005Chars00 ++ (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail)))))) fragment0355293Acc00600 := object_fragment0355293_field_005 fuel (fragment0355293Field006Chars00 ++ (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail))))) fragment0355293Acc00700 := object_fragment0355293_field_006 fuel (fragment0355293Field007Chars00 ++ (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail)))) fragment0355293Acc00800 := object_fragment0355293_field_007 fuel (fragment0355293Field008Chars00 ++ (fragment0355293Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0355293Field009Chars00 ++ (tail))) fragment0355293Acc00900 := object_fragment0355293_field_008 fuel (fragment0355293Field009Chars00 ++ (tail))
    _ = .ok (fragment0355293Value, tail) := object_fragment0355293_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0075_before_reader"
  err.flush

noncomputable def chunk0075LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0075SuffixChars00 : List Char := [',']
noncomputable def chunk0075Chars00 : List Char := chunk0075LeadChars00 ++ fragment0353711Chars ++ chunk0075SuffixChars00
noncomputable def chunk0075Push00 (acc : List SourceJson) : List SourceJson := fragment0353711Value :: acc

noncomputable def chunk0075AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0075_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 529)
      (SourceJson.white (chunk0075LeadChars00 ++ (fragment0353711Chars ++ rest))) acc =
      (SourceJson.value (fuel + 528) (fragment0353711Chars ++ rest)).bind
        (chunk0075AfterValue00 (fuel + 528) acc) := by rfl

theorem array_chunk0075 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 529) (SourceJson.white (chunk0075Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 528) (SourceJson.white tail) (chunk0075Push00 acc) := by
  have hinput : chunk0075Chars00 ++ tail = chunk0075LeadChars00 ++ (fragment0353711Chars ++ (chunk0075SuffixChars00 ++ tail)) := by
    simp only [chunk0075Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 529) (SourceJson.white (chunk0075Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 529)
          (SourceJson.white (chunk0075LeadChars00 ++ (fragment0353711Chars ++ (chunk0075SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 529) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 528) (fragment0353711Chars ++ (chunk0075SuffixChars00 ++ tail))).bind
        (chunk0075AfterValue00 (fuel + 528) acc) := array_chunk0075_head fuel (chunk0075SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0353711Value, chunk0075SuffixChars00 ++ tail)).bind
        (chunk0075AfterValue00 (fuel + 528) acc) :=
      congrArg (fun result => result.bind (chunk0075AfterValue00 (fuel + 528) acc))
        (value_fragment0353711 (fuel + 295) (chunk0075SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 528) (SourceJson.white tail) (chunk0075Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0075_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0076_before_reader"
  err.flush

noncomputable def chunk0076LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0076SuffixChars00 : List Char := [',']
noncomputable def chunk0076Chars00 : List Char := chunk0076LeadChars00 ++ fragment0355293Chars ++ chunk0076SuffixChars00
noncomputable def chunk0076Push00 (acc : List SourceJson) : List SourceJson := fragment0355293Value :: acc

noncomputable def chunk0076AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0076_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 528)
      (SourceJson.white (chunk0076LeadChars00 ++ (fragment0355293Chars ++ rest))) acc =
      (SourceJson.value (fuel + 527) (fragment0355293Chars ++ rest)).bind
        (chunk0076AfterValue00 (fuel + 527) acc) := by rfl

theorem array_chunk0076 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 528) (SourceJson.white (chunk0076Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 527) (SourceJson.white tail) (chunk0076Push00 acc) := by
  have hinput : chunk0076Chars00 ++ tail = chunk0076LeadChars00 ++ (fragment0355293Chars ++ (chunk0076SuffixChars00 ++ tail)) := by
    simp only [chunk0076Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 528) (SourceJson.white (chunk0076Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 528)
          (SourceJson.white (chunk0076LeadChars00 ++ (fragment0355293Chars ++ (chunk0076SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 528) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 527) (fragment0355293Chars ++ (chunk0076SuffixChars00 ++ tail))).bind
        (chunk0076AfterValue00 (fuel + 527) acc) := array_chunk0076_head fuel (chunk0076SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0355293Value, chunk0076SuffixChars00 ++ tail)).bind
        (chunk0076AfterValue00 (fuel + 527) acc) :=
      congrArg (fun result => result.bind (chunk0076AfterValue00 (fuel + 527) acc))
        (value_fragment0355293 (fuel + 257) (chunk0076SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 527) (SourceJson.white tail) (chunk0076Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0076_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0075Chars00 ++ chunk0076Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0076Push00 (chunk0075Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 529) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 527) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0075Chars00 ++ (chunk0076Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 529) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 529) (SourceJson.white (chunk0075Chars00 ++ (chunk0076Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 529) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 528) (SourceJson.white (chunk0076Chars00 ++ (tail))) (chunk0075Push00 (acc)) := array_chunk0075 fuel (chunk0076Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 527) (SourceJson.white tail) (blockPush acc) := array_chunk0076 fuel (tail) (chunk0075Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 353705).take 3264 = blockChars := by rfl

theorem block_original_split : sourceRest 353705 = blockChars ++ sourceRest 356969 := by
  calc
    sourceRest 353705 = (sourceRest 353705).take 3264 ++ (sourceRest 353705).drop 3264 :=
      (List.take_append_drop 3264 (sourceRest 353705)).symm
    _ = blockChars ++ (sourceRest 353705).drop 3264 :=
      congrArg (fun part => part ++ (sourceRest 353705).drop 3264) block_original_prefix
    _ = blockChars ++ sourceRest 356969 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 353705 3264)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 529) (SourceJson.white (sourceRest 353705)) acc =
      SourceJson.array (fuel + 527) (SourceJson.white (sourceRest 356969)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 529) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 356969) acc)

#print axioms object_fragment0353711_field_000
#print axioms object_fragment0353711_field_001
#print axioms object_fragment0353711_field_002
#print axioms object_fragment0353711_field_003
#print axioms object_fragment0353711_field_004
#print axioms object_fragment0353711_field_005
#print axioms object_fragment0353711_field_006
#print axioms object_fragment0353711_field_007
#print axioms object_fragment0353711_field_008
#print axioms object_fragment0353711_field_009
#print axioms value_fragment0353711
#print axioms object_fragment0355293_field_000
#print axioms object_fragment0355293_field_001
#print axioms object_fragment0355293_field_002
#print axioms object_fragment0355293_field_003
#print axioms object_fragment0355293_field_004
#print axioms object_fragment0355293_field_005
#print axioms object_fragment0355293_field_006
#print axioms object_fragment0355293_field_007
#print axioms object_fragment0355293_field_008
#print axioms object_fragment0355293_field_009
#print axioms value_fragment0355293
#print axioms array_chunk0075_head
#print axioms array_chunk0075
#print axioms array_chunk0076_head
#print axioms array_chunk0076
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock038

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
