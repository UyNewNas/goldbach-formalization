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

namespace SimplicesBlock043

noncomputable def fragment0370096Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0370096Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0370096Field000Value00 : SourceJson := .number (String.ofList ['8', '5'])
noncomputable def fragment0370096Acc00100 : List (String × SourceJson) := (fragment0370096Field000Key00, fragment0370096Field000Value00) :: fragment0370096Acc00000
noncomputable def fragment0370096Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '5', ',']

theorem object_fragment0370096_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0370096Field000Chars00 ++ tail)) fragment0370096Acc00000 =
      SourceJson.object (fuel + 212) (SourceJson.white tail) fragment0370096Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0370096_object_field_000"
  err.flush

noncomputable def fragment0370096Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0370096Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0370096Acc00200 : List (String × SourceJson) := (fragment0370096Field001Key00, fragment0370096Field001Value00) :: fragment0370096Acc00100
noncomputable def fragment0370096Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0370096_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 212) (SourceJson.white (fragment0370096Field001Chars00 ++ tail)) fragment0370096Acc00100 =
      SourceJson.object (fuel + 211) (SourceJson.white tail) fragment0370096Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0370096_object_field_001"
  err.flush

noncomputable def fragment0370096Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0370096Field002Value00 : SourceJson := .str (String.ofList ['3', '4', '4', '5', '2', '5', '9', '1', '8', '6', '2', '5', '5', '7', '9', '6', '3', '6', '2', '2', '6', '1', '5', '9', '3', '8', '1', '8', '7', '1', '3', '8', '1', '5', '8', '5', '3', '7', '0', '3', '2', '0', '2', '3', '2', '1', '/', '2', '0', '1', '2', '5', '3', '3', '3', '6', '9', '9', '5', '5', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0370096Acc00300 : List (String × SourceJson) := (fragment0370096Field002Key00, fragment0370096Field002Value00) :: fragment0370096Acc00200
noncomputable def fragment0370096Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '4', '4', '5', '2', '5', '9', '1', '8', '6', '2', '5', '5', '7', '9', '6', '3', '6', '2', '2', '6', '1', '5', '9', '3', '8', '1', '8', '7', '1', '3', '8', '1', '5', '8', '5', '3', '7', '0', '3', '2', '0', '2', '3', '2', '1', '/', '2', '0', '1', '2', '5', '3', '3', '3', '6', '9', '9', '5', '5', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0370096_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 211) (SourceJson.white (fragment0370096Field002Chars00 ++ tail)) fragment0370096Acc00200 =
      SourceJson.object (fuel + 210) (SourceJson.white tail) fragment0370096Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0370096_object_field_002"
  err.flush

noncomputable def fragment0370096Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0370096Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0370096Acc00400 : List (String × SourceJson) := (fragment0370096Field003Key00, fragment0370096Field003Value00) :: fragment0370096Acc00300
noncomputable def fragment0370096Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0370096_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 210) (SourceJson.white (fragment0370096Field003Chars00 ++ tail)) fragment0370096Acc00300 =
      SourceJson.object (fuel + 209) (SourceJson.white tail) fragment0370096Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0370096_object_field_003"
  err.flush

noncomputable def fragment0370096Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0370096Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0370096Acc00500 : List (String × SourceJson) := (fragment0370096Field004Key00, fragment0370096Field004Value00) :: fragment0370096Acc00400
noncomputable def fragment0370096Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0370096_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 209) (SourceJson.white (fragment0370096Field004Chars00 ++ tail)) fragment0370096Acc00400 =
      SourceJson.object (fuel + 208) (SourceJson.white tail) fragment0370096Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0370096_object_field_004"
  err.flush

noncomputable def fragment0370096Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0370096Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '3', '9', '7', '0', '7', '6', '0', '0', '2', '9', '/', '1', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '9', '7', '0', '7', '3', '5', '4', '4', '3', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '1', '7', '3', '5', '3', '7', '9', '9', '8', '9', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '4', '6', '6', '8', '9', '6', '5', '0', '1', '/', '5', '5', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '5', '9', '6', '0', '9', '9', '0', '6', '0', '9', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '3', '4', '6', '4', '2', '8', '3', '6', '7', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '1', '4', '2', '5', '5', '2', '9', '/', '3', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '8', '8', '9', '1', '5', '5', '9', '2', '7', '/', '6', '7', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '8', '7', '2', '7', '3', '0', '1', '7', '/', '6', '7', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '9', '9', '3', '1', '9', '5', '6', '2', '3', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0370096Acc00600 : List (String × SourceJson) := (fragment0370096Field005Key00, fragment0370096Field005Value00) :: fragment0370096Acc00500
noncomputable def fragment0370096Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '7', '0', '7', '6', '0', '0', '2', '9', '/', '1', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '9', '7', '0', '7', '3', '5', '4', '4', '3', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '1', '7', '3', '5', '3', '7', '9', '9', '8', '9', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '4', '6', '6', '8', '9', '6', '5', '0', '1', '/', '5', '5', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '5', '9', '6', '0', '9', '9', '0', '6', '0', '9', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '3', '4', '6', '4', '2', '8', '3', '6', '7', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '1', '4', '2', '5', '5', '2', '9', '/', '3', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '8', '8', '9', '1', '5', '5', '9', '2', '7', '/', '6', '7', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '8', '7', '2', '7', '3', '0', '1', '7', '/', '6', '7', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '9', '9', '3', '1', '9', '5', '6', '2', '3', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0370096_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 208) (SourceJson.white (fragment0370096Field005Chars00 ++ tail)) fragment0370096Acc00500 =
      SourceJson.object (fuel + 207) (SourceJson.white tail) fragment0370096Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0370096_object_field_005"
  err.flush

noncomputable def fragment0370096Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0370096Field006Value00 : SourceJson := .str (String.ofList ['5', '1', '2', '9', '5', '0', '6', '1', '9', '4', '1', '4', '8', '4', '1', '1', '3', '3', '7', '8', '8', '2', '5', '2', '8', '4', '3', '8', '8', '6', '0', '9', '5', '4', '0', '4', '7', '1', '2', '8', '7', '1', '5', '6', '3', '0', '2', '1', '5', '2', '4', '4', '5', '8', '4', '0', '0', '0', '0', '/', '5', '9', '6', '8', '3', '7', '1', '5', '4', '0', '9', '4', '6', '1', '4', '7', '6', '1', '4', '9', '2', '1', '3', '4', '9', '9', '9', '4', '7', '3', '0', '1', '9', '2', '6', '0', '0', '0', '8', '5', '7', '8', '0', '9', '4', '8', '9', '0', '7', '5', '1', '2', '5', '2', '0', '9', '1', '2', '1', '0', '3', '0', '1', '8', '0', '6', '0', '4', '4', '1'])
noncomputable def fragment0370096Acc00700 : List (String × SourceJson) := (fragment0370096Field006Key00, fragment0370096Field006Value00) :: fragment0370096Acc00600
noncomputable def fragment0370096Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '1', '2', '9', '5', '0', '6', '1', '9', '4', '1', '4', '8', '4', '1', '1', '3', '3', '7', '8', '8', '2', '5', '2', '8', '4', '3', '8', '8', '6', '0', '9', '5', '4', '0', '4', '7', '1', '2', '8', '7', '1', '5', '6', '3', '0', '2', '1', '5', '2', '4', '4', '5', '8', '4', '0', '0', '0', '0', '/', '5', '9', '6', '8', '3', '7', '1', '5', '4', '0', '9', '4', '6', '1', '4', '7', '6', '1', '4', '9', '2', '1', '3', '4', '9', '9', '9', '4', '7', '3', '0', '1', '9', '2', '6', '0', '0', '0', '8', '5', '7', '8', '0', '9', '4', '8', '9', '0', '7', '5', '1', '2', '5', '2', '0', '9', '1', '2', '1', '0', '3', '0', '1', '8', '0', '6', '0', '4', '4', '1', '"', ',']

theorem object_fragment0370096_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 207) (SourceJson.white (fragment0370096Field006Chars00 ++ tail)) fragment0370096Acc00600 =
      SourceJson.object (fuel + 206) (SourceJson.white tail) fragment0370096Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0370096_object_field_006"
  err.flush

noncomputable def fragment0370096Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0370096Field007Value00 : SourceJson := .str (String.ofList ['2', '1', '5', '5', '2', '1', '8', '7', '9', '2', '9', '8', '9', '3', '5', '4', '7', '0', '0', '3', '5', '9', '2', '5', '8', '4', '2', '2', '5', '8', '2', '6', '5', '4', '2', '5', '9', '5', '6', '5', '8', '2', '7', '5', '4', '4', '4', '9', '1', '8', '8', '0', '7', '6', '8', '2', '1', '9', '9', '5', '6', '0', '5', '7', '3', '9', '3', '0', '6', '7', '2', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '4', '6', '5', '9', '0', '5', '2', '2', '5', '2', '2', '5', '4', '5', '0', '1', '4', '5', '4', '5', '1', '9', '2', '6', '0', '1', '2', '7', '3', '9', '4', '3', '9', '6', '6', '0', '6', '4', '1', '3', '7', '5', '5', '9', '9', '5', '8', '6', '1', '2', '7', '0', '1', '6', '6', '8', '1', '6', '0', '9', '7', '8', '2', '7', '1', '0', '3', '5', '2', '1', '5', '1', '9', '0', '4', '4', '1', '9', '9', '1', '4', '5', '0', '4', '5', '2', '3', '8', '4', '7', '3', '7', '9', '7', '5', '3', '6', '5', '3', '7', '6', '3', '9', '8', '1'])
noncomputable def fragment0370096Acc00800 : List (String × SourceJson) := (fragment0370096Field007Key00, fragment0370096Field007Value00) :: fragment0370096Acc00700
noncomputable def fragment0370096Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '5', '5', '2', '1', '8', '7', '9', '2', '9', '8', '9', '3', '5', '4', '7', '0', '0', '3', '5', '9', '2', '5', '8', '4', '2', '2', '5', '8', '2', '6', '5', '4', '2', '5', '9', '5', '6', '5', '8', '2', '7', '5', '4', '4', '4', '9', '1', '8', '8', '0', '7', '6', '8', '2', '1', '9', '9', '5', '6', '0', '5', '7', '3', '9', '3', '0', '6', '7', '2', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '4', '6', '5', '9', '0', '5', '2', '2', '5', '2', '2', '5', '4', '5', '0', '1', '4', '5', '4', '5', '1', '9', '2', '6', '0', '1', '2', '7', '3', '9', '4', '3', '9', '6', '6', '0', '6', '4', '1', '3', '7', '5', '5', '9', '9', '5', '8', '6', '1', '2', '7', '0', '1', '6', '6', '8', '1', '6', '0', '9', '7', '8', '2', '7', '1', '0', '3', '5', '2', '1', '5', '1', '9', '0', '4', '4', '1', '9', '9', '1', '4', '5', '0', '4', '5', '2', '3', '8', '4', '7', '3', '7', '9', '7', '5', '3', '6', '5', '3', '7', '6', '3', '9', '8', '1', '"', ',']

theorem object_fragment0370096_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 206) (SourceJson.white (fragment0370096Field007Chars00 ++ tail)) fragment0370096Acc00700 =
      SourceJson.object (fuel + 205) (SourceJson.white tail) fragment0370096Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0370096_object_field_007"
  err.flush

noncomputable def fragment0370096Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0370096Field008Value00 : SourceJson := .str (String.ofList ['6', '8', '0', '9', '2', '5', '0', '1', '8', '7', '9', '2', '4', '6', '3', '3', '3', '3'])
noncomputable def fragment0370096Acc00900 : List (String × SourceJson) := (fragment0370096Field008Key00, fragment0370096Field008Value00) :: fragment0370096Acc00800
noncomputable def fragment0370096Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '8', '0', '9', '2', '5', '0', '1', '8', '7', '9', '2', '4', '6', '3', '3', '3', '3', '"', ',']

theorem object_fragment0370096_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 205) (SourceJson.white (fragment0370096Field008Chars00 ++ tail)) fragment0370096Acc00800 =
      SourceJson.object (fuel + 204) (SourceJson.white tail) fragment0370096Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0370096_object_field_008"
  err.flush

noncomputable def fragment0370096Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0370096Field009Value00 : SourceJson := .str (String.ofList ['4', '9', '2', '6', '6', '7', '8', '9', '9', '6', '9', '3', '2', '1', '8', '0', '0', '6', '1'])
noncomputable def fragment0370096Acc01000 : List (String × SourceJson) := (fragment0370096Field009Key00, fragment0370096Field009Value00) :: fragment0370096Acc00900
noncomputable def fragment0370096Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '9', '2', '6', '6', '7', '8', '9', '9', '6', '9', '3', '2', '1', '8', '0', '0', '6', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0370096_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0370096Field009Chars00 ++ tail)) fragment0370096Acc00900 =
      .ok (.obj (fragment0370096Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0370096_object_field_009"
  err.flush

noncomputable def fragment0370096Chars : List Char := '{' :: (fragment0370096Field000Chars00 ++ fragment0370096Field001Chars00 ++ fragment0370096Field002Chars00 ++ fragment0370096Field003Chars00 ++ fragment0370096Field004Chars00 ++ fragment0370096Field005Chars00 ++ fragment0370096Field006Chars00 ++ fragment0370096Field007Chars00 ++ fragment0370096Field008Chars00 ++ fragment0370096Field009Chars00)
noncomputable def fragment0370096Value : SourceJson := .obj (fragment0370096Acc01000.reverse)

theorem value_fragment0370096 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 214) (fragment0370096Chars ++ tail) =
      .ok (fragment0370096Value, tail) := by
  have hinput : fragment0370096Chars ++ tail = '{' :: (fragment0370096Field000Chars00 ++ (fragment0370096Field001Chars00 ++ (fragment0370096Field002Chars00 ++ (fragment0370096Field003Chars00 ++ (fragment0370096Field004Chars00 ++ (fragment0370096Field005Chars00 ++ (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0370096Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 214) (fragment0370096Chars ++ tail) =
        SourceJson.value (fuel + 214) ('{' :: (fragment0370096Field000Chars00 ++ (fragment0370096Field001Chars00 ++ (fragment0370096Field002Chars00 ++ (fragment0370096Field003Chars00 ++ (fragment0370096Field004Chars00 ++ (fragment0370096Field005Chars00 ++ (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 214)) hinput
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0370096Field000Chars00 ++ (fragment0370096Field001Chars00 ++ (fragment0370096Field002Chars00 ++ (fragment0370096Field003Chars00 ++ (fragment0370096Field004Chars00 ++ (fragment0370096Field005Chars00 ++ (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail)))))))))))) fragment0370096Acc00000 := by rfl
    _ = SourceJson.object (fuel + 212) (SourceJson.white (fragment0370096Field001Chars00 ++ (fragment0370096Field002Chars00 ++ (fragment0370096Field003Chars00 ++ (fragment0370096Field004Chars00 ++ (fragment0370096Field005Chars00 ++ (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail))))))))))) fragment0370096Acc00100 := object_fragment0370096_field_000 fuel (fragment0370096Field001Chars00 ++ (fragment0370096Field002Chars00 ++ (fragment0370096Field003Chars00 ++ (fragment0370096Field004Chars00 ++ (fragment0370096Field005Chars00 ++ (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 211) (SourceJson.white (fragment0370096Field002Chars00 ++ (fragment0370096Field003Chars00 ++ (fragment0370096Field004Chars00 ++ (fragment0370096Field005Chars00 ++ (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail)))))))))) fragment0370096Acc00200 := object_fragment0370096_field_001 fuel (fragment0370096Field002Chars00 ++ (fragment0370096Field003Chars00 ++ (fragment0370096Field004Chars00 ++ (fragment0370096Field005Chars00 ++ (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 210) (SourceJson.white (fragment0370096Field003Chars00 ++ (fragment0370096Field004Chars00 ++ (fragment0370096Field005Chars00 ++ (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail))))))))) fragment0370096Acc00300 := object_fragment0370096_field_002 fuel (fragment0370096Field003Chars00 ++ (fragment0370096Field004Chars00 ++ (fragment0370096Field005Chars00 ++ (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 209) (SourceJson.white (fragment0370096Field004Chars00 ++ (fragment0370096Field005Chars00 ++ (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail)))))))) fragment0370096Acc00400 := object_fragment0370096_field_003 fuel (fragment0370096Field004Chars00 ++ (fragment0370096Field005Chars00 ++ (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 208) (SourceJson.white (fragment0370096Field005Chars00 ++ (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail))))))) fragment0370096Acc00500 := object_fragment0370096_field_004 fuel (fragment0370096Field005Chars00 ++ (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 207) (SourceJson.white (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail)))))) fragment0370096Acc00600 := object_fragment0370096_field_005 fuel (fragment0370096Field006Chars00 ++ (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 206) (SourceJson.white (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail))))) fragment0370096Acc00700 := object_fragment0370096_field_006 fuel (fragment0370096Field007Chars00 ++ (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 205) (SourceJson.white (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail)))) fragment0370096Acc00800 := object_fragment0370096_field_007 fuel (fragment0370096Field008Chars00 ++ (fragment0370096Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0370096Field009Chars00 ++ (tail))) fragment0370096Acc00900 := object_fragment0370096_field_008 fuel (fragment0370096Field009Chars00 ++ (tail))
    _ = .ok (fragment0370096Value, tail) := object_fragment0370096_field_009 fuel (tail)

noncomputable def fragment0371690Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0371690Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0371690Field000Value00 : SourceJson := .number (String.ofList ['8', '6'])
noncomputable def fragment0371690Acc00100 : List (String × SourceJson) := (fragment0371690Field000Key00, fragment0371690Field000Value00) :: fragment0371690Acc00000
noncomputable def fragment0371690Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '6', ',']

theorem object_fragment0371690_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 268) (SourceJson.white (fragment0371690Field000Chars00 ++ tail)) fragment0371690Acc00000 =
      SourceJson.object (fuel + 267) (SourceJson.white tail) fragment0371690Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0371690_object_field_000"
  err.flush

noncomputable def fragment0371690Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0371690Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0371690Acc00200 : List (String × SourceJson) := (fragment0371690Field001Key00, fragment0371690Field001Value00) :: fragment0371690Acc00100
noncomputable def fragment0371690Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0371690_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 267) (SourceJson.white (fragment0371690Field001Chars00 ++ tail)) fragment0371690Acc00100 =
      SourceJson.object (fuel + 266) (SourceJson.white tail) fragment0371690Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0371690_object_field_001"
  err.flush

noncomputable def fragment0371690Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0371690Field002Value00 : SourceJson := .str (String.ofList ['1', '0', '3', '1', '6', '9', '2', '0', '1', '4', '8', '5', '2', '6', '9', '3', '4', '8', '6', '5', '9', '6', '1', '0', '1', '4', '3', '0', '1', '2', '9', '2', '2', '0', '8', '1', '0', '3', '1', '/', '6', '7', '1', '7', '9', '3', '9', '0', '6', '4', '0', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0371690Acc00300 : List (String × SourceJson) := (fragment0371690Field002Key00, fragment0371690Field002Value00) :: fragment0371690Acc00200
noncomputable def fragment0371690Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '0', '3', '1', '6', '9', '2', '0', '1', '4', '8', '5', '2', '6', '9', '3', '4', '8', '6', '5', '9', '6', '1', '0', '1', '4', '3', '0', '1', '2', '9', '2', '2', '0', '8', '1', '0', '3', '1', '/', '6', '7', '1', '7', '9', '3', '9', '0', '6', '4', '0', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0371690_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 266) (SourceJson.white (fragment0371690Field002Chars00 ++ tail)) fragment0371690Acc00200 =
      SourceJson.object (fuel + 265) (SourceJson.white tail) fragment0371690Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0371690_object_field_002"
  err.flush

noncomputable def fragment0371690Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0371690Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0371690Acc00400 : List (String × SourceJson) := (fragment0371690Field003Key00, fragment0371690Field003Value00) :: fragment0371690Acc00300
noncomputable def fragment0371690Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0371690_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 265) (SourceJson.white (fragment0371690Field003Chars00 ++ tail)) fragment0371690Acc00300 =
      SourceJson.object (fuel + 264) (SourceJson.white tail) fragment0371690Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0371690_object_field_003"
  err.flush

noncomputable def fragment0371690Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0371690Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0371690Acc00500 : List (String × SourceJson) := (fragment0371690Field004Key00, fragment0371690Field004Value00) :: fragment0371690Acc00400
noncomputable def fragment0371690Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0371690_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment0371690Field004Chars00 ++ tail)) fragment0371690Acc00400 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment0371690Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0371690_object_field_004"
  err.flush

noncomputable def fragment0371690Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0371690Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '4', '6', '4', '0', '4', '3', '0', '0', '8', '0', '3', '8', '5', '7', '/', '1', '6', '5', '7', '7', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '8', '0', '8', '0', '0', '3', '8', '1', '2', '8', '9', '3', '7', '/', '1', '6', '5', '7', '7', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '1', '9', '7', '8', '6', '6', '0', '2', '8', '2', '1', '/', '1', '2', '7', '5', '2', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '1', '3', '5', '6', '1', '2', '0', '1', '2', '9', '9', '4', '3', '/', '2', '4', '8', '6', '6', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '1', '6', '6', '0', '7', '9', '6', '5', '6', '6', '9', '/', '9', '7', '5', '1', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '9', '5', '9', '8', '6', '8', '8', '6', '1', '2', '3', '9', '/', '1', '6', '5', '7', '7', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '4', '6', '3', '5', '2', '5', '1', '1', '7', '1', '7', '/', '5', '2', '3', '5', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '3', '4', '9', '5', '8', '2', '0', '3', '5', '3', '3', '9', '/', '9', '9', '4', '6', '5', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '1', '8', '2', '4', '8', '0', '2', '4', '5', '0', '9', '3', '3', '/', '4', '9', '7', '3', '2', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '1', '8', '2', '3', '8', '0', '7', '7', '9', '1', '8', '1', '3', '/', '4', '9', '7', '3', '2', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0371690Acc00600 : List (String × SourceJson) := (fragment0371690Field005Key00, fragment0371690Field005Value00) :: fragment0371690Acc00500
noncomputable def fragment0371690Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '4', '0', '4', '3', '0', '0', '8', '0', '3', '8', '5', '7', '/', '1', '6', '5', '7', '7', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '0', '8', '0', '0', '3', '8', '1', '2', '8', '9', '3', '7', '/', '1', '6', '5', '7', '7', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '1', '9', '7', '8', '6', '6', '0', '2', '8', '2', '1', '/', '1', '2', '7', '5', '2', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '1', '3', '5', '6', '1', '2', '0', '1', '2', '9', '9', '4', '3', '/', '2', '4', '8', '6', '6', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '1', '6', '6', '0', '7', '9', '6', '5', '6', '6', '9', '/', '9', '7', '5', '1', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '9', '5', '9', '8', '6', '8', '8', '6', '1', '2', '3', '9', '/', '1', '6', '5', '7', '7', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '6', '3', '5', '2', '5', '1', '1', '7', '1', '7', '/', '5', '2', '3', '5', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '3', '4', '9', '5', '8', '2', '0', '3', '5', '3', '3', '9', '/', '9', '9', '4', '6', '5', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '8', '2', '4', '8', '0', '2', '4', '5', '0', '9', '3', '3', '/', '4', '9', '7', '3', '2', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '8', '2', '3', '8', '0', '7', '7', '9', '1', '8', '1', '3', '/', '4', '9', '7', '3', '2', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0371690_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0371690Field005Chars00 ++ tail)) fragment0371690Acc00500 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0371690Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0371690_object_field_005"
  err.flush

noncomputable def fragment0371690Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0371690Field006Value00 : SourceJson := .str (String.ofList ['4', '4', '7', '2', '1', '5', '6', '2', '3', '9', '1', '2', '9', '0', '8', '0', '5', '3', '2', '3', '2', '4', '0', '9', '7', '3', '2', '0', '3', '7', '4', '3', '0', '5', '7', '3', '6', '7', '3', '0', '4', '8', '4', '0', '0', '0', '0', '0', '/', '6', '1', '5', '9', '1', '1', '0', '9', '5', '9', '7', '8', '0', '5', '7', '7', '1', '2', '8', '6', '6', '6', '4', '1', '6', '6', '2', '3', '3', '8', '5', '0', '4', '1', '5', '8', '2', '0', '2', '6', '7', '6', '1', '8', '0', '7', '5', '5', '0', '0', '8', '0', '3', '7', '3', '7', '5', '9', '3', '2', '7', '5', '7', '9'])
noncomputable def fragment0371690Acc00700 : List (String × SourceJson) := (fragment0371690Field006Key00, fragment0371690Field006Value00) :: fragment0371690Acc00600
noncomputable def fragment0371690Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '4', '7', '2', '1', '5', '6', '2', '3', '9', '1', '2', '9', '0', '8', '0', '5', '3', '2', '3', '2', '4', '0', '9', '7', '3', '2', '0', '3', '7', '4', '3', '0', '5', '7', '3', '6', '7', '3', '0', '4', '8', '4', '0', '0', '0', '0', '0', '/', '6', '1', '5', '9', '1', '1', '0', '9', '5', '9', '7', '8', '0', '5', '7', '7', '1', '2', '8', '6', '6', '6', '4', '1', '6', '6', '2', '3', '3', '8', '5', '0', '4', '1', '5', '8', '2', '0', '2', '6', '7', '6', '1', '8', '0', '7', '5', '5', '0', '0', '8', '0', '3', '7', '3', '7', '5', '9', '3', '2', '7', '5', '7', '9', '"', ',']

theorem object_fragment0371690_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0371690Field006Chars00 ++ tail)) fragment0371690Acc00600 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0371690Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0371690_object_field_006"
  err.flush

noncomputable def fragment0371690Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0371690Field007Value00 : SourceJson := .str (String.ofList ['1', '6', '9', '1', '6', '2', '1', '8', '1', '3', '1', '2', '4', '4', '9', '2', '7', '9', '6', '4', '7', '7', '6', '0', '0', '1', '2', '9', '9', '4', '4', '4', '7', '9', '8', '2', '4', '3', '1', '7', '6', '9', '5', '3', '9', '5', '9', '0', '1', '7', '8', '3', '7', '6', '4', '5', '8', '5', '8', '6', '7', '3', '2', '0', '0', '5', '8', '1', '4', '2', '9', '4', '5', '9', '5', '8', '2', '5', '4', '0', '7', '3', '2', '6', '4', '6', '0', '5', '0', '7', '9', '8', '1', '7', '2', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '3', '1', '3', '9', '8', '7', '1', '2', '5', '4', '4', '3', '0', '7', '8', '3', '9', '9', '8', '2', '6', '8', '8', '8', '9', '0', '3', '9', '1', '7', '6', '3', '3', '0', '3', '9', '9', '5', '7', '5', '4', '0', '0', '1', '4', '4', '6', '3', '6', '8', '8', '0', '5', '6', '5', '4', '1', '3', '4', '3', '3', '0', '8', '7', '6', '6', '7', '0', '0', '6', '7', '2', '4', '6', '1', '2', '2', '3', '8', '2', '4', '6', '8', '6', '2', '4', '9', '0', '1', '2', '5', '2', '5', '2', '3', '3', '5', '2', '7', '1', '8', '0', '6', '1', '7', '1', '3', '4', '6', '0', '3', '7', '6', '6', '8', '7', '0', '7', '9', '9', '3', '3', '4', '9', '5', '5', '3', '7', '2', '2', '6', '8', '5', '4', '7'])
noncomputable def fragment0371690Acc00800 : List (String × SourceJson) := (fragment0371690Field007Key00, fragment0371690Field007Value00) :: fragment0371690Acc00700
noncomputable def fragment0371690Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '9', '1', '6', '2', '1', '8', '1', '3', '1', '2', '4', '4', '9', '2', '7', '9', '6', '4', '7', '7', '6', '0', '0', '1', '2', '9', '9', '4', '4', '4', '7', '9', '8', '2', '4', '3', '1', '7', '6', '9', '5', '3', '9', '5', '9', '0', '1', '7', '8', '3', '7', '6', '4', '5', '8', '5', '8', '6', '7', '3', '2', '0', '0', '5', '8', '1', '4', '2', '9', '4', '5', '9', '5', '8', '2', '5', '4', '0', '7', '3', '2', '6', '4', '6', '0', '5', '0', '7', '9', '8', '1', '7', '2', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '3', '1', '3', '9', '8', '7', '1', '2', '5', '4', '4', '3', '0', '7', '8', '3', '9', '9', '8', '2', '6', '8', '8', '8', '9', '0', '3', '9', '1', '7', '6', '3', '3', '0', '3', '9', '9', '5', '7', '5', '4', '0', '0', '1', '4', '4', '6', '3', '6', '8', '8', '0', '5', '6', '5', '4', '1', '3', '4', '3', '3', '0', '8', '7', '6', '6', '7', '0', '0', '6', '7', '2', '4', '6', '1', '2', '2', '3', '8', '2', '4', '6', '8', '6', '2', '4', '9', '0', '1', '2', '5', '2', '5', '2', '3', '3', '5', '2', '7', '1', '8', '0', '6', '1', '7', '1', '3', '4', '6', '0', '3', '7', '6', '6', '8', '7', '0', '7', '9', '9', '3', '3', '4', '9', '5', '5', '3', '7', '2', '2', '6', '8', '5', '4', '7', '"', ',']

theorem object_fragment0371690_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0371690Field007Chars00 ++ tail)) fragment0371690Acc00700 =
      SourceJson.object (fuel + 260) (SourceJson.white tail) fragment0371690Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0371690_object_field_007"
  err.flush

noncomputable def fragment0371690Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0371690Field008Value00 : SourceJson := .str (String.ofList ['5', '7', '5', '2', '7', '9', '0', '0', '3', '1', '1', '6', '9'])
noncomputable def fragment0371690Acc00900 : List (String × SourceJson) := (fragment0371690Field008Key00, fragment0371690Field008Value00) :: fragment0371690Acc00800
noncomputable def fragment0371690Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '7', '5', '2', '7', '9', '0', '0', '3', '1', '1', '6', '9', '"', ',']

theorem object_fragment0371690_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0371690Field008Chars00 ++ tail)) fragment0371690Acc00800 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0371690Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0371690_object_field_008"
  err.flush

noncomputable def fragment0371690Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0371690Field009Value00 : SourceJson := .str (String.ofList ['4', '0', '4', '4', '1', '9', '4', '5', '8', '6', '4', '5', '2', '5'])
noncomputable def fragment0371690Acc01000 : List (String × SourceJson) := (fragment0371690Field009Key00, fragment0371690Field009Value00) :: fragment0371690Acc00900
noncomputable def fragment0371690Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '4', '4', '1', '9', '4', '5', '8', '6', '4', '5', '2', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0371690_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0371690Field009Chars00 ++ tail)) fragment0371690Acc00900 =
      .ok (.obj (fragment0371690Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0371690_object_field_009"
  err.flush

noncomputable def fragment0371690Chars : List Char := '{' :: (fragment0371690Field000Chars00 ++ fragment0371690Field001Chars00 ++ fragment0371690Field002Chars00 ++ fragment0371690Field003Chars00 ++ fragment0371690Field004Chars00 ++ fragment0371690Field005Chars00 ++ fragment0371690Field006Chars00 ++ fragment0371690Field007Chars00 ++ fragment0371690Field008Chars00 ++ fragment0371690Field009Chars00)
noncomputable def fragment0371690Value : SourceJson := .obj (fragment0371690Acc01000.reverse)

theorem value_fragment0371690 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 269) (fragment0371690Chars ++ tail) =
      .ok (fragment0371690Value, tail) := by
  have hinput : fragment0371690Chars ++ tail = '{' :: (fragment0371690Field000Chars00 ++ (fragment0371690Field001Chars00 ++ (fragment0371690Field002Chars00 ++ (fragment0371690Field003Chars00 ++ (fragment0371690Field004Chars00 ++ (fragment0371690Field005Chars00 ++ (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0371690Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 269) (fragment0371690Chars ++ tail) =
        SourceJson.value (fuel + 269) ('{' :: (fragment0371690Field000Chars00 ++ (fragment0371690Field001Chars00 ++ (fragment0371690Field002Chars00 ++ (fragment0371690Field003Chars00 ++ (fragment0371690Field004Chars00 ++ (fragment0371690Field005Chars00 ++ (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 269)) hinput
    _ = SourceJson.object (fuel + 268) (SourceJson.white (fragment0371690Field000Chars00 ++ (fragment0371690Field001Chars00 ++ (fragment0371690Field002Chars00 ++ (fragment0371690Field003Chars00 ++ (fragment0371690Field004Chars00 ++ (fragment0371690Field005Chars00 ++ (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail)))))))))))) fragment0371690Acc00000 := by rfl
    _ = SourceJson.object (fuel + 267) (SourceJson.white (fragment0371690Field001Chars00 ++ (fragment0371690Field002Chars00 ++ (fragment0371690Field003Chars00 ++ (fragment0371690Field004Chars00 ++ (fragment0371690Field005Chars00 ++ (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail))))))))))) fragment0371690Acc00100 := object_fragment0371690_field_000 fuel (fragment0371690Field001Chars00 ++ (fragment0371690Field002Chars00 ++ (fragment0371690Field003Chars00 ++ (fragment0371690Field004Chars00 ++ (fragment0371690Field005Chars00 ++ (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 266) (SourceJson.white (fragment0371690Field002Chars00 ++ (fragment0371690Field003Chars00 ++ (fragment0371690Field004Chars00 ++ (fragment0371690Field005Chars00 ++ (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail)))))))))) fragment0371690Acc00200 := object_fragment0371690_field_001 fuel (fragment0371690Field002Chars00 ++ (fragment0371690Field003Chars00 ++ (fragment0371690Field004Chars00 ++ (fragment0371690Field005Chars00 ++ (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 265) (SourceJson.white (fragment0371690Field003Chars00 ++ (fragment0371690Field004Chars00 ++ (fragment0371690Field005Chars00 ++ (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail))))))))) fragment0371690Acc00300 := object_fragment0371690_field_002 fuel (fragment0371690Field003Chars00 ++ (fragment0371690Field004Chars00 ++ (fragment0371690Field005Chars00 ++ (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment0371690Field004Chars00 ++ (fragment0371690Field005Chars00 ++ (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail)))))))) fragment0371690Acc00400 := object_fragment0371690_field_003 fuel (fragment0371690Field004Chars00 ++ (fragment0371690Field005Chars00 ++ (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0371690Field005Chars00 ++ (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail))))))) fragment0371690Acc00500 := object_fragment0371690_field_004 fuel (fragment0371690Field005Chars00 ++ (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail)))))) fragment0371690Acc00600 := object_fragment0371690_field_005 fuel (fragment0371690Field006Chars00 ++ (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail))))) fragment0371690Acc00700 := object_fragment0371690_field_006 fuel (fragment0371690Field007Chars00 ++ (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail)))) fragment0371690Acc00800 := object_fragment0371690_field_007 fuel (fragment0371690Field008Chars00 ++ (fragment0371690Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0371690Field009Chars00 ++ (tail))) fragment0371690Acc00900 := object_fragment0371690_field_008 fuel (fragment0371690Field009Chars00 ++ (tail))
    _ = .ok (fragment0371690Value, tail) := object_fragment0371690_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0085_before_reader"
  err.flush

noncomputable def chunk0085LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0085SuffixChars00 : List Char := [',']
noncomputable def chunk0085Chars00 : List Char := chunk0085LeadChars00 ++ fragment0370096Chars ++ chunk0085SuffixChars00
noncomputable def chunk0085Push00 (acc : List SourceJson) : List SourceJson := fragment0370096Value :: acc

noncomputable def chunk0085AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0085_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 519)
      (SourceJson.white (chunk0085LeadChars00 ++ (fragment0370096Chars ++ rest))) acc =
      (SourceJson.value (fuel + 518) (fragment0370096Chars ++ rest)).bind
        (chunk0085AfterValue00 (fuel + 518) acc) := by rfl

theorem array_chunk0085 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 519) (SourceJson.white (chunk0085Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 518) (SourceJson.white tail) (chunk0085Push00 acc) := by
  have hinput : chunk0085Chars00 ++ tail = chunk0085LeadChars00 ++ (fragment0370096Chars ++ (chunk0085SuffixChars00 ++ tail)) := by
    simp only [chunk0085Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 519) (SourceJson.white (chunk0085Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 519)
          (SourceJson.white (chunk0085LeadChars00 ++ (fragment0370096Chars ++ (chunk0085SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 519) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 518) (fragment0370096Chars ++ (chunk0085SuffixChars00 ++ tail))).bind
        (chunk0085AfterValue00 (fuel + 518) acc) := array_chunk0085_head fuel (chunk0085SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0370096Value, chunk0085SuffixChars00 ++ tail)).bind
        (chunk0085AfterValue00 (fuel + 518) acc) :=
      congrArg (fun result => result.bind (chunk0085AfterValue00 (fuel + 518) acc))
        (value_fragment0370096 (fuel + 304) (chunk0085SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 518) (SourceJson.white tail) (chunk0085Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0085_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0086_before_reader"
  err.flush

noncomputable def chunk0086LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0086SuffixChars00 : List Char := [',']
noncomputable def chunk0086Chars00 : List Char := chunk0086LeadChars00 ++ fragment0371690Chars ++ chunk0086SuffixChars00
noncomputable def chunk0086Push00 (acc : List SourceJson) : List SourceJson := fragment0371690Value :: acc

noncomputable def chunk0086AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0086_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 518)
      (SourceJson.white (chunk0086LeadChars00 ++ (fragment0371690Chars ++ rest))) acc =
      (SourceJson.value (fuel + 517) (fragment0371690Chars ++ rest)).bind
        (chunk0086AfterValue00 (fuel + 517) acc) := by rfl

theorem array_chunk0086 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 518) (SourceJson.white (chunk0086Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 517) (SourceJson.white tail) (chunk0086Push00 acc) := by
  have hinput : chunk0086Chars00 ++ tail = chunk0086LeadChars00 ++ (fragment0371690Chars ++ (chunk0086SuffixChars00 ++ tail)) := by
    simp only [chunk0086Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 518) (SourceJson.white (chunk0086Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 518)
          (SourceJson.white (chunk0086LeadChars00 ++ (fragment0371690Chars ++ (chunk0086SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 518) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 517) (fragment0371690Chars ++ (chunk0086SuffixChars00 ++ tail))).bind
        (chunk0086AfterValue00 (fuel + 517) acc) := array_chunk0086_head fuel (chunk0086SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0371690Value, chunk0086SuffixChars00 ++ tail)).bind
        (chunk0086AfterValue00 (fuel + 517) acc) :=
      congrArg (fun result => result.bind (chunk0086AfterValue00 (fuel + 517) acc))
        (value_fragment0371690 (fuel + 248) (chunk0086SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 517) (SourceJson.white tail) (chunk0086Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0086_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0085Chars00 ++ chunk0086Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0086Push00 (chunk0085Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 519) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 517) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0085Chars00 ++ (chunk0086Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 519) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 519) (SourceJson.white (chunk0085Chars00 ++ (chunk0086Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 519) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 518) (SourceJson.white (chunk0086Chars00 ++ (tail))) (chunk0085Push00 (acc)) := array_chunk0085 fuel (chunk0086Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 517) (SourceJson.white tail) (blockPush acc) := array_chunk0086 fuel (tail) (chunk0085Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 370090).take 3258 = blockChars := by rfl

theorem block_original_split : sourceRest 370090 = blockChars ++ sourceRest 373348 := by
  calc
    sourceRest 370090 = (sourceRest 370090).take 3258 ++ (sourceRest 370090).drop 3258 :=
      (List.take_append_drop 3258 (sourceRest 370090)).symm
    _ = blockChars ++ (sourceRest 370090).drop 3258 :=
      congrArg (fun part => part ++ (sourceRest 370090).drop 3258) block_original_prefix
    _ = blockChars ++ sourceRest 373348 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 370090 3258)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 519) (SourceJson.white (sourceRest 370090)) acc =
      SourceJson.array (fuel + 517) (SourceJson.white (sourceRest 373348)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 519) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 373348) acc)

#print axioms object_fragment0370096_field_000
#print axioms object_fragment0370096_field_001
#print axioms object_fragment0370096_field_002
#print axioms object_fragment0370096_field_003
#print axioms object_fragment0370096_field_004
#print axioms object_fragment0370096_field_005
#print axioms object_fragment0370096_field_006
#print axioms object_fragment0370096_field_007
#print axioms object_fragment0370096_field_008
#print axioms object_fragment0370096_field_009
#print axioms value_fragment0370096
#print axioms object_fragment0371690_field_000
#print axioms object_fragment0371690_field_001
#print axioms object_fragment0371690_field_002
#print axioms object_fragment0371690_field_003
#print axioms object_fragment0371690_field_004
#print axioms object_fragment0371690_field_005
#print axioms object_fragment0371690_field_006
#print axioms object_fragment0371690_field_007
#print axioms object_fragment0371690_field_008
#print axioms object_fragment0371690_field_009
#print axioms value_fragment0371690
#print axioms array_chunk0085_head
#print axioms array_chunk0085
#print axioms array_chunk0086_head
#print axioms array_chunk0086
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock043

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
