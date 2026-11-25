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

namespace SimplicesBlock032

noncomputable def fragment0333597Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0333597Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0333597Field000Value00 : SourceJson := .number (String.ofList ['6', '3'])
noncomputable def fragment0333597Acc00100 : List (String × SourceJson) := (fragment0333597Field000Key00, fragment0333597Field000Value00) :: fragment0333597Acc00000
noncomputable def fragment0333597Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '3', ',']

theorem object_fragment0333597_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0333597Field000Chars00 ++ tail)) fragment0333597Acc00000 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0333597Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333597_object_field_000"
  err.flush

noncomputable def fragment0333597Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0333597Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0333597Acc00200 : List (String × SourceJson) := (fragment0333597Field001Key00, fragment0333597Field001Value00) :: fragment0333597Acc00100
noncomputable def fragment0333597Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0333597_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0333597Field001Chars00 ++ tail)) fragment0333597Acc00100 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment0333597Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333597_object_field_001"
  err.flush

noncomputable def fragment0333597Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0333597Field002Value00 : SourceJson := .str (String.ofList ['3', '0', '2', '4', '9', '5', '6', '7', '8', '7', '5', '0', '6', '4', '4', '6', '4', '7', '2', '8', '7', '0', '4', '5', '8', '4', '4', '2', '7', '5', '2', '7', '8', '6', '3', '9', '/', '1', '5', '4', '0', '1', '4', '8', '4', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0333597Acc00300 : List (String × SourceJson) := (fragment0333597Field002Key00, fragment0333597Field002Value00) :: fragment0333597Acc00200
noncomputable def fragment0333597Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '0', '2', '4', '9', '5', '6', '7', '8', '7', '5', '0', '6', '4', '4', '6', '4', '7', '2', '8', '7', '0', '4', '5', '8', '4', '4', '2', '7', '5', '2', '7', '8', '6', '3', '9', '/', '1', '5', '4', '0', '1', '4', '8', '4', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0333597_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0333597Field002Chars00 ++ tail)) fragment0333597Acc00200 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment0333597Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333597_object_field_002"
  err.flush

noncomputable def fragment0333597Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0333597Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0333597Acc00400 : List (String × SourceJson) := (fragment0333597Field003Key00, fragment0333597Field003Value00) :: fragment0333597Acc00300
noncomputable def fragment0333597Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0333597_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment0333597Field003Chars00 ++ tail)) fragment0333597Acc00300 =
      SourceJson.object (fuel + 213) (SourceJson.white tail) fragment0333597Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333597_object_field_003"
  err.flush

noncomputable def fragment0333597Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0333597Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0333597Acc00500 : List (String × SourceJson) := (fragment0333597Field004Key00, fragment0333597Field004Value00) :: fragment0333597Acc00400
noncomputable def fragment0333597Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0333597_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0333597Field004Chars00 ++ tail)) fragment0333597Acc00400 =
      SourceJson.object (fuel + 212) (SourceJson.white tail) fragment0333597Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333597_object_field_004"
  err.flush

noncomputable def fragment0333597Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0333597Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '1', '3', '9', '4', '6', '0', '3', '6', '0', '2', '3', '/', '7', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '1', '4', '5', '2', '1', '3', '8', '2', '6', '3', '/', '7', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '6', '1', '2', '1', '9', '7', '3', '0', '7', '/', '2', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '6', '4', '1', '9', '7', '5', '8', '0', '3', '/', '2', '4', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '0', '8', '9', '2', '5', '4', '9', '8', '3', '/', '4', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '4', '2', '3', '0', '2', '3', '9', '1', '2', '9', '/', '3', '7', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '5', '1', '8', '1', '9', '5', '1', '5', '0', '7', '/', '2', '9', '7', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '3', '5', '5', '5', '6', '1', '3', '0', '9', '7', '/', '2', '9', '7', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '0', '0', '6', '4', '1', '6', '1', '1', '1', '/', '2', '4', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '0', '1', '8', '2', '5', '8', '2', '5', '3', '/', '7', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0333597Acc00600 : List (String × SourceJson) := (fragment0333597Field005Key00, fragment0333597Field005Value00) :: fragment0333597Acc00500
noncomputable def fragment0333597Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '3', '9', '4', '6', '0', '3', '6', '0', '2', '3', '/', '7', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '1', '4', '5', '2', '1', '3', '8', '2', '6', '3', '/', '7', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '6', '1', '2', '1', '9', '7', '3', '0', '7', '/', '2', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '6', '4', '1', '9', '7', '5', '8', '0', '3', '/', '2', '4', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '0', '8', '9', '2', '5', '4', '9', '8', '3', '/', '4', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '4', '2', '3', '0', '2', '3', '9', '1', '2', '9', '/', '3', '7', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '5', '1', '8', '1', '9', '5', '1', '5', '0', '7', '/', '2', '9', '7', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '3', '5', '5', '5', '6', '1', '3', '0', '9', '7', '/', '2', '9', '7', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '0', '0', '6', '4', '1', '6', '1', '1', '1', '/', '2', '4', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '0', '1', '8', '2', '5', '8', '2', '5', '3', '/', '7', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0333597_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 212) (SourceJson.white (fragment0333597Field005Chars00 ++ tail)) fragment0333597Acc00500 =
      SourceJson.object (fuel + 211) (SourceJson.white tail) fragment0333597Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333597_object_field_005"
  err.flush

noncomputable def fragment0333597Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0333597Field006Value00 : SourceJson := .str (String.ofList ['4', '0', '8', '1', '9', '0', '1', '4', '1', '2', '2', '6', '5', '7', '1', '2', '1', '4', '4', '3', '3', '2', '7', '6', '1', '4', '2', '9', '2', '8', '2', '1', '1', '3', '2', '2', '2', '6', '3', '1', '6', '8', '7', '5', '0', '0', '/', '3', '4', '0', '4', '4', '1', '1', '7', '9', '3', '1', '4', '0', '3', '6', '3', '3', '2', '7', '4', '0', '0', '2', '4', '2', '8', '5', '9', '4', '2', '4', '0', '9', '4', '4', '3', '7', '5', '1', '9', '1', '5', '4', '1', '6', '3', '3', '0', '4', '2', '1', '5', '6', '8', '7', '7', '9', '0', '0', '4', '1'])
noncomputable def fragment0333597Acc00700 : List (String × SourceJson) := (fragment0333597Field006Key00, fragment0333597Field006Value00) :: fragment0333597Acc00600
noncomputable def fragment0333597Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '0', '8', '1', '9', '0', '1', '4', '1', '2', '2', '6', '5', '7', '1', '2', '1', '4', '4', '3', '3', '2', '7', '6', '1', '4', '2', '9', '2', '8', '2', '1', '1', '3', '2', '2', '2', '6', '3', '1', '6', '8', '7', '5', '0', '0', '/', '3', '4', '0', '4', '4', '1', '1', '7', '9', '3', '1', '4', '0', '3', '6', '3', '3', '2', '7', '4', '0', '0', '2', '4', '2', '8', '5', '9', '4', '2', '4', '0', '9', '4', '4', '3', '7', '5', '1', '9', '1', '5', '4', '1', '6', '3', '3', '0', '4', '2', '1', '5', '6', '8', '7', '7', '9', '0', '0', '4', '1', '"', ',']

theorem object_fragment0333597_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 211) (SourceJson.white (fragment0333597Field006Chars00 ++ tail)) fragment0333597Acc00600 =
      SourceJson.object (fuel + 210) (SourceJson.white tail) fragment0333597Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333597_object_field_006"
  err.flush

noncomputable def fragment0333597Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0333597Field007Value00 : SourceJson := .str (String.ofList ['1', '6', '2', '1', '5', '6', '6', '5', '8', '0', '6', '4', '8', '5', '6', '6', '8', '7', '3', '7', '3', '0', '1', '7', '0', '4', '0', '3', '0', '4', '7', '5', '5', '3', '4', '6', '5', '0', '4', '1', '2', '6', '4', '9', '7', '5', '1', '0', '2', '2', '8', '9', '1', '5', '3', '0', '5', '9', '1', '0', '8', '6', '5', '5', '7', '5', '2', '8', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '2', '8', '6', '9', '1', '9', '7', '6', '3', '4', '1', '8', '4', '8', '3', '0', '2', '0', '0', '6', '8', '2', '7', '6', '8', '4', '0', '6', '0', '1', '1', '1', '2', '6', '0', '1', '1', '4', '9', '1', '1', '4', '4', '6', '9', '9', '2', '2', '3', '4', '8', '0', '4', '9', '6', '0', '9', '3', '5', '7', '2', '4', '7', '8', '5', '0', '5', '9', '9', '4', '8', '1', '4', '4', '9', '7', '2', '1', '5', '5', '0', '4', '7', '9', '3', '2', '9', '7', '8', '2', '0', '9', '9', '0', '5', '2', '7', '1', '8', '9', '7', '8', '3', '1', '4', '8', '3', '9'])
noncomputable def fragment0333597Acc00800 : List (String × SourceJson) := (fragment0333597Field007Key00, fragment0333597Field007Value00) :: fragment0333597Acc00700
noncomputable def fragment0333597Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '2', '1', '5', '6', '6', '5', '8', '0', '6', '4', '8', '5', '6', '6', '8', '7', '3', '7', '3', '0', '1', '7', '0', '4', '0', '3', '0', '4', '7', '5', '5', '3', '4', '6', '5', '0', '4', '1', '2', '6', '4', '9', '7', '5', '1', '0', '2', '2', '8', '9', '1', '5', '3', '0', '5', '9', '1', '0', '8', '6', '5', '5', '7', '5', '2', '8', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '2', '8', '6', '9', '1', '9', '7', '6', '3', '4', '1', '8', '4', '8', '3', '0', '2', '0', '0', '6', '8', '2', '7', '6', '8', '4', '0', '6', '0', '1', '1', '1', '2', '6', '0', '1', '1', '4', '9', '1', '1', '4', '4', '6', '9', '9', '2', '2', '3', '4', '8', '0', '4', '9', '6', '0', '9', '3', '5', '7', '2', '4', '7', '8', '5', '0', '5', '9', '9', '4', '8', '1', '4', '4', '9', '7', '2', '1', '5', '5', '0', '4', '7', '9', '3', '2', '9', '7', '8', '2', '0', '9', '9', '0', '5', '2', '7', '1', '8', '9', '7', '8', '3', '1', '4', '8', '3', '9', '"', ',']

theorem object_fragment0333597_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 210) (SourceJson.white (fragment0333597Field007Chars00 ++ tail)) fragment0333597Acc00700 =
      SourceJson.object (fuel + 209) (SourceJson.white tail) fragment0333597Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333597_object_field_007"
  err.flush

noncomputable def fragment0333597Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0333597Field008Value00 : SourceJson := .str (String.ofList ['9', '4', '9', '9', '4', '8', '3', '8', '4', '9', '4', '5', '1', '5'])
noncomputable def fragment0333597Acc00900 : List (String × SourceJson) := (fragment0333597Field008Key00, fragment0333597Field008Value00) :: fragment0333597Acc00800
noncomputable def fragment0333597Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '4', '9', '9', '4', '8', '3', '8', '4', '9', '4', '5', '1', '5', '"', ',']

theorem object_fragment0333597_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 209) (SourceJson.white (fragment0333597Field008Chars00 ++ tail)) fragment0333597Acc00800 =
      SourceJson.object (fuel + 208) (SourceJson.white tail) fragment0333597Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333597_object_field_008"
  err.flush

noncomputable def fragment0333597Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0333597Field009Value00 : SourceJson := .str (String.ofList ['6', '6', '6', '1', '1', '8', '4', '9', '9', '7', '6', '6', '8', '7', '7'])
noncomputable def fragment0333597Acc01000 : List (String × SourceJson) := (fragment0333597Field009Key00, fragment0333597Field009Value00) :: fragment0333597Acc00900
noncomputable def fragment0333597Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '6', '1', '1', '8', '4', '9', '9', '7', '6', '6', '8', '7', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0333597_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 208) (SourceJson.white (fragment0333597Field009Chars00 ++ tail)) fragment0333597Acc00900 =
      .ok (.obj (fragment0333597Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333597_object_field_009"
  err.flush

noncomputable def fragment0333597Chars : List Char := '{' :: (fragment0333597Field000Chars00 ++ fragment0333597Field001Chars00 ++ fragment0333597Field002Chars00 ++ fragment0333597Field003Chars00 ++ fragment0333597Field004Chars00 ++ fragment0333597Field005Chars00 ++ fragment0333597Field006Chars00 ++ fragment0333597Field007Chars00 ++ fragment0333597Field008Chars00 ++ fragment0333597Field009Chars00)
noncomputable def fragment0333597Value : SourceJson := .obj (fragment0333597Acc01000.reverse)

theorem value_fragment0333597 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 218) (fragment0333597Chars ++ tail) =
      .ok (fragment0333597Value, tail) := by
  have hinput : fragment0333597Chars ++ tail = '{' :: (fragment0333597Field000Chars00 ++ (fragment0333597Field001Chars00 ++ (fragment0333597Field002Chars00 ++ (fragment0333597Field003Chars00 ++ (fragment0333597Field004Chars00 ++ (fragment0333597Field005Chars00 ++ (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0333597Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 218) (fragment0333597Chars ++ tail) =
        SourceJson.value (fuel + 218) ('{' :: (fragment0333597Field000Chars00 ++ (fragment0333597Field001Chars00 ++ (fragment0333597Field002Chars00 ++ (fragment0333597Field003Chars00 ++ (fragment0333597Field004Chars00 ++ (fragment0333597Field005Chars00 ++ (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 218)) hinput
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0333597Field000Chars00 ++ (fragment0333597Field001Chars00 ++ (fragment0333597Field002Chars00 ++ (fragment0333597Field003Chars00 ++ (fragment0333597Field004Chars00 ++ (fragment0333597Field005Chars00 ++ (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail)))))))))))) fragment0333597Acc00000 := by rfl
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0333597Field001Chars00 ++ (fragment0333597Field002Chars00 ++ (fragment0333597Field003Chars00 ++ (fragment0333597Field004Chars00 ++ (fragment0333597Field005Chars00 ++ (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail))))))))))) fragment0333597Acc00100 := object_fragment0333597_field_000 fuel (fragment0333597Field001Chars00 ++ (fragment0333597Field002Chars00 ++ (fragment0333597Field003Chars00 ++ (fragment0333597Field004Chars00 ++ (fragment0333597Field005Chars00 ++ (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0333597Field002Chars00 ++ (fragment0333597Field003Chars00 ++ (fragment0333597Field004Chars00 ++ (fragment0333597Field005Chars00 ++ (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail)))))))))) fragment0333597Acc00200 := object_fragment0333597_field_001 fuel (fragment0333597Field002Chars00 ++ (fragment0333597Field003Chars00 ++ (fragment0333597Field004Chars00 ++ (fragment0333597Field005Chars00 ++ (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment0333597Field003Chars00 ++ (fragment0333597Field004Chars00 ++ (fragment0333597Field005Chars00 ++ (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail))))))))) fragment0333597Acc00300 := object_fragment0333597_field_002 fuel (fragment0333597Field003Chars00 ++ (fragment0333597Field004Chars00 ++ (fragment0333597Field005Chars00 ++ (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0333597Field004Chars00 ++ (fragment0333597Field005Chars00 ++ (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail)))))))) fragment0333597Acc00400 := object_fragment0333597_field_003 fuel (fragment0333597Field004Chars00 ++ (fragment0333597Field005Chars00 ++ (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 212) (SourceJson.white (fragment0333597Field005Chars00 ++ (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail))))))) fragment0333597Acc00500 := object_fragment0333597_field_004 fuel (fragment0333597Field005Chars00 ++ (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 211) (SourceJson.white (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail)))))) fragment0333597Acc00600 := object_fragment0333597_field_005 fuel (fragment0333597Field006Chars00 ++ (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 210) (SourceJson.white (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail))))) fragment0333597Acc00700 := object_fragment0333597_field_006 fuel (fragment0333597Field007Chars00 ++ (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 209) (SourceJson.white (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail)))) fragment0333597Acc00800 := object_fragment0333597_field_007 fuel (fragment0333597Field008Chars00 ++ (fragment0333597Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 208) (SourceJson.white (fragment0333597Field009Chars00 ++ (tail))) fragment0333597Acc00900 := object_fragment0333597_field_008 fuel (fragment0333597Field009Chars00 ++ (tail))
    _ = .ok (fragment0333597Value, tail) := object_fragment0333597_field_009 fuel (tail)

noncomputable def fragment0335146Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0335146Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0335146Field000Value00 : SourceJson := .number (String.ofList ['6', '4'])
noncomputable def fragment0335146Acc00100 : List (String × SourceJson) := (fragment0335146Field000Key00, fragment0335146Field000Value00) :: fragment0335146Acc00000
noncomputable def fragment0335146Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '4', ',']

theorem object_fragment0335146_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0335146Field000Chars00 ++ tail)) fragment0335146Acc00000 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0335146Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0335146_object_field_000"
  err.flush

noncomputable def fragment0335146Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0335146Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0335146Acc00200 : List (String × SourceJson) := (fragment0335146Field001Key00, fragment0335146Field001Value00) :: fragment0335146Acc00100
noncomputable def fragment0335146Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0335146_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0335146Field001Chars00 ++ tail)) fragment0335146Acc00100 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0335146Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0335146_object_field_001"
  err.flush

noncomputable def fragment0335146Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0335146Field002Value00 : SourceJson := .str (String.ofList ['6', '2', '1', '3', '7', '7', '7', '1', '7', '4', '1', '2', '2', '3', '3', '3', '8', '4', '8', '9', '0', '4', '8', '6', '3', '6', '2', '1', '4', '6', '1', '7', '9', '/', '2', '6', '7', '3', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0335146Acc00300 : List (String × SourceJson) := (fragment0335146Field002Key00, fragment0335146Field002Value00) :: fragment0335146Acc00200
noncomputable def fragment0335146Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '2', '1', '3', '7', '7', '7', '1', '7', '4', '1', '2', '2', '3', '3', '3', '8', '4', '8', '9', '0', '4', '8', '6', '3', '6', '2', '1', '4', '6', '1', '7', '9', '/', '2', '6', '7', '3', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0335146_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0335146Field002Chars00 ++ tail)) fragment0335146Acc00200 =
      SourceJson.object (fuel + 222) (SourceJson.white tail) fragment0335146Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0335146_object_field_002"
  err.flush

noncomputable def fragment0335146Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0335146Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0335146Acc00400 : List (String × SourceJson) := (fragment0335146Field003Key00, fragment0335146Field003Value00) :: fragment0335146Acc00300
noncomputable def fragment0335146Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0335146_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment0335146Field003Chars00 ++ tail)) fragment0335146Acc00300 =
      SourceJson.object (fuel + 221) (SourceJson.white tail) fragment0335146Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0335146_object_field_003"
  err.flush

noncomputable def fragment0335146Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0335146Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0335146Acc00500 : List (String × SourceJson) := (fragment0335146Field004Key00, fragment0335146Field004Value00) :: fragment0335146Acc00400
noncomputable def fragment0335146Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0335146_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 221) (SourceJson.white (fragment0335146Field004Chars00 ++ tail)) fragment0335146Acc00400 =
      SourceJson.object (fuel + 220) (SourceJson.white tail) fragment0335146Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0335146_object_field_004"
  err.flush

noncomputable def fragment0335146Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0335146Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '4', '4', '8', '2', '7', '1', '9', '7', '0', '7', '1', '/', '1', '4', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '9', '8', '3', '9', '4', '0', '1', '5', '5', '1', '/', '1', '4', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '9', '6', '7', '2', '0', '2', '1', '3', '/', '1', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '5', '6', '3', '8', '9', '0', '9', '9', '3', '1', '/', '4', '9', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '8', '3', '9', '4', '0', '1', '1', '9', '7', '/', '2', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '0', '3', '5', '1', '7', '3', '3', '1', '1', '/', '2', '4', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '7', '1', '4', '3', '8', '2', '1', '8', '5', '3', '/', '7', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '7', '0', '1', '6', '2', '6', '3', '6', '2', '1', '/', '1', '4', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '5', '6', '8', '3', '5', '3', '8', '3', '4', '1', '/', '1', '4', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '1', '8', '9', '3', '8', '5', '2', '7', '2', '7', '/', '4', '9', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0335146Acc00600 : List (String × SourceJson) := (fragment0335146Field005Key00, fragment0335146Field005Value00) :: fragment0335146Acc00500
noncomputable def fragment0335146Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '4', '8', '2', '7', '1', '9', '7', '0', '7', '1', '/', '1', '4', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '9', '8', '3', '9', '4', '0', '1', '5', '5', '1', '/', '1', '4', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '9', '6', '7', '2', '0', '2', '1', '3', '/', '1', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '5', '6', '3', '8', '9', '0', '9', '9', '3', '1', '/', '4', '9', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '8', '3', '9', '4', '0', '1', '1', '9', '7', '/', '2', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '0', '3', '5', '1', '7', '3', '3', '1', '1', '/', '2', '4', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '7', '1', '4', '3', '8', '2', '1', '8', '5', '3', '/', '7', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '7', '0', '1', '6', '2', '6', '3', '6', '2', '1', '/', '1', '4', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '5', '6', '8', '3', '5', '3', '8', '3', '4', '1', '/', '1', '4', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '8', '9', '3', '8', '5', '2', '7', '2', '7', '/', '4', '9', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0335146_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment0335146Field005Chars00 ++ tail)) fragment0335146Acc00500 =
      SourceJson.object (fuel + 219) (SourceJson.white tail) fragment0335146Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0335146_object_field_005"
  err.flush

noncomputable def fragment0335146Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0335146Field006Value00 : SourceJson := .str (String.ofList ['1', '7', '4', '4', '0', '6', '3', '7', '1', '4', '5', '2', '3', '4', '1', '6', '8', '8', '5', '4', '7', '5', '6', '8', '5', '5', '1', '6', '1', '9', '4', '6', '6', '8', '6', '8', '5', '6', '5', '1', '0', '0', '0', '0', '0', '0', '/', '1', '4', '2', '6', '7', '0', '4', '0', '8', '2', '1', '2', '3', '6', '3', '2', '7', '3', '5', '9', '6', '9', '5', '7', '8', '1', '2', '0', '4', '6', '0', '7', '3', '8', '4', '9', '3', '6', '2', '2', '0', '7', '6', '0', '9', '3', '9', '8', '9', '5', '6', '4', '0', '0', '5', '9', '1', '9', '1', '4', '3'])
noncomputable def fragment0335146Acc00700 : List (String × SourceJson) := (fragment0335146Field006Key00, fragment0335146Field006Value00) :: fragment0335146Acc00600
noncomputable def fragment0335146Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '7', '4', '4', '0', '6', '3', '7', '1', '4', '5', '2', '3', '4', '1', '6', '8', '8', '5', '4', '7', '5', '6', '8', '5', '5', '1', '6', '1', '9', '4', '6', '6', '8', '6', '8', '5', '6', '5', '1', '0', '0', '0', '0', '0', '0', '/', '1', '4', '2', '6', '7', '0', '4', '0', '8', '2', '1', '2', '3', '6', '3', '2', '7', '3', '5', '9', '6', '9', '5', '7', '8', '1', '2', '0', '4', '6', '0', '7', '3', '8', '4', '9', '3', '6', '2', '2', '0', '7', '6', '0', '9', '3', '9', '8', '9', '5', '6', '4', '0', '0', '5', '9', '1', '9', '1', '4', '3', '"', ',']

theorem object_fragment0335146_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 219) (SourceJson.white (fragment0335146Field006Chars00 ++ tail)) fragment0335146Acc00600 =
      SourceJson.object (fuel + 218) (SourceJson.white tail) fragment0335146Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0335146_object_field_006"
  err.flush

noncomputable def fragment0335146Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0335146Field007Value00 : SourceJson := .str (String.ofList ['2', '1', '1', '3', '9', '3', '5', '2', '0', '2', '0', '3', '3', '6', '5', '0', '2', '2', '3', '5', '9', '8', '3', '2', '7', '9', '1', '9', '8', '7', '2', '0', '3', '4', '6', '1', '0', '5', '3', '4', '2', '8', '6', '6', '5', '2', '9', '7', '0', '0', '4', '8', '4', '5', '9', '3', '8', '1', '2', '5', '9', '8', '3', '3', '1', '7', '0', '0', '0', '9', '7', '8', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '2', '3', '4', '3', '5', '7', '9', '4', '8', '9', '6', '2', '2', '7', '8', '8', '3', '1', '5', '0', '8', '9', '4', '9', '4', '7', '2', '3', '6', '3', '7', '9', '3', '2', '2', '4', '4', '9', '4', '1', '0', '4', '0', '9', '0', '0', '2', '4', '7', '7', '3', '1', '6', '0', '2', '8', '0', '0', '3', '2', '0', '1', '6', '0', '3', '2', '6', '9', '4', '3', '9', '6', '3', '7', '4', '5', '6', '1', '9', '7', '7', '1', '4', '3', '7', '3', '5', '2', '1', '5', '5', '2', '9', '6', '2', '1', '8', '4', '8', '5', '6', '4', '7', '7', '8', '2', '1', '4', '3', '2', '8', '3', '7'])
noncomputable def fragment0335146Acc00800 : List (String × SourceJson) := (fragment0335146Field007Key00, fragment0335146Field007Value00) :: fragment0335146Acc00700
noncomputable def fragment0335146Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '1', '3', '9', '3', '5', '2', '0', '2', '0', '3', '3', '6', '5', '0', '2', '2', '3', '5', '9', '8', '3', '2', '7', '9', '1', '9', '8', '7', '2', '0', '3', '4', '6', '1', '0', '5', '3', '4', '2', '8', '6', '6', '5', '2', '9', '7', '0', '0', '4', '8', '4', '5', '9', '3', '8', '1', '2', '5', '9', '8', '3', '3', '1', '7', '0', '0', '0', '9', '7', '8', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '2', '3', '4', '3', '5', '7', '9', '4', '8', '9', '6', '2', '2', '7', '8', '8', '3', '1', '5', '0', '8', '9', '4', '9', '4', '7', '2', '3', '6', '3', '7', '9', '3', '2', '2', '4', '4', '9', '4', '1', '0', '4', '0', '9', '0', '0', '2', '4', '7', '7', '3', '1', '6', '0', '2', '8', '0', '0', '3', '2', '0', '1', '6', '0', '3', '2', '6', '9', '4', '3', '9', '6', '3', '7', '4', '5', '6', '1', '9', '7', '7', '1', '4', '3', '7', '3', '5', '2', '1', '5', '5', '2', '9', '6', '2', '1', '8', '4', '8', '5', '6', '4', '7', '7', '8', '2', '1', '4', '3', '2', '8', '3', '7', '"', ',']

theorem object_fragment0335146_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0335146Field007Chars00 ++ tail)) fragment0335146Acc00700 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment0335146Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0335146_object_field_007"
  err.flush

noncomputable def fragment0335146Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0335146Field008Value00 : SourceJson := .str (String.ofList ['9', '6', '8', '5', '1', '8', '7', '3', '5', '8', '8', '1', '1', '9'])
noncomputable def fragment0335146Acc00900 : List (String × SourceJson) := (fragment0335146Field008Key00, fragment0335146Field008Value00) :: fragment0335146Acc00800
noncomputable def fragment0335146Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '6', '8', '5', '1', '8', '7', '3', '5', '8', '8', '1', '1', '9', '"', ',']

theorem object_fragment0335146_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0335146Field008Chars00 ++ tail)) fragment0335146Acc00800 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0335146Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0335146_object_field_008"
  err.flush

noncomputable def fragment0335146Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0335146Field009Value00 : SourceJson := .str (String.ofList ['7', '4', '9', '5', '8', '0', '8', '8', '8', '8', '1', '4', '7', '5', '7'])
noncomputable def fragment0335146Acc01000 : List (String × SourceJson) := (fragment0335146Field009Key00, fragment0335146Field009Value00) :: fragment0335146Acc00900
noncomputable def fragment0335146Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '4', '9', '5', '8', '0', '8', '8', '8', '8', '1', '4', '7', '5', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0335146_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0335146Field009Chars00 ++ tail)) fragment0335146Acc00900 =
      .ok (.obj (fragment0335146Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0335146_object_field_009"
  err.flush

noncomputable def fragment0335146Chars : List Char := '{' :: (fragment0335146Field000Chars00 ++ fragment0335146Field001Chars00 ++ fragment0335146Field002Chars00 ++ fragment0335146Field003Chars00 ++ fragment0335146Field004Chars00 ++ fragment0335146Field005Chars00 ++ fragment0335146Field006Chars00 ++ fragment0335146Field007Chars00 ++ fragment0335146Field008Chars00 ++ fragment0335146Field009Chars00)
noncomputable def fragment0335146Value : SourceJson := .obj (fragment0335146Acc01000.reverse)

theorem value_fragment0335146 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 226) (fragment0335146Chars ++ tail) =
      .ok (fragment0335146Value, tail) := by
  have hinput : fragment0335146Chars ++ tail = '{' :: (fragment0335146Field000Chars00 ++ (fragment0335146Field001Chars00 ++ (fragment0335146Field002Chars00 ++ (fragment0335146Field003Chars00 ++ (fragment0335146Field004Chars00 ++ (fragment0335146Field005Chars00 ++ (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0335146Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 226) (fragment0335146Chars ++ tail) =
        SourceJson.value (fuel + 226) ('{' :: (fragment0335146Field000Chars00 ++ (fragment0335146Field001Chars00 ++ (fragment0335146Field002Chars00 ++ (fragment0335146Field003Chars00 ++ (fragment0335146Field004Chars00 ++ (fragment0335146Field005Chars00 ++ (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 226)) hinput
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0335146Field000Chars00 ++ (fragment0335146Field001Chars00 ++ (fragment0335146Field002Chars00 ++ (fragment0335146Field003Chars00 ++ (fragment0335146Field004Chars00 ++ (fragment0335146Field005Chars00 ++ (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail)))))))))))) fragment0335146Acc00000 := by rfl
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0335146Field001Chars00 ++ (fragment0335146Field002Chars00 ++ (fragment0335146Field003Chars00 ++ (fragment0335146Field004Chars00 ++ (fragment0335146Field005Chars00 ++ (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail))))))))))) fragment0335146Acc00100 := object_fragment0335146_field_000 fuel (fragment0335146Field001Chars00 ++ (fragment0335146Field002Chars00 ++ (fragment0335146Field003Chars00 ++ (fragment0335146Field004Chars00 ++ (fragment0335146Field005Chars00 ++ (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0335146Field002Chars00 ++ (fragment0335146Field003Chars00 ++ (fragment0335146Field004Chars00 ++ (fragment0335146Field005Chars00 ++ (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail)))))))))) fragment0335146Acc00200 := object_fragment0335146_field_001 fuel (fragment0335146Field002Chars00 ++ (fragment0335146Field003Chars00 ++ (fragment0335146Field004Chars00 ++ (fragment0335146Field005Chars00 ++ (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment0335146Field003Chars00 ++ (fragment0335146Field004Chars00 ++ (fragment0335146Field005Chars00 ++ (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail))))))))) fragment0335146Acc00300 := object_fragment0335146_field_002 fuel (fragment0335146Field003Chars00 ++ (fragment0335146Field004Chars00 ++ (fragment0335146Field005Chars00 ++ (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 221) (SourceJson.white (fragment0335146Field004Chars00 ++ (fragment0335146Field005Chars00 ++ (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail)))))))) fragment0335146Acc00400 := object_fragment0335146_field_003 fuel (fragment0335146Field004Chars00 ++ (fragment0335146Field005Chars00 ++ (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment0335146Field005Chars00 ++ (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail))))))) fragment0335146Acc00500 := object_fragment0335146_field_004 fuel (fragment0335146Field005Chars00 ++ (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 219) (SourceJson.white (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail)))))) fragment0335146Acc00600 := object_fragment0335146_field_005 fuel (fragment0335146Field006Chars00 ++ (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail))))) fragment0335146Acc00700 := object_fragment0335146_field_006 fuel (fragment0335146Field007Chars00 ++ (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail)))) fragment0335146Acc00800 := object_fragment0335146_field_007 fuel (fragment0335146Field008Chars00 ++ (fragment0335146Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0335146Field009Chars00 ++ (tail))) fragment0335146Acc00900 := object_fragment0335146_field_008 fuel (fragment0335146Field009Chars00 ++ (tail))
    _ = .ok (fragment0335146Value, tail) := object_fragment0335146_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0063_before_reader"
  err.flush

noncomputable def chunk0063LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0063SuffixChars00 : List Char := [',']
noncomputable def chunk0063Chars00 : List Char := chunk0063LeadChars00 ++ fragment0333597Chars ++ chunk0063SuffixChars00
noncomputable def chunk0063Push00 (acc : List SourceJson) : List SourceJson := fragment0333597Value :: acc

noncomputable def chunk0063AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0063_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 541)
      (SourceJson.white (chunk0063LeadChars00 ++ (fragment0333597Chars ++ rest))) acc =
      (SourceJson.value (fuel + 540) (fragment0333597Chars ++ rest)).bind
        (chunk0063AfterValue00 (fuel + 540) acc) := by rfl

theorem array_chunk0063 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 541) (SourceJson.white (chunk0063Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 540) (SourceJson.white tail) (chunk0063Push00 acc) := by
  have hinput : chunk0063Chars00 ++ tail = chunk0063LeadChars00 ++ (fragment0333597Chars ++ (chunk0063SuffixChars00 ++ tail)) := by
    simp only [chunk0063Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 541) (SourceJson.white (chunk0063Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 541)
          (SourceJson.white (chunk0063LeadChars00 ++ (fragment0333597Chars ++ (chunk0063SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 541) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 540) (fragment0333597Chars ++ (chunk0063SuffixChars00 ++ tail))).bind
        (chunk0063AfterValue00 (fuel + 540) acc) := array_chunk0063_head fuel (chunk0063SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0333597Value, chunk0063SuffixChars00 ++ tail)).bind
        (chunk0063AfterValue00 (fuel + 540) acc) :=
      congrArg (fun result => result.bind (chunk0063AfterValue00 (fuel + 540) acc))
        (value_fragment0333597 (fuel + 322) (chunk0063SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 540) (SourceJson.white tail) (chunk0063Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0063_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0064_before_reader"
  err.flush

noncomputable def chunk0064LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0064SuffixChars00 : List Char := [',']
noncomputable def chunk0064Chars00 : List Char := chunk0064LeadChars00 ++ fragment0335146Chars ++ chunk0064SuffixChars00
noncomputable def chunk0064Push00 (acc : List SourceJson) : List SourceJson := fragment0335146Value :: acc

noncomputable def chunk0064AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0064_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 540)
      (SourceJson.white (chunk0064LeadChars00 ++ (fragment0335146Chars ++ rest))) acc =
      (SourceJson.value (fuel + 539) (fragment0335146Chars ++ rest)).bind
        (chunk0064AfterValue00 (fuel + 539) acc) := by rfl

theorem array_chunk0064 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 540) (SourceJson.white (chunk0064Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 539) (SourceJson.white tail) (chunk0064Push00 acc) := by
  have hinput : chunk0064Chars00 ++ tail = chunk0064LeadChars00 ++ (fragment0335146Chars ++ (chunk0064SuffixChars00 ++ tail)) := by
    simp only [chunk0064Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 540) (SourceJson.white (chunk0064Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 540)
          (SourceJson.white (chunk0064LeadChars00 ++ (fragment0335146Chars ++ (chunk0064SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 540) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 539) (fragment0335146Chars ++ (chunk0064SuffixChars00 ++ tail))).bind
        (chunk0064AfterValue00 (fuel + 539) acc) := array_chunk0064_head fuel (chunk0064SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0335146Value, chunk0064SuffixChars00 ++ tail)).bind
        (chunk0064AfterValue00 (fuel + 539) acc) :=
      congrArg (fun result => result.bind (chunk0064AfterValue00 (fuel + 539) acc))
        (value_fragment0335146 (fuel + 313) (chunk0064SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 539) (SourceJson.white tail) (chunk0064Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0064_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0063Chars00 ++ chunk0064Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0064Push00 (chunk0063Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 541) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 539) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0063Chars00 ++ (chunk0064Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 541) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 541) (SourceJson.white (chunk0063Chars00 ++ (chunk0064Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 541) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 540) (SourceJson.white (chunk0064Chars00 ++ (tail))) (chunk0063Push00 (acc)) := array_chunk0063 fuel (chunk0064Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 539) (SourceJson.white tail) (blockPush acc) := array_chunk0064 fuel (tail) (chunk0063Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 333591).take 3101 = blockChars := by rfl

theorem block_original_split : sourceRest 333591 = blockChars ++ sourceRest 336692 := by
  calc
    sourceRest 333591 = (sourceRest 333591).take 3101 ++ (sourceRest 333591).drop 3101 :=
      (List.take_append_drop 3101 (sourceRest 333591)).symm
    _ = blockChars ++ (sourceRest 333591).drop 3101 :=
      congrArg (fun part => part ++ (sourceRest 333591).drop 3101) block_original_prefix
    _ = blockChars ++ sourceRest 336692 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 333591 3101)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 541) (SourceJson.white (sourceRest 333591)) acc =
      SourceJson.array (fuel + 539) (SourceJson.white (sourceRest 336692)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 541) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 336692) acc)

#print axioms object_fragment0333597_field_000
#print axioms object_fragment0333597_field_001
#print axioms object_fragment0333597_field_002
#print axioms object_fragment0333597_field_003
#print axioms object_fragment0333597_field_004
#print axioms object_fragment0333597_field_005
#print axioms object_fragment0333597_field_006
#print axioms object_fragment0333597_field_007
#print axioms object_fragment0333597_field_008
#print axioms object_fragment0333597_field_009
#print axioms value_fragment0333597
#print axioms object_fragment0335146_field_000
#print axioms object_fragment0335146_field_001
#print axioms object_fragment0335146_field_002
#print axioms object_fragment0335146_field_003
#print axioms object_fragment0335146_field_004
#print axioms object_fragment0335146_field_005
#print axioms object_fragment0335146_field_006
#print axioms object_fragment0335146_field_007
#print axioms object_fragment0335146_field_008
#print axioms object_fragment0335146_field_009
#print axioms value_fragment0335146
#print axioms array_chunk0063_head
#print axioms array_chunk0063
#print axioms array_chunk0064_head
#print axioms array_chunk0064
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock032

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
