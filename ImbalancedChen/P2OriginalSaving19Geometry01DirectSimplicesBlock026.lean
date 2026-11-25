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

namespace SimplicesBlock026

noncomputable def fragment0313535Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0313535Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0313535Field000Value00 : SourceJson := .number (String.ofList ['5', '1'])
noncomputable def fragment0313535Acc00100 : List (String × SourceJson) := (fragment0313535Field000Key00, fragment0313535Field000Value00) :: fragment0313535Acc00000
noncomputable def fragment0313535Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '1', ',']

theorem object_fragment0313535_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 390) (SourceJson.white (fragment0313535Field000Chars00 ++ tail)) fragment0313535Acc00000 =
      SourceJson.object (fuel + 389) (SourceJson.white tail) fragment0313535Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313535_object_field_000"
  err.flush

noncomputable def fragment0313535Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0313535Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0313535Acc00200 : List (String × SourceJson) := (fragment0313535Field001Key00, fragment0313535Field001Value00) :: fragment0313535Acc00100
noncomputable def fragment0313535Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0313535_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 389) (SourceJson.white (fragment0313535Field001Chars00 ++ tail)) fragment0313535Acc00100 =
      SourceJson.object (fuel + 388) (SourceJson.white tail) fragment0313535Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313535_object_field_001"
  err.flush

noncomputable def fragment0313535Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0313535Field002Value00 : SourceJson := .str (String.ofList ['7', '9', '7', '0', '3', '6', '0', '4', '8', '4', '9', '7', '0', '2', '2', '4', '5', '9', '2', '0', '4', '4', '1', '9', '9', '0', '7', '8', '0', '6', '5', '9', '1', '9', '2', '8', '6', '3', '1', '2', '6', '9', '0', '1', '4', '9', '/', '1', '9', '3', '4', '0', '1', '9', '7', '2', '2', '4', '3', '6', '6', '7', '3', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0313535Acc00300 : List (String × SourceJson) := (fragment0313535Field002Key00, fragment0313535Field002Value00) :: fragment0313535Acc00200
noncomputable def fragment0313535Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '9', '7', '0', '3', '6', '0', '4', '8', '4', '9', '7', '0', '2', '2', '4', '5', '9', '2', '0', '4', '4', '1', '9', '9', '0', '7', '8', '0', '6', '5', '9', '1', '9', '2', '8', '6', '3', '1', '2', '6', '9', '0', '1', '4', '9', '/', '1', '9', '3', '4', '0', '1', '9', '7', '2', '2', '4', '3', '6', '6', '7', '3', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0313535_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 388) (SourceJson.white (fragment0313535Field002Chars00 ++ tail)) fragment0313535Acc00200 =
      SourceJson.object (fuel + 387) (SourceJson.white tail) fragment0313535Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313535_object_field_002"
  err.flush

noncomputable def fragment0313535Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0313535Field003Value00 : SourceJson := .str (String.ofList ['3', '4', '6', '3', '0', '0', '6', '1', '/', '4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0'])
noncomputable def fragment0313535Acc00400 : List (String × SourceJson) := (fragment0313535Field003Key00, fragment0313535Field003Value00) :: fragment0313535Acc00300
noncomputable def fragment0313535Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '4', '6', '3', '0', '0', '6', '1', '/', '4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0313535_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 387) (SourceJson.white (fragment0313535Field003Chars00 ++ tail)) fragment0313535Acc00300 =
      SourceJson.object (fuel + 386) (SourceJson.white tail) fragment0313535Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313535_object_field_003"
  err.flush

noncomputable def fragment0313535Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0313535Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['8', '0', '7', '/', '1', '7', '7', '9', '2'])]
noncomputable def fragment0313535Acc00500 : List (String × SourceJson) := (fragment0313535Field004Key00, fragment0313535Field004Value00) :: fragment0313535Acc00400
noncomputable def fragment0313535Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '7', '/', '1', '7', '7', '9', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0313535_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 386) (SourceJson.white (fragment0313535Field004Chars00 ++ tail)) fragment0313535Acc00400 =
      SourceJson.object (fuel + 385) (SourceJson.white tail) fragment0313535Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313535_object_field_004"
  err.flush

noncomputable def fragment0313535Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0313535Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '0', '8', '4', '1', '9', '4', '5', '0', '4', '6', '5', '8', '7', '0', '9', '8', '7', '1', '/', '6', '4', '0', '2', '0', '5', '9', '3', '7', '7', '0', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '0', '3', '8', '8', '8', '3', '4', '1', '1', '3', '1', '6', '8', '5', '4', '7', '4', '3', '/', '2', '2', '4', '0', '7', '2', '0', '7', '8', '1', '9', '7', '4', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '6', '6', '8', '3', '7', '8', '5', '8', '2', '8', '3', '0', '0', '5', '7', '2', '3', '2', '3', '/', '2', '6', '8', '8', '8', '6', '4', '9', '3', '8', '3', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '7', '9', '0', '2', '8', '4', '1', '7', '4', '9', '9', '4', '2', '4', '2', '1', '1', '/', '2', '5', '2', '0', '8', '1', '0', '8', '7', '9', '7', '2', '1', '3', '1', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '7', '7', '6', '8', '4', '5', '5', '7', '1', '8', '5', '3', '5', '6', '6', '6', '2', '3', '/', '1', '3', '4', '4', '4', '3', '2', '4', '6', '9', '1', '8', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '6', '3', '8', '6', '2', '2', '5', '1', '0', '7', '1', '9', '8', '2', '4', '7', '2', '3', '/', '2', '6', '8', '8', '8', '6', '4', '9', '3', '8', '3', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '7', '9', '3', '1', '8', '4', '6', '7', '8', '9', '4', '2', '1', '6', '8', '7', '9', '/', '1', '4', '1', '5', '1', '9', '2', '0', '7', '2', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '6', '4', '7', '1', '2', '8', '4', '2', '8', '3', '0', '7', '8', '6', '8', '5', '3', '7', '1', '/', '2', '6', '8', '8', '8', '6', '4', '9', '3', '8', '3', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '8', '7', '6', '5', '2', '1', '2', '3', '2', '1', '4', '8', '9', '2', '5', '8', '9', '3', '/', '1', '3', '4', '4', '4', '3', '2', '4', '6', '9', '1', '8', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '1', '9', '2', '1', '1', '7', '1', '7', '5', '5', '3', '6', '9', '0', '1', '2', '6', '2', '1', '/', '8', '0', '6', '6', '5', '9', '4', '8', '1', '5', '1', '0', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0313535Acc00600 : List (String × SourceJson) := (fragment0313535Field005Key00, fragment0313535Field005Value00) :: fragment0313535Acc00500
noncomputable def fragment0313535Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '8', '4', '1', '9', '4', '5', '0', '4', '6', '5', '8', '7', '0', '9', '8', '7', '1', '/', '6', '4', '0', '2', '0', '5', '9', '3', '7', '7', '0', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '0', '3', '8', '8', '8', '3', '4', '1', '1', '3', '1', '6', '8', '5', '4', '7', '4', '3', '/', '2', '2', '4', '0', '7', '2', '0', '7', '8', '1', '9', '7', '4', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '6', '6', '8', '3', '7', '8', '5', '8', '2', '8', '3', '0', '0', '5', '7', '2', '3', '2', '3', '/', '2', '6', '8', '8', '8', '6', '4', '9', '3', '8', '3', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '7', '9', '0', '2', '8', '4', '1', '7', '4', '9', '9', '4', '2', '4', '2', '1', '1', '/', '2', '5', '2', '0', '8', '1', '0', '8', '7', '9', '7', '2', '1', '3', '1', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '7', '7', '6', '8', '4', '5', '5', '7', '1', '8', '5', '3', '5', '6', '6', '6', '2', '3', '/', '1', '3', '4', '4', '4', '3', '2', '4', '6', '9', '1', '8', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '6', '3', '8', '6', '2', '2', '5', '1', '0', '7', '1', '9', '8', '2', '4', '7', '2', '3', '/', '2', '6', '8', '8', '8', '6', '4', '9', '3', '8', '3', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '7', '9', '3', '1', '8', '4', '6', '7', '8', '9', '4', '2', '1', '6', '8', '7', '9', '/', '1', '4', '1', '5', '1', '9', '2', '0', '7', '2', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '4', '7', '1', '2', '8', '4', '2', '8', '3', '0', '7', '8', '6', '8', '5', '3', '7', '1', '/', '2', '6', '8', '8', '8', '6', '4', '9', '3', '8', '3', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '8', '7', '6', '5', '2', '1', '2', '3', '2', '1', '4', '8', '9', '2', '5', '8', '9', '3', '/', '1', '3', '4', '4', '4', '3', '2', '4', '6', '9', '1', '8', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '1', '9', '2', '1', '1', '7', '1', '7', '5', '5', '3', '6', '9', '0', '1', '2', '6', '2', '1', '/', '8', '0', '6', '6', '5', '9', '4', '8', '1', '5', '1', '0', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0313535_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 385) (SourceJson.white (fragment0313535Field005Chars00 ++ tail)) fragment0313535Acc00500 =
      SourceJson.object (fuel + 384) (SourceJson.white tail) fragment0313535Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313535_object_field_005"
  err.flush

noncomputable def fragment0313535Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0313535Field006Value00 : SourceJson := .str (String.ofList ['2', '7', '6', '0', '1', '4', '0', '6', '9', '7', '8', '6', '5', '0', '8', '4', '6', '0', '8', '0', '6', '1', '9', '0', '7', '2', '8', '7', '6', '9', '5', '6', '6', '5', '4', '6', '9', '0', '6', '0', '8', '4', '9', '2', '4', '9', '3', '3', '9', '6', '9', '0', '8', '9', '/', '1', '4', '0', '8', '4', '3', '7', '3', '8', '2', '9', '4', '8', '2', '2', '6', '4', '1', '4', '2', '1', '3', '4', '5', '4', '1', '4', '1', '4', '2', '1', '1', '5', '1', '3', '0', '2', '1', '7', '6', '0', '7', '7', '2', '1', '1', '2', '0', '8', '3', '9', '3', '9', '8', '3', '3', '7', '7', '4', '1', '9', '6', '8', '7', '5', '0'])
noncomputable def fragment0313535Acc00700 : List (String × SourceJson) := (fragment0313535Field006Key00, fragment0313535Field006Value00) :: fragment0313535Acc00600
noncomputable def fragment0313535Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '7', '6', '0', '1', '4', '0', '6', '9', '7', '8', '6', '5', '0', '8', '4', '6', '0', '8', '0', '6', '1', '9', '0', '7', '2', '8', '7', '6', '9', '5', '6', '6', '5', '4', '6', '9', '0', '6', '0', '8', '4', '9', '2', '4', '9', '3', '3', '9', '6', '9', '0', '8', '9', '/', '1', '4', '0', '8', '4', '3', '7', '3', '8', '2', '9', '4', '8', '2', '2', '6', '4', '1', '4', '2', '1', '3', '4', '5', '4', '1', '4', '1', '4', '2', '1', '1', '5', '1', '3', '0', '2', '1', '7', '6', '0', '7', '7', '2', '1', '1', '2', '0', '8', '3', '9', '3', '9', '8', '3', '3', '7', '7', '4', '1', '9', '6', '8', '7', '5', '0', '"', ',']

theorem object_fragment0313535_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 384) (SourceJson.white (fragment0313535Field006Chars00 ++ tail)) fragment0313535Acc00600 =
      SourceJson.object (fuel + 383) (SourceJson.white tail) fragment0313535Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313535_object_field_006"
  err.flush

noncomputable def fragment0313535Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0313535Field007Value00 : SourceJson := .str (String.ofList ['3', '0', '6', '4', '5', '9', '8', '7', '6', '3', '6', '0', '1', '4', '0', '9', '5', '3', '2', '8', '3', '5', '2', '5', '7', '7', '9', '6', '7', '3', '7', '7', '0', '9', '3', '9', '0', '4', '4', '3', '7', '8', '0', '7', '9', '4', '2', '2', '1', '3', '5', '1', '9', '0', '9', '6', '0', '8', '7', '8', '7', '1', '8', '8', '0', '4', '0', '1', '0', '0', '7', '2', '8', '4', '5', '6', '7', '5', '1', '0', '7', '8', '5', '8', '9', '4', '1', '0', '7', '9', '6', '8', '3', '0', '7', '9', '6', '5', '3', '0', '3', '1', '3', '7', '6', '2', '3', '0', '8', '5', '4', '7', '5', '4', '3', '6', '6', '4', '2', '3', '7', '9', '6', '7', '9', '4', '1', '5', '0', '0', '1', '2', '7', '1', '6', '2', '1', '6', '1', '0', '5', '7', '5', '2', '0', '0', '8', '6', '8', '3', '7', '3', '9', '7', '6', '3', '9', '7', '8', '5', '7', '2', '0', '3', '4', '8', '3', '5', '8', '1', '5', '4', '2', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '/', '1', '7', '3', '2', '9', '7', '6', '4', '0', '3', '4', '1', '3', '3', '7', '1', '9', '8', '5', '0', '3', '0', '7', '2', '6', '3', '2', '4', '9', '5', '0', '3', '3', '8', '2', '0', '6', '7', '0', '4', '5', '6', '5', '4', '8', '2', '9', '9', '2', '9', '3', '5', '7', '4', '3', '5', '5', '5', '2', '4', '9', '5', '0', '5', '7', '5', '1', '5', '6', '6', '8', '2', '9', '7', '7', '2', '5', '8', '8', '1', '8', '0', '6', '8', '1', '2', '7', '3', '5', '5', '9', '1', '4', '1', '9', '3', '2', '3', '6', '8', '0', '8', '9', '7', '8', '0', '2', '9', '5', '7', '9', '3', '8', '9', '5', '1', '0', '6', '3', '3', '8', '4', '8', '3', '6', '7', '9', '1', '5', '8', '2', '1', '5', '6', '6', '7', '7', '7', '8', '5', '1', '8', '6', '2', '2', '6', '5', '7', '5', '2', '4', '5', '6', '4', '6', '1', '4', '7', '1', '4', '1', '0', '4', '1', '0', '5', '2', '2', '1', '7', '9', '8', '9', '3', '0', '5', '6', '0', '1', '4', '5', '8', '2', '7', '5', '3', '7', '9', '8', '6', '8', '1', '8', '4', '7'])
noncomputable def fragment0313535Acc00800 : List (String × SourceJson) := (fragment0313535Field007Key00, fragment0313535Field007Value00) :: fragment0313535Acc00700
noncomputable def fragment0313535Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '6', '4', '5', '9', '8', '7', '6', '3', '6', '0', '1', '4', '0', '9', '5', '3', '2', '8', '3', '5', '2', '5', '7', '7', '9', '6', '7', '3', '7', '7', '0', '9', '3', '9', '0', '4', '4', '3', '7', '8', '0', '7', '9', '4', '2', '2', '1', '3', '5', '1', '9', '0', '9', '6', '0', '8', '7', '8', '7', '1', '8', '8', '0', '4', '0', '1', '0', '0', '7', '2', '8', '4', '5', '6', '7', '5', '1', '0', '7', '8', '5', '8', '9', '4', '1', '0', '7', '9', '6', '8', '3', '0', '7', '9', '6', '5', '3', '0', '3', '1', '3', '7', '6', '2', '3', '0', '8', '5', '4', '7', '5', '4', '3', '6', '6', '4', '2', '3', '7', '9', '6', '7', '9', '4', '1', '5', '0', '0', '1', '2', '7', '1', '6', '2', '1', '6', '1', '0', '5', '7', '5', '2', '0', '0', '8', '6', '8', '3', '7', '3', '9', '7', '6', '3', '9', '7', '8', '5', '7', '2', '0', '3', '4', '8', '3', '5', '8', '1', '5', '4', '2', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '/', '1', '7', '3', '2', '9', '7', '6', '4', '0', '3', '4', '1', '3', '3', '7', '1', '9', '8', '5', '0', '3', '0', '7', '2', '6', '3', '2', '4', '9', '5', '0', '3', '3', '8', '2', '0', '6', '7', '0', '4', '5', '6', '5', '4', '8', '2', '9', '9', '2', '9', '3', '5', '7', '4', '3', '5', '5', '5', '2', '4', '9', '5', '0', '5', '7', '5', '1', '5', '6', '6', '8', '2', '9', '7', '7', '2', '5', '8', '8', '1', '8', '0', '6', '8', '1', '2', '7', '3', '5', '5', '9', '1', '4', '1', '9', '3', '2', '3', '6', '8', '0', '8', '9', '7', '8', '0', '2', '9', '5', '7', '9', '3', '8', '9', '5', '1', '0', '6', '3', '3', '8', '4', '8', '3', '6', '7', '9', '1', '5', '8', '2', '1', '5', '6', '6', '7', '7', '7', '8', '5', '1', '8', '6', '2', '2', '6', '5', '7', '5', '2', '4', '5', '6', '4', '6', '1', '4', '7', '1', '4', '1', '0', '4', '1', '0', '5', '2', '2', '1', '7', '9', '8', '9', '3', '0', '5', '6', '0', '1', '4', '5', '8', '2', '7', '5', '3', '7', '9', '8', '6', '8', '1', '8', '4', '7', '"', ',']

theorem object_fragment0313535_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 383) (SourceJson.white (fragment0313535Field007Chars00 ++ tail)) fragment0313535Acc00700 =
      SourceJson.object (fuel + 382) (SourceJson.white tail) fragment0313535Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313535_object_field_007"
  err.flush

noncomputable def fragment0313535Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0313535Field008Value00 : SourceJson := .str (String.ofList ['1', '5', '5', '2', '6', '4', '8', '9', '0', '3', '1', '0', '5', '1', '8', '3', '5', '2'])
noncomputable def fragment0313535Acc00900 : List (String × SourceJson) := (fragment0313535Field008Key00, fragment0313535Field008Value00) :: fragment0313535Acc00800
noncomputable def fragment0313535Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '5', '2', '6', '4', '8', '9', '0', '3', '1', '0', '5', '1', '8', '3', '5', '2', '"', ',']

theorem object_fragment0313535_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 382) (SourceJson.white (fragment0313535Field008Chars00 ++ tail)) fragment0313535Acc00800 =
      SourceJson.object (fuel + 381) (SourceJson.white tail) fragment0313535Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313535_object_field_008"
  err.flush

noncomputable def fragment0313535Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0313535Field009Value00 : SourceJson := .str (String.ofList ['1', '4', '0', '1', '0', '7', '2', '3', '3', '0', '8', '4', '8', '7', '5', '2', '0', '4', '7'])
noncomputable def fragment0313535Acc01000 : List (String × SourceJson) := (fragment0313535Field009Key00, fragment0313535Field009Value00) :: fragment0313535Acc00900
noncomputable def fragment0313535Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '0', '1', '0', '7', '2', '3', '3', '0', '8', '4', '8', '7', '5', '2', '0', '4', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0313535_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 381) (SourceJson.white (fragment0313535Field009Chars00 ++ tail)) fragment0313535Acc00900 =
      .ok (.obj (fragment0313535Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313535_object_field_009"
  err.flush

noncomputable def fragment0313535Chars : List Char := '{' :: (fragment0313535Field000Chars00 ++ fragment0313535Field001Chars00 ++ fragment0313535Field002Chars00 ++ fragment0313535Field003Chars00 ++ fragment0313535Field004Chars00 ++ fragment0313535Field005Chars00 ++ fragment0313535Field006Chars00 ++ fragment0313535Field007Chars00 ++ fragment0313535Field008Chars00 ++ fragment0313535Field009Chars00)
noncomputable def fragment0313535Value : SourceJson := .obj (fragment0313535Acc01000.reverse)

theorem value_fragment0313535 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 391) (fragment0313535Chars ++ tail) =
      .ok (fragment0313535Value, tail) := by
  have hinput : fragment0313535Chars ++ tail = '{' :: (fragment0313535Field000Chars00 ++ (fragment0313535Field001Chars00 ++ (fragment0313535Field002Chars00 ++ (fragment0313535Field003Chars00 ++ (fragment0313535Field004Chars00 ++ (fragment0313535Field005Chars00 ++ (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0313535Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 391) (fragment0313535Chars ++ tail) =
        SourceJson.value (fuel + 391) ('{' :: (fragment0313535Field000Chars00 ++ (fragment0313535Field001Chars00 ++ (fragment0313535Field002Chars00 ++ (fragment0313535Field003Chars00 ++ (fragment0313535Field004Chars00 ++ (fragment0313535Field005Chars00 ++ (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 391)) hinput
    _ = SourceJson.object (fuel + 390) (SourceJson.white (fragment0313535Field000Chars00 ++ (fragment0313535Field001Chars00 ++ (fragment0313535Field002Chars00 ++ (fragment0313535Field003Chars00 ++ (fragment0313535Field004Chars00 ++ (fragment0313535Field005Chars00 ++ (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail)))))))))))) fragment0313535Acc00000 := by rfl
    _ = SourceJson.object (fuel + 389) (SourceJson.white (fragment0313535Field001Chars00 ++ (fragment0313535Field002Chars00 ++ (fragment0313535Field003Chars00 ++ (fragment0313535Field004Chars00 ++ (fragment0313535Field005Chars00 ++ (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail))))))))))) fragment0313535Acc00100 := object_fragment0313535_field_000 fuel (fragment0313535Field001Chars00 ++ (fragment0313535Field002Chars00 ++ (fragment0313535Field003Chars00 ++ (fragment0313535Field004Chars00 ++ (fragment0313535Field005Chars00 ++ (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 388) (SourceJson.white (fragment0313535Field002Chars00 ++ (fragment0313535Field003Chars00 ++ (fragment0313535Field004Chars00 ++ (fragment0313535Field005Chars00 ++ (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail)))))))))) fragment0313535Acc00200 := object_fragment0313535_field_001 fuel (fragment0313535Field002Chars00 ++ (fragment0313535Field003Chars00 ++ (fragment0313535Field004Chars00 ++ (fragment0313535Field005Chars00 ++ (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 387) (SourceJson.white (fragment0313535Field003Chars00 ++ (fragment0313535Field004Chars00 ++ (fragment0313535Field005Chars00 ++ (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail))))))))) fragment0313535Acc00300 := object_fragment0313535_field_002 fuel (fragment0313535Field003Chars00 ++ (fragment0313535Field004Chars00 ++ (fragment0313535Field005Chars00 ++ (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 386) (SourceJson.white (fragment0313535Field004Chars00 ++ (fragment0313535Field005Chars00 ++ (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail)))))))) fragment0313535Acc00400 := object_fragment0313535_field_003 fuel (fragment0313535Field004Chars00 ++ (fragment0313535Field005Chars00 ++ (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 385) (SourceJson.white (fragment0313535Field005Chars00 ++ (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail))))))) fragment0313535Acc00500 := object_fragment0313535_field_004 fuel (fragment0313535Field005Chars00 ++ (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 384) (SourceJson.white (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail)))))) fragment0313535Acc00600 := object_fragment0313535_field_005 fuel (fragment0313535Field006Chars00 ++ (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 383) (SourceJson.white (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail))))) fragment0313535Acc00700 := object_fragment0313535_field_006 fuel (fragment0313535Field007Chars00 ++ (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 382) (SourceJson.white (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail)))) fragment0313535Acc00800 := object_fragment0313535_field_007 fuel (fragment0313535Field008Chars00 ++ (fragment0313535Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 381) (SourceJson.white (fragment0313535Field009Chars00 ++ (tail))) fragment0313535Acc00900 := object_fragment0313535_field_008 fuel (fragment0313535Field009Chars00 ++ (tail))
    _ = .ok (fragment0313535Value, tail) := object_fragment0313535_field_009 fuel (tail)

noncomputable def fragment0315463Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0315463Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0315463Field000Value00 : SourceJson := .number (String.ofList ['5', '2'])
noncomputable def fragment0315463Acc00100 : List (String × SourceJson) := (fragment0315463Field000Key00, fragment0315463Field000Value00) :: fragment0315463Acc00000
noncomputable def fragment0315463Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '2', ',']

theorem object_fragment0315463_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0315463Field000Chars00 ++ tail)) fragment0315463Acc00000 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0315463Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315463_object_field_000"
  err.flush

noncomputable def fragment0315463Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0315463Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['0'])]
noncomputable def fragment0315463Acc00200 : List (String × SourceJson) := (fragment0315463Field001Key00, fragment0315463Field001Value00) :: fragment0315463Acc00100
noncomputable def fragment0315463Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0315463_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0315463Field001Chars00 ++ tail)) fragment0315463Acc00100 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0315463Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315463_object_field_001"
  err.flush

noncomputable def fragment0315463Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0315463Field002Value00 : SourceJson := .str (String.ofList ['2', '0', '8', '8', '0', '4', '7', '4', '1', '8', '5', '2', '9', '1', '3', '3', '9', '3', '0', '8', '7', '3', '8', '3', '4', '1', '2', '0', '0', '4', '6', '7', '7', '7', '0', '3', '2', '2', '8', '6', '0', '3', '1', '3', '3', '9', '/', '2', '7', '4', '3', '1', '5', '0', '4', '2', '2', '6', '3', '9', '7', '7', '1', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0315463Acc00300 : List (String × SourceJson) := (fragment0315463Field002Key00, fragment0315463Field002Value00) :: fragment0315463Acc00200
noncomputable def fragment0315463Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '0', '8', '8', '0', '4', '7', '4', '1', '8', '5', '2', '9', '1', '3', '3', '9', '3', '0', '8', '7', '3', '8', '3', '4', '1', '2', '0', '0', '4', '6', '7', '7', '7', '0', '3', '2', '2', '8', '6', '0', '3', '1', '3', '3', '9', '/', '2', '7', '4', '3', '1', '5', '0', '4', '2', '2', '6', '3', '9', '7', '7', '1', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0315463_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0315463Field002Chars00 ++ tail)) fragment0315463Acc00200 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0315463Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315463_object_field_002"
  err.flush

noncomputable def fragment0315463Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0315463Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0315463Acc00400 : List (String × SourceJson) := (fragment0315463Field003Key00, fragment0315463Field003Value00) :: fragment0315463Acc00300
noncomputable def fragment0315463Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0315463_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0315463Field003Chars00 ++ tail)) fragment0315463Acc00300 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0315463Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315463_object_field_003"
  err.flush

noncomputable def fragment0315463Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0315463Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['8', '0', '7', '/', '1', '7', '7', '9', '2'])]
noncomputable def fragment0315463Acc00500 : List (String × SourceJson) := (fragment0315463Field004Key00, fragment0315463Field004Value00) :: fragment0315463Acc00400
noncomputable def fragment0315463Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '7', '/', '1', '7', '7', '9', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0315463_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0315463Field004Chars00 ++ tail)) fragment0315463Acc00400 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0315463Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315463_object_field_004"
  err.flush

noncomputable def fragment0315463Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0315463Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '5', '6', '0', '3', '5', '9', '6', '4', '7', '7', '9', '/', '7', '3', '9', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '7', '6', '5', '5', '4', '2', '3', '3', '1', '9', '/', '7', '3', '9', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '5', '3', '8', '3', '5', '5', '5', '4', '2', '3', '/', '4', '4', '3', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '7', '7', '8', '3', '5', '5', '3', '5', '2', '3', '3', '/', '3', '3', '2', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '8', '5', '3', '8', '3', '2', '1', '9', '4', '3', '/', '2', '2', '1', '8', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '5', '0', '1', '5', '0', '8', '0', '3', '8', '9', '/', '2', '2', '1', '8', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '0', '7', '9', '3', '9', '9', '8', '1', '9', '/', '1', '1', '6', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '0', '6', '6', '2', '8', '4', '6', '9', '8', '1', '/', '2', '2', '1', '8', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '4', '7', '3', '7', '0', '1', '4', '2', '7', '1', '/', '2', '2', '1', '8', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '5', '4', '3', '6', '5', '6', '2', '0', '9', '9', '9', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0315463Acc00600 : List (String × SourceJson) := (fragment0315463Field005Key00, fragment0315463Field005Value00) :: fragment0315463Acc00500
noncomputable def fragment0315463Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '6', '0', '3', '5', '9', '6', '4', '7', '7', '9', '/', '7', '3', '9', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '7', '6', '5', '5', '4', '2', '3', '3', '1', '9', '/', '7', '3', '9', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '5', '3', '8', '3', '5', '5', '5', '4', '2', '3', '/', '4', '4', '3', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '7', '7', '8', '3', '5', '5', '3', '5', '2', '3', '3', '/', '3', '3', '2', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '8', '5', '3', '8', '3', '2', '1', '9', '4', '3', '/', '2', '2', '1', '8', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '5', '0', '1', '5', '0', '8', '0', '3', '8', '9', '/', '2', '2', '1', '8', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '0', '7', '9', '3', '9', '9', '8', '1', '9', '/', '1', '1', '6', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '0', '6', '6', '2', '8', '4', '6', '9', '8', '1', '/', '2', '2', '1', '8', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '4', '7', '3', '7', '0', '1', '4', '2', '7', '1', '/', '2', '2', '1', '8', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '5', '4', '3', '6', '5', '6', '2', '0', '9', '9', '9', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0315463_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0315463Field005Chars00 ++ tail)) fragment0315463Acc00500 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0315463Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315463_object_field_005"
  err.flush

noncomputable def fragment0315463Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0315463Field006Value00 : SourceJson := .str (String.ofList ['1', '2', '7', '1', '2', '4', '2', '9', '4', '1', '3', '0', '1', '4', '8', '8', '7', '9', '0', '6', '6', '0', '6', '7', '6', '8', '1', '5', '1', '3', '2', '7', '5', '8', '7', '4', '6', '0', '1', '9', '3', '4', '9', '3', '1', '3', '7', '7', '8', '6', '4', '1', '/', '2', '0', '3', '8', '4', '5', '0', '6', '0', '6', '3', '0', '7', '8', '2', '4', '5', '6', '8', '6', '7', '6', '2', '8', '2', '0', '2', '4', '7', '5', '5', '7', '2', '7', '1', '0', '3', '3', '1', '6', '0', '6', '3', '4', '3', '5', '6', '3', '0', '6', '4', '1', '0', '2', '1', '3', '3', '9', '6', '6', '4', '0', '6', '2', '5'])
noncomputable def fragment0315463Acc00700 : List (String × SourceJson) := (fragment0315463Field006Key00, fragment0315463Field006Value00) :: fragment0315463Acc00600
noncomputable def fragment0315463Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '7', '1', '2', '4', '2', '9', '4', '1', '3', '0', '1', '4', '8', '8', '7', '9', '0', '6', '6', '0', '6', '7', '6', '8', '1', '5', '1', '3', '2', '7', '5', '8', '7', '4', '6', '0', '1', '9', '3', '4', '9', '3', '1', '3', '7', '7', '8', '6', '4', '1', '/', '2', '0', '3', '8', '4', '5', '0', '6', '0', '6', '3', '0', '7', '8', '2', '4', '5', '6', '8', '6', '7', '6', '2', '8', '2', '0', '2', '4', '7', '5', '5', '7', '2', '7', '1', '0', '3', '3', '1', '6', '0', '6', '3', '4', '3', '5', '6', '3', '0', '6', '4', '1', '0', '2', '1', '3', '3', '9', '6', '6', '4', '0', '6', '2', '5', '"', ',']

theorem object_fragment0315463_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0315463Field006Chars00 ++ tail)) fragment0315463Acc00600 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0315463Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315463_object_field_006"
  err.flush

noncomputable def fragment0315463Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0315463Field007Value00 : SourceJson := .str (String.ofList ['1', '8', '7', '6', '3', '9', '2', '2', '8', '5', '2', '6', '0', '2', '0', '1', '5', '7', '5', '7', '4', '2', '3', '5', '5', '9', '8', '4', '9', '5', '9', '7', '1', '6', '0', '9', '4', '6', '9', '1', '0', '7', '9', '6', '7', '5', '1', '9', '9', '5', '0', '8', '0', '1', '6', '8', '6', '2', '4', '5', '0', '8', '8', '8', '6', '6', '5', '2', '1', '8', '6', '8', '5', '6', '2', '4', '8', '2', '0', '2', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '4', '3', '6', '2', '3', '7', '3', '1', '2', '0', '0', '9', '7', '1', '6', '4', '0', '0', '5', '6', '6', '7', '7', '4', '3', '9', '2', '3', '3', '1', '5', '9', '5', '8', '6', '7', '5', '6', '0', '8', '6', '7', '5', '9', '4', '3', '9', '6', '5', '7', '2', '0', '9', '9', '0', '4', '7', '6', '7', '8', '5', '0', '2', '7', '2', '7', '7', '9', '0', '2', '0', '7', '3', '6', '3', '0', '6', '7', '1', '2', '9', '8', '4', '1', '8', '0', '6', '0', '5', '6', '4', '7', '7', '3', '0', '5', '4', '2', '8', '1', '8', '6', '7', '3', '4', '3', '3', '2', '4', '8', '3', '6', '0', '8', '6', '8', '6', '1'])
noncomputable def fragment0315463Acc00800 : List (String × SourceJson) := (fragment0315463Field007Key00, fragment0315463Field007Value00) :: fragment0315463Acc00700
noncomputable def fragment0315463Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '7', '6', '3', '9', '2', '2', '8', '5', '2', '6', '0', '2', '0', '1', '5', '7', '5', '7', '4', '2', '3', '5', '5', '9', '8', '4', '9', '5', '9', '7', '1', '6', '0', '9', '4', '6', '9', '1', '0', '7', '9', '6', '7', '5', '1', '9', '9', '5', '0', '8', '0', '1', '6', '8', '6', '2', '4', '5', '0', '8', '8', '8', '6', '6', '5', '2', '1', '8', '6', '8', '5', '6', '2', '4', '8', '2', '0', '2', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '4', '3', '6', '2', '3', '7', '3', '1', '2', '0', '0', '9', '7', '1', '6', '4', '0', '0', '5', '6', '6', '7', '7', '4', '3', '9', '2', '3', '3', '1', '5', '9', '5', '8', '6', '7', '5', '6', '0', '8', '6', '7', '5', '9', '4', '3', '9', '6', '5', '7', '2', '0', '9', '9', '0', '4', '7', '6', '7', '8', '5', '0', '2', '7', '2', '7', '7', '9', '0', '2', '0', '7', '3', '6', '3', '0', '6', '7', '1', '2', '9', '8', '4', '1', '8', '0', '6', '0', '5', '6', '4', '7', '7', '3', '0', '5', '4', '2', '8', '1', '8', '6', '7', '3', '4', '3', '3', '2', '4', '8', '3', '6', '0', '8', '6', '8', '6', '1', '"', ',']

theorem object_fragment0315463_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0315463Field007Chars00 ++ tail)) fragment0315463Acc00700 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0315463Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315463_object_field_007"
  err.flush

noncomputable def fragment0315463Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0315463Field008Value00 : SourceJson := .str (String.ofList ['4', '9', '4', '0', '9', '2', '1', '4', '0', '5', '5', '4', '6', '0', '1', '1'])
noncomputable def fragment0315463Acc00900 : List (String × SourceJson) := (fragment0315463Field008Key00, fragment0315463Field008Value00) :: fragment0315463Acc00800
noncomputable def fragment0315463Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '9', '4', '0', '9', '2', '1', '4', '0', '5', '5', '4', '6', '0', '1', '1', '"', ',']

theorem object_fragment0315463_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0315463Field008Chars00 ++ tail)) fragment0315463Acc00800 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0315463Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315463_object_field_008"
  err.flush

noncomputable def fragment0315463Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0315463Field009Value00 : SourceJson := .str (String.ofList ['4', '3', '2', '6', '3', '3', '4', '2', '8', '4', '2', '3', '3', '7', '0', '5', '8'])
noncomputable def fragment0315463Acc01000 : List (String × SourceJson) := (fragment0315463Field009Key00, fragment0315463Field009Value00) :: fragment0315463Acc00900
noncomputable def fragment0315463Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '3', '2', '6', '3', '3', '4', '2', '8', '4', '2', '3', '3', '7', '0', '5', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0315463_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0315463Field009Chars00 ++ tail)) fragment0315463Acc00900 =
      .ok (.obj (fragment0315463Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315463_object_field_009"
  err.flush

noncomputable def fragment0315463Chars : List Char := '{' :: (fragment0315463Field000Chars00 ++ fragment0315463Field001Chars00 ++ fragment0315463Field002Chars00 ++ fragment0315463Field003Chars00 ++ fragment0315463Field004Chars00 ++ fragment0315463Field005Chars00 ++ fragment0315463Field006Chars00 ++ fragment0315463Field007Chars00 ++ fragment0315463Field008Chars00 ++ fragment0315463Field009Chars00)
noncomputable def fragment0315463Value : SourceJson := .obj (fragment0315463Acc01000.reverse)

theorem value_fragment0315463 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 238) (fragment0315463Chars ++ tail) =
      .ok (fragment0315463Value, tail) := by
  have hinput : fragment0315463Chars ++ tail = '{' :: (fragment0315463Field000Chars00 ++ (fragment0315463Field001Chars00 ++ (fragment0315463Field002Chars00 ++ (fragment0315463Field003Chars00 ++ (fragment0315463Field004Chars00 ++ (fragment0315463Field005Chars00 ++ (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0315463Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 238) (fragment0315463Chars ++ tail) =
        SourceJson.value (fuel + 238) ('{' :: (fragment0315463Field000Chars00 ++ (fragment0315463Field001Chars00 ++ (fragment0315463Field002Chars00 ++ (fragment0315463Field003Chars00 ++ (fragment0315463Field004Chars00 ++ (fragment0315463Field005Chars00 ++ (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 238)) hinput
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0315463Field000Chars00 ++ (fragment0315463Field001Chars00 ++ (fragment0315463Field002Chars00 ++ (fragment0315463Field003Chars00 ++ (fragment0315463Field004Chars00 ++ (fragment0315463Field005Chars00 ++ (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail)))))))))))) fragment0315463Acc00000 := by rfl
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0315463Field001Chars00 ++ (fragment0315463Field002Chars00 ++ (fragment0315463Field003Chars00 ++ (fragment0315463Field004Chars00 ++ (fragment0315463Field005Chars00 ++ (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail))))))))))) fragment0315463Acc00100 := object_fragment0315463_field_000 fuel (fragment0315463Field001Chars00 ++ (fragment0315463Field002Chars00 ++ (fragment0315463Field003Chars00 ++ (fragment0315463Field004Chars00 ++ (fragment0315463Field005Chars00 ++ (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0315463Field002Chars00 ++ (fragment0315463Field003Chars00 ++ (fragment0315463Field004Chars00 ++ (fragment0315463Field005Chars00 ++ (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail)))))))))) fragment0315463Acc00200 := object_fragment0315463_field_001 fuel (fragment0315463Field002Chars00 ++ (fragment0315463Field003Chars00 ++ (fragment0315463Field004Chars00 ++ (fragment0315463Field005Chars00 ++ (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0315463Field003Chars00 ++ (fragment0315463Field004Chars00 ++ (fragment0315463Field005Chars00 ++ (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail))))))))) fragment0315463Acc00300 := object_fragment0315463_field_002 fuel (fragment0315463Field003Chars00 ++ (fragment0315463Field004Chars00 ++ (fragment0315463Field005Chars00 ++ (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0315463Field004Chars00 ++ (fragment0315463Field005Chars00 ++ (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail)))))))) fragment0315463Acc00400 := object_fragment0315463_field_003 fuel (fragment0315463Field004Chars00 ++ (fragment0315463Field005Chars00 ++ (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0315463Field005Chars00 ++ (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail))))))) fragment0315463Acc00500 := object_fragment0315463_field_004 fuel (fragment0315463Field005Chars00 ++ (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail)))))) fragment0315463Acc00600 := object_fragment0315463_field_005 fuel (fragment0315463Field006Chars00 ++ (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail))))) fragment0315463Acc00700 := object_fragment0315463_field_006 fuel (fragment0315463Field007Chars00 ++ (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail)))) fragment0315463Acc00800 := object_fragment0315463_field_007 fuel (fragment0315463Field008Chars00 ++ (fragment0315463Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0315463Field009Chars00 ++ (tail))) fragment0315463Acc00900 := object_fragment0315463_field_008 fuel (fragment0315463Field009Chars00 ++ (tail))
    _ = .ok (fragment0315463Value, tail) := object_fragment0315463_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0051_before_reader"
  err.flush

noncomputable def chunk0051LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0051SuffixChars00 : List Char := [',']
noncomputable def chunk0051Chars00 : List Char := chunk0051LeadChars00 ++ fragment0313535Chars ++ chunk0051SuffixChars00
noncomputable def chunk0051Push00 (acc : List SourceJson) : List SourceJson := fragment0313535Value :: acc

noncomputable def chunk0051AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0051_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 553)
      (SourceJson.white (chunk0051LeadChars00 ++ (fragment0313535Chars ++ rest))) acc =
      (SourceJson.value (fuel + 552) (fragment0313535Chars ++ rest)).bind
        (chunk0051AfterValue00 (fuel + 552) acc) := by rfl

theorem array_chunk0051 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 553) (SourceJson.white (chunk0051Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 552) (SourceJson.white tail) (chunk0051Push00 acc) := by
  have hinput : chunk0051Chars00 ++ tail = chunk0051LeadChars00 ++ (fragment0313535Chars ++ (chunk0051SuffixChars00 ++ tail)) := by
    simp only [chunk0051Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 553) (SourceJson.white (chunk0051Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 553)
          (SourceJson.white (chunk0051LeadChars00 ++ (fragment0313535Chars ++ (chunk0051SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 553) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 552) (fragment0313535Chars ++ (chunk0051SuffixChars00 ++ tail))).bind
        (chunk0051AfterValue00 (fuel + 552) acc) := array_chunk0051_head fuel (chunk0051SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0313535Value, chunk0051SuffixChars00 ++ tail)).bind
        (chunk0051AfterValue00 (fuel + 552) acc) :=
      congrArg (fun result => result.bind (chunk0051AfterValue00 (fuel + 552) acc))
        (value_fragment0313535 (fuel + 161) (chunk0051SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 552) (SourceJson.white tail) (chunk0051Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0051_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0052_before_reader"
  err.flush

noncomputable def chunk0052LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0052SuffixChars00 : List Char := [',']
noncomputable def chunk0052Chars00 : List Char := chunk0052LeadChars00 ++ fragment0315463Chars ++ chunk0052SuffixChars00
noncomputable def chunk0052Push00 (acc : List SourceJson) : List SourceJson := fragment0315463Value :: acc

noncomputable def chunk0052AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0052_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 552)
      (SourceJson.white (chunk0052LeadChars00 ++ (fragment0315463Chars ++ rest))) acc =
      (SourceJson.value (fuel + 551) (fragment0315463Chars ++ rest)).bind
        (chunk0052AfterValue00 (fuel + 551) acc) := by rfl

theorem array_chunk0052 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 552) (SourceJson.white (chunk0052Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 551) (SourceJson.white tail) (chunk0052Push00 acc) := by
  have hinput : chunk0052Chars00 ++ tail = chunk0052LeadChars00 ++ (fragment0315463Chars ++ (chunk0052SuffixChars00 ++ tail)) := by
    simp only [chunk0052Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 552) (SourceJson.white (chunk0052Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 552)
          (SourceJson.white (chunk0052LeadChars00 ++ (fragment0315463Chars ++ (chunk0052SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 552) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 551) (fragment0315463Chars ++ (chunk0052SuffixChars00 ++ tail))).bind
        (chunk0052AfterValue00 (fuel + 551) acc) := array_chunk0052_head fuel (chunk0052SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0315463Value, chunk0052SuffixChars00 ++ tail)).bind
        (chunk0052AfterValue00 (fuel + 551) acc) :=
      congrArg (fun result => result.bind (chunk0052AfterValue00 (fuel + 551) acc))
        (value_fragment0315463 (fuel + 313) (chunk0052SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 551) (SourceJson.white tail) (chunk0052Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0052_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0051Chars00 ++ chunk0052Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0052Push00 (chunk0051Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 553) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 551) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0051Chars00 ++ (chunk0052Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 553) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 553) (SourceJson.white (chunk0051Chars00 ++ (chunk0052Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 553) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 552) (SourceJson.white (chunk0052Chars00 ++ (tail))) (chunk0051Push00 (acc)) := array_chunk0051 fuel (chunk0052Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 551) (SourceJson.white tail) (blockPush acc) := array_chunk0052 fuel (tail) (chunk0051Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 313529).take 3536 = blockChars := by rfl

theorem block_original_split : sourceRest 313529 = blockChars ++ sourceRest 317065 := by
  calc
    sourceRest 313529 = (sourceRest 313529).take 3536 ++ (sourceRest 313529).drop 3536 :=
      (List.take_append_drop 3536 (sourceRest 313529)).symm
    _ = blockChars ++ (sourceRest 313529).drop 3536 :=
      congrArg (fun part => part ++ (sourceRest 313529).drop 3536) block_original_prefix
    _ = blockChars ++ sourceRest 317065 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 313529 3536)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 553) (SourceJson.white (sourceRest 313529)) acc =
      SourceJson.array (fuel + 551) (SourceJson.white (sourceRest 317065)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 553) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 317065) acc)

#print axioms object_fragment0313535_field_000
#print axioms object_fragment0313535_field_001
#print axioms object_fragment0313535_field_002
#print axioms object_fragment0313535_field_003
#print axioms object_fragment0313535_field_004
#print axioms object_fragment0313535_field_005
#print axioms object_fragment0313535_field_006
#print axioms object_fragment0313535_field_007
#print axioms object_fragment0313535_field_008
#print axioms object_fragment0313535_field_009
#print axioms value_fragment0313535
#print axioms object_fragment0315463_field_000
#print axioms object_fragment0315463_field_001
#print axioms object_fragment0315463_field_002
#print axioms object_fragment0315463_field_003
#print axioms object_fragment0315463_field_004
#print axioms object_fragment0315463_field_005
#print axioms object_fragment0315463_field_006
#print axioms object_fragment0315463_field_007
#print axioms object_fragment0315463_field_008
#print axioms object_fragment0315463_field_009
#print axioms value_fragment0315463
#print axioms array_chunk0051_head
#print axioms array_chunk0051
#print axioms array_chunk0052_head
#print axioms array_chunk0052
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock026

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
