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

namespace SimplicesBlock041

noncomputable def fragment0363535Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0363535Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0363535Field000Value00 : SourceJson := .number (String.ofList ['8', '1'])
noncomputable def fragment0363535Acc00100 : List (String × SourceJson) := (fragment0363535Field000Key00, fragment0363535Field000Value00) :: fragment0363535Acc00000
noncomputable def fragment0363535Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '1', ',']

theorem object_fragment0363535_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 191) (SourceJson.white (fragment0363535Field000Chars00 ++ tail)) fragment0363535Acc00000 =
      SourceJson.object (fuel + 190) (SourceJson.white tail) fragment0363535Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0363535_object_field_000"
  err.flush

noncomputable def fragment0363535Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0363535Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '1']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0363535Acc00200 : List (String × SourceJson) := (fragment0363535Field001Key00, fragment0363535Field001Value00) :: fragment0363535Acc00100
noncomputable def fragment0363535Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0363535_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 190) (SourceJson.white (fragment0363535Field001Chars00 ++ tail)) fragment0363535Acc00100 =
      SourceJson.object (fuel + 189) (SourceJson.white tail) fragment0363535Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0363535_object_field_001"
  err.flush

noncomputable def fragment0363535Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0363535Field002Value00 : SourceJson := .str (String.ofList ['3', '9', '6', '1', '6', '8', '5', '6', '3', '1', '6', '6', '6', '5', '2', '9', '3', '7', '5', '6', '5', '7', '0', '3', '7', '0', '5', '6', '3', '2', '0', '1', '3', '9', '4', '8', '8', '7', '5', '4', '1', '/', '9', '2', '6', '8', '2', '4', '5', '7', '8', '2', '6', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0363535Acc00300 : List (String × SourceJson) := (fragment0363535Field002Key00, fragment0363535Field002Value00) :: fragment0363535Acc00200
noncomputable def fragment0363535Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '9', '6', '1', '6', '8', '5', '6', '3', '1', '6', '6', '6', '5', '2', '9', '3', '7', '5', '6', '5', '7', '0', '3', '7', '0', '5', '6', '3', '2', '0', '1', '3', '9', '4', '8', '8', '7', '5', '4', '1', '/', '9', '2', '6', '8', '2', '4', '5', '7', '8', '2', '6', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0363535_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 189) (SourceJson.white (fragment0363535Field002Chars00 ++ tail)) fragment0363535Acc00200 =
      SourceJson.object (fuel + 188) (SourceJson.white tail) fragment0363535Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0363535_object_field_002"
  err.flush

noncomputable def fragment0363535Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0363535Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0363535Acc00400 : List (String × SourceJson) := (fragment0363535Field003Key00, fragment0363535Field003Value00) :: fragment0363535Acc00300
noncomputable def fragment0363535Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0363535_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 188) (SourceJson.white (fragment0363535Field003Chars00 ++ tail)) fragment0363535Acc00300 =
      SourceJson.object (fuel + 187) (SourceJson.white tail) fragment0363535Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0363535_object_field_003"
  err.flush

noncomputable def fragment0363535Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0363535Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '3', '7', '7', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0363535Acc00500 : List (String × SourceJson) := (fragment0363535Field004Key00, fragment0363535Field004Value00) :: fragment0363535Acc00400
noncomputable def fragment0363535Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '3', '3', '7', '7', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0363535_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 187) (SourceJson.white (fragment0363535Field004Chars00 ++ tail)) fragment0363535Acc00400 =
      SourceJson.object (fuel + 186) (SourceJson.white tail) fragment0363535Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0363535_object_field_004"
  err.flush

noncomputable def fragment0363535Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0363535Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '3', '9', '2', '3', '2', '9', '8', '6', '9', '/', '2', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '4', '2', '2', '1', '1', '6', '2', '3', '/', '1', '8', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '0', '3', '1', '4', '5', '3', '6', '8', '1', '/', '8', '3', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '3', '7', '7', '1', '3', '6', '4', '1', '/', '3', '4', '9', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '7', '8', '5', '2', '7', '7', '9', '3', '7', '/', '1', '6', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '4', '8', '7', '4', '8', '0', '1', '/', '1', '0', '4', '7', '3', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '1', '4', '1', '4', '9', '3', '9', '/', '1', '3', '4', '0', '6', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '9', '6', '0', '8', '3', '3', '9', '6', '1', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '9', '6', '0', '7', '8', '9', '2', '7', '3', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '2', '9', '1', '1', '2', '4', '9', '5', '7', '/', '8', '3', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0363535Acc00600 : List (String × SourceJson) := (fragment0363535Field005Key00, fragment0363535Field005Value00) :: fragment0363535Acc00500
noncomputable def fragment0363535Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '2', '3', '2', '9', '8', '6', '9', '/', '2', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '4', '2', '2', '1', '1', '6', '2', '3', '/', '1', '8', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '0', '3', '1', '4', '5', '3', '6', '8', '1', '/', '8', '3', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '3', '7', '7', '1', '3', '6', '4', '1', '/', '3', '4', '9', '1', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '7', '8', '5', '2', '7', '7', '9', '3', '7', '/', '1', '6', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '4', '8', '7', '4', '8', '0', '1', '/', '1', '0', '4', '7', '3', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '1', '4', '1', '4', '9', '3', '9', '/', '1', '3', '4', '0', '6', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '6', '0', '8', '3', '3', '9', '6', '1', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '6', '0', '7', '8', '9', '2', '7', '3', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '9', '1', '1', '2', '4', '9', '5', '7', '/', '8', '3', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0363535_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 186) (SourceJson.white (fragment0363535Field005Chars00 ++ tail)) fragment0363535Acc00500 =
      SourceJson.object (fuel + 185) (SourceJson.white tail) fragment0363535Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0363535_object_field_005"
  err.flush

noncomputable def fragment0363535Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0363535Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '8', '7', '4', '8', '5', '6', '0', '3', '9', '1', '3', '5', '4', '5', '3', '7', '1', '6', '2', '7', '6', '1', '3', '0', '3', '5', '0', '0', '0', '0', '0', '3', '7', '3', '7', '7', '3', '0', '9', '9', '0', '4', '4', '9', '0', '0', '6', '8', '4', '8', '0', '0', '0', '0', '/', '9', '0', '9', '5', '7', '7', '0', '6', '7', '6', '5', '8', '2', '4', '1', '5', '8', '8', '7', '4', '0', '3', '0', '8', '7', '9', '3', '8', '3', '7', '3', '8', '8', '3', '7', '0', '3', '7', '8', '8', '8', '2', '5', '1', '9', '2', '0', '7', '8', '6', '0', '3', '4', '9', '4', '7', '8', '4', '5', '3', '4', '4', '2', '7', '7', '9', '9', '3', '9', '9'])
noncomputable def fragment0363535Acc00700 : List (String × SourceJson) := (fragment0363535Field006Key00, fragment0363535Field006Value00) :: fragment0363535Acc00600
noncomputable def fragment0363535Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '8', '7', '4', '8', '5', '6', '0', '3', '9', '1', '3', '5', '4', '5', '3', '7', '1', '6', '2', '7', '6', '1', '3', '0', '3', '5', '0', '0', '0', '0', '0', '3', '7', '3', '7', '7', '3', '0', '9', '9', '0', '4', '4', '9', '0', '0', '6', '8', '4', '8', '0', '0', '0', '0', '/', '9', '0', '9', '5', '7', '7', '0', '6', '7', '6', '5', '8', '2', '4', '1', '5', '8', '8', '7', '4', '0', '3', '0', '8', '7', '9', '3', '8', '3', '7', '3', '8', '8', '3', '7', '0', '3', '7', '8', '8', '8', '2', '5', '1', '9', '2', '0', '7', '8', '6', '0', '3', '4', '9', '4', '7', '8', '4', '5', '3', '4', '4', '2', '7', '7', '9', '9', '3', '9', '9', '"', ',']

theorem object_fragment0363535_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 185) (SourceJson.white (fragment0363535Field006Chars00 ++ tail)) fragment0363535Acc00600 =
      SourceJson.object (fuel + 184) (SourceJson.white tail) fragment0363535Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0363535_object_field_006"
  err.flush

noncomputable def fragment0363535Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0363535Field007Value00 : SourceJson := .str (String.ofList ['2', '2', '9', '9', '0', '8', '4', '0', '0', '1', '1', '1', '9', '3', '5', '1', '9', '3', '4', '1', '4', '6', '2', '1', '4', '7', '0', '2', '8', '2', '4', '2', '2', '5', '0', '4', '1', '7', '4', '5', '4', '4', '1', '0', '1', '6', '7', '6', '2', '2', '4', '4', '1', '3', '8', '3', '8', '3', '6', '4', '7', '4', '2', '8', '3', '9', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '2', '9', '4', '2', '4', '9', '0', '4', '4', '9', '8', '1', '3', '6', '1', '7', '8', '9', '9', '4', '6', '2', '8', '9', '2', '0', '8', '2', '6', '3', '0', '2', '7', '6', '5', '7', '3', '4', '5', '6', '3', '2', '5', '1', '1', '5', '9', '3', '4', '5', '1', '3', '3', '5', '3', '3', '4', '2', '8', '2', '2', '4', '3', '8', '4', '4', '4', '9', '8', '3', '0', '3', '6', '2', '6', '0', '0', '9', '0', '8', '4', '6', '9', '0', '4', '6', '1', '8', '2', '5', '4', '5', '1', '6', '9'])
noncomputable def fragment0363535Acc00800 : List (String × SourceJson) := (fragment0363535Field007Key00, fragment0363535Field007Value00) :: fragment0363535Acc00700
noncomputable def fragment0363535Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '2', '9', '9', '0', '8', '4', '0', '0', '1', '1', '1', '9', '3', '5', '1', '9', '3', '4', '1', '4', '6', '2', '1', '4', '7', '0', '2', '8', '2', '4', '2', '2', '5', '0', '4', '1', '7', '4', '5', '4', '4', '1', '0', '1', '6', '7', '6', '2', '2', '4', '4', '1', '3', '8', '3', '8', '3', '6', '4', '7', '4', '2', '8', '3', '9', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '2', '9', '4', '2', '4', '9', '0', '4', '4', '9', '8', '1', '3', '6', '1', '7', '8', '9', '9', '4', '6', '2', '8', '9', '2', '0', '8', '2', '6', '3', '0', '2', '7', '6', '5', '7', '3', '4', '5', '6', '3', '2', '5', '1', '1', '5', '9', '3', '4', '5', '1', '3', '3', '5', '3', '3', '4', '2', '8', '2', '2', '4', '3', '8', '4', '4', '4', '9', '8', '3', '0', '3', '6', '2', '6', '0', '0', '9', '0', '8', '4', '6', '9', '0', '4', '6', '1', '8', '2', '5', '4', '5', '1', '6', '9', '"', ',']

theorem object_fragment0363535_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 184) (SourceJson.white (fragment0363535Field007Chars00 ++ tail)) fragment0363535Acc00700 =
      SourceJson.object (fuel + 183) (SourceJson.white tail) fragment0363535Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0363535_object_field_007"
  err.flush

noncomputable def fragment0363535Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0363535Field008Value00 : SourceJson := .str (String.ofList ['1', '6', '4', '4', '0', '8', '2', '9', '6', '4', '3', '5', '1', '7', '8'])
noncomputable def fragment0363535Acc00900 : List (String × SourceJson) := (fragment0363535Field008Key00, fragment0363535Field008Value00) :: fragment0363535Acc00800
noncomputable def fragment0363535Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '4', '4', '0', '8', '2', '9', '6', '4', '3', '5', '1', '7', '8', '"', ',']

theorem object_fragment0363535_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 183) (SourceJson.white (fragment0363535Field008Chars00 ++ tail)) fragment0363535Acc00800 =
      SourceJson.object (fuel + 182) (SourceJson.white tail) fragment0363535Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0363535_object_field_008"
  err.flush

noncomputable def fragment0363535Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0363535Field009Value00 : SourceJson := .str (String.ofList ['1', '2', '7', '4', '3', '0', '4', '0', '9', '4', '6', '1', '4', '7', '6', '2'])
noncomputable def fragment0363535Acc01000 : List (String × SourceJson) := (fragment0363535Field009Key00, fragment0363535Field009Value00) :: fragment0363535Acc00900
noncomputable def fragment0363535Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '7', '4', '3', '0', '4', '0', '9', '4', '6', '1', '4', '7', '6', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0363535_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 182) (SourceJson.white (fragment0363535Field009Chars00 ++ tail)) fragment0363535Acc00900 =
      .ok (.obj (fragment0363535Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0363535_object_field_009"
  err.flush

noncomputable def fragment0363535Chars : List Char := '{' :: (fragment0363535Field000Chars00 ++ fragment0363535Field001Chars00 ++ fragment0363535Field002Chars00 ++ fragment0363535Field003Chars00 ++ fragment0363535Field004Chars00 ++ fragment0363535Field005Chars00 ++ fragment0363535Field006Chars00 ++ fragment0363535Field007Chars00 ++ fragment0363535Field008Chars00 ++ fragment0363535Field009Chars00)
noncomputable def fragment0363535Value : SourceJson := .obj (fragment0363535Acc01000.reverse)

theorem value_fragment0363535 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 192) (fragment0363535Chars ++ tail) =
      .ok (fragment0363535Value, tail) := by
  have hinput : fragment0363535Chars ++ tail = '{' :: (fragment0363535Field000Chars00 ++ (fragment0363535Field001Chars00 ++ (fragment0363535Field002Chars00 ++ (fragment0363535Field003Chars00 ++ (fragment0363535Field004Chars00 ++ (fragment0363535Field005Chars00 ++ (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0363535Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 192) (fragment0363535Chars ++ tail) =
        SourceJson.value (fuel + 192) ('{' :: (fragment0363535Field000Chars00 ++ (fragment0363535Field001Chars00 ++ (fragment0363535Field002Chars00 ++ (fragment0363535Field003Chars00 ++ (fragment0363535Field004Chars00 ++ (fragment0363535Field005Chars00 ++ (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 192)) hinput
    _ = SourceJson.object (fuel + 191) (SourceJson.white (fragment0363535Field000Chars00 ++ (fragment0363535Field001Chars00 ++ (fragment0363535Field002Chars00 ++ (fragment0363535Field003Chars00 ++ (fragment0363535Field004Chars00 ++ (fragment0363535Field005Chars00 ++ (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail)))))))))))) fragment0363535Acc00000 := by rfl
    _ = SourceJson.object (fuel + 190) (SourceJson.white (fragment0363535Field001Chars00 ++ (fragment0363535Field002Chars00 ++ (fragment0363535Field003Chars00 ++ (fragment0363535Field004Chars00 ++ (fragment0363535Field005Chars00 ++ (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail))))))))))) fragment0363535Acc00100 := object_fragment0363535_field_000 fuel (fragment0363535Field001Chars00 ++ (fragment0363535Field002Chars00 ++ (fragment0363535Field003Chars00 ++ (fragment0363535Field004Chars00 ++ (fragment0363535Field005Chars00 ++ (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 189) (SourceJson.white (fragment0363535Field002Chars00 ++ (fragment0363535Field003Chars00 ++ (fragment0363535Field004Chars00 ++ (fragment0363535Field005Chars00 ++ (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail)))))))))) fragment0363535Acc00200 := object_fragment0363535_field_001 fuel (fragment0363535Field002Chars00 ++ (fragment0363535Field003Chars00 ++ (fragment0363535Field004Chars00 ++ (fragment0363535Field005Chars00 ++ (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 188) (SourceJson.white (fragment0363535Field003Chars00 ++ (fragment0363535Field004Chars00 ++ (fragment0363535Field005Chars00 ++ (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail))))))))) fragment0363535Acc00300 := object_fragment0363535_field_002 fuel (fragment0363535Field003Chars00 ++ (fragment0363535Field004Chars00 ++ (fragment0363535Field005Chars00 ++ (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 187) (SourceJson.white (fragment0363535Field004Chars00 ++ (fragment0363535Field005Chars00 ++ (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail)))))))) fragment0363535Acc00400 := object_fragment0363535_field_003 fuel (fragment0363535Field004Chars00 ++ (fragment0363535Field005Chars00 ++ (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 186) (SourceJson.white (fragment0363535Field005Chars00 ++ (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail))))))) fragment0363535Acc00500 := object_fragment0363535_field_004 fuel (fragment0363535Field005Chars00 ++ (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 185) (SourceJson.white (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail)))))) fragment0363535Acc00600 := object_fragment0363535_field_005 fuel (fragment0363535Field006Chars00 ++ (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 184) (SourceJson.white (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail))))) fragment0363535Acc00700 := object_fragment0363535_field_006 fuel (fragment0363535Field007Chars00 ++ (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 183) (SourceJson.white (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail)))) fragment0363535Acc00800 := object_fragment0363535_field_007 fuel (fragment0363535Field008Chars00 ++ (fragment0363535Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 182) (SourceJson.white (fragment0363535Field009Chars00 ++ (tail))) fragment0363535Acc00900 := object_fragment0363535_field_008 fuel (fragment0363535Field009Chars00 ++ (tail))
    _ = .ok (fragment0363535Value, tail) := object_fragment0363535_field_009 fuel (tail)

noncomputable def fragment0365076Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0365076Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0365076Field000Value00 : SourceJson := .number (String.ofList ['8', '2'])
noncomputable def fragment0365076Acc00100 : List (String × SourceJson) := (fragment0365076Field000Key00, fragment0365076Field000Value00) :: fragment0365076Acc00000
noncomputable def fragment0365076Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '2', ',']

theorem object_fragment0365076_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 206) (SourceJson.white (fragment0365076Field000Chars00 ++ tail)) fragment0365076Acc00000 =
      SourceJson.object (fuel + 205) (SourceJson.white tail) fragment0365076Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0365076_object_field_000"
  err.flush

noncomputable def fragment0365076Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0365076Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0365076Acc00200 : List (String × SourceJson) := (fragment0365076Field001Key00, fragment0365076Field001Value00) :: fragment0365076Acc00100
noncomputable def fragment0365076Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0365076_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 205) (SourceJson.white (fragment0365076Field001Chars00 ++ tail)) fragment0365076Acc00100 =
      SourceJson.object (fuel + 204) (SourceJson.white tail) fragment0365076Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0365076_object_field_001"
  err.flush

noncomputable def fragment0365076Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0365076Field002Value00 : SourceJson := .str (String.ofList ['1', '0', '0', '7', '3', '1', '7', '0', '4', '2', '6', '6', '7', '7', '3', '2', '2', '1', '4', '9', '2', '0', '7', '7', '5', '0', '9', '7', '4', '3', '7', '6', '7', '0', '1', '9', '/', '1', '4', '6', '5', '9', '9', '8', '7', '0', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0365076Acc00300 : List (String × SourceJson) := (fragment0365076Field002Key00, fragment0365076Field002Value00) :: fragment0365076Acc00200
noncomputable def fragment0365076Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '0', '0', '7', '3', '1', '7', '0', '4', '2', '6', '6', '7', '7', '3', '2', '2', '1', '4', '9', '2', '0', '7', '7', '5', '0', '9', '7', '4', '3', '7', '6', '7', '0', '1', '9', '/', '1', '4', '6', '5', '9', '9', '8', '7', '0', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0365076_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0365076Field002Chars00 ++ tail)) fragment0365076Acc00200 =
      SourceJson.object (fuel + 203) (SourceJson.white tail) fragment0365076Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0365076_object_field_002"
  err.flush

noncomputable def fragment0365076Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0365076Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0365076Acc00400 : List (String × SourceJson) := (fragment0365076Field003Key00, fragment0365076Field003Value00) :: fragment0365076Acc00300
noncomputable def fragment0365076Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0365076_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0365076Field003Chars00 ++ tail)) fragment0365076Acc00300 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0365076Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0365076_object_field_003"
  err.flush

noncomputable def fragment0365076Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0365076Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0365076Acc00500 : List (String × SourceJson) := (fragment0365076Field004Key00, fragment0365076Field004Value00) :: fragment0365076Acc00400
noncomputable def fragment0365076Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0365076_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0365076Field004Chars00 ++ tail)) fragment0365076Acc00400 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0365076Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0365076_object_field_004"
  err.flush

noncomputable def fragment0365076Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0365076Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '3', '9', '8', '4', '7', '4', '5', '6', '3', '7', '/', '7', '0', '5', '4', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '3', '4', '8', '9', '1', '2', '6', '7', '4', '9', '/', '3', '5', '2', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '4', '9', '9', '4', '0', '6', '6', '7', '/', '9', '0', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '2', '8', '1', '9', '7', '1', '6', '3', '9', '/', '5', '2', '9', '0', '7', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '3', '5', '6', '6', '0', '8', '2', '7', '/', '3', '4', '5', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '1', '2', '7', '2', '2', '5', '9', '6', '7', '/', '1', '1', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '5', '9', '0', '3', '7', '0', '4', '1', '/', '2', '7', '8', '4', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '9', '9', '7', '8', '8', '7', '7', '1', '/', '3', '3', '0', '6', '7', '1', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '0', '9', '1', '9', '2', '9', '5', '8', '9', '9', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '0', '9', '1', '7', '1', '7', '9', '6', '0', '3', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0365076Acc00600 : List (String × SourceJson) := (fragment0365076Field005Key00, fragment0365076Field005Value00) :: fragment0365076Acc00500
noncomputable def fragment0365076Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '9', '8', '4', '7', '4', '5', '6', '3', '7', '/', '7', '0', '5', '4', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '3', '4', '8', '9', '1', '2', '6', '7', '4', '9', '/', '3', '5', '2', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '4', '9', '9', '4', '0', '6', '6', '7', '/', '9', '0', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '2', '8', '1', '9', '7', '1', '6', '3', '9', '/', '5', '2', '9', '0', '7', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '3', '5', '6', '6', '0', '8', '2', '7', '/', '3', '4', '5', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '1', '2', '7', '2', '2', '5', '9', '6', '7', '/', '1', '1', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '5', '9', '0', '3', '7', '0', '4', '1', '/', '2', '7', '8', '4', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '9', '9', '7', '8', '8', '7', '7', '1', '/', '3', '3', '0', '6', '7', '1', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '0', '9', '1', '9', '2', '9', '5', '8', '9', '9', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '0', '9', '1', '7', '1', '7', '9', '6', '0', '3', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0365076_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0365076Field005Chars00 ++ tail)) fragment0365076Acc00500 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0365076Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0365076_object_field_005"
  err.flush

noncomputable def fragment0365076Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0365076Field006Value00 : SourceJson := .str (String.ofList ['5', '1', '4', '1', '9', '7', '1', '5', '9', '2', '6', '6', '4', '4', '8', '4', '0', '8', '3', '8', '4', '9', '5', '2', '0', '6', '6', '9', '4', '3', '1', '9', '6', '4', '1', '9', '1', '4', '2', '4', '8', '4', '4', '1', '6', '0', '0', '0', '0', '/', '1', '5', '3', '7', '2', '1', '7', '3', '0', '9', '6', '1', '2', '3', '5', '4', '1', '8', '6', '5', '7', '3', '1', '5', '8', '6', '5', '7', '9', '2', '3', '3', '2', '3', '2', '1', '3', '6', '1', '0', '7', '6', '6', '1', '6', '8', '1', '7', '3', '2', '2', '5', '1', '6', '5', '6', '2', '3', '1', '3', '0', '1', '5', '1', '7'])
noncomputable def fragment0365076Acc00700 : List (String × SourceJson) := (fragment0365076Field006Key00, fragment0365076Field006Value00) :: fragment0365076Acc00600
noncomputable def fragment0365076Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '1', '4', '1', '9', '7', '1', '5', '9', '2', '6', '6', '4', '4', '8', '4', '0', '8', '3', '8', '4', '9', '5', '2', '0', '6', '6', '9', '4', '3', '1', '9', '6', '4', '1', '9', '1', '4', '2', '4', '8', '4', '4', '1', '6', '0', '0', '0', '0', '/', '1', '5', '3', '7', '2', '1', '7', '3', '0', '9', '6', '1', '2', '3', '5', '4', '1', '8', '6', '5', '7', '3', '1', '5', '8', '6', '5', '7', '9', '2', '3', '3', '2', '3', '2', '1', '3', '6', '1', '0', '7', '6', '6', '1', '6', '8', '1', '7', '3', '2', '2', '5', '1', '6', '5', '6', '2', '3', '1', '3', '0', '1', '5', '1', '7', '"', ',']

theorem object_fragment0365076_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0365076Field006Chars00 ++ tail)) fragment0365076Acc00600 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0365076Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0365076_object_field_006"
  err.flush

noncomputable def fragment0365076Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0365076Field007Value00 : SourceJson := .str (String.ofList ['9', '5', '0', '9', '4', '6', '8', '8', '3', '0', '1', '5', '6', '8', '3', '2', '0', '3', '5', '5', '1', '7', '0', '9', '1', '3', '7', '8', '0', '8', '3', '3', '1', '2', '9', '1', '0', '4', '2', '0', '1', '5', '5', '1', '2', '2', '8', '8', '3', '0', '4', '1', '9', '1', '8', '3', '6', '4', '3', '6', '8', '5', '6', '3', '3', '5', '8', '2', '2', '4', '3', '4', '3', '7', '1', '1', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '0', '4', '7', '2', '0', '3', '4', '0', '2', '4', '8', '6', '3', '3', '1', '3', '6', '7', '3', '4', '7', '4', '4', '5', '5', '9', '0', '0', '4', '7', '9', '4', '0', '2', '0', '3', '1', '7', '3', '5', '7', '9', '6', '2', '1', '8', '4', '4', '2', '0', '1', '5', '2', '6', '9', '0', '8', '4', '6', '6', '7', '5', '2', '9', '0', '7', '2', '2', '5', '2', '8', '9', '5', '0', '3', '9', '0', '7', '5', '6', '2', '4', '0', '3', '3', '4', '1', '3', '8', '2', '2', '1', '0', '5', '9', '9', '1', '7', '9', '6', '6', '1', '4', '7'])
noncomputable def fragment0365076Acc00800 : List (String × SourceJson) := (fragment0365076Field007Key00, fragment0365076Field007Value00) :: fragment0365076Acc00700
noncomputable def fragment0365076Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '5', '0', '9', '4', '6', '8', '8', '3', '0', '1', '5', '6', '8', '3', '2', '0', '3', '5', '5', '1', '7', '0', '9', '1', '3', '7', '8', '0', '8', '3', '3', '1', '2', '9', '1', '0', '4', '2', '0', '1', '5', '5', '1', '2', '2', '8', '8', '3', '0', '4', '1', '9', '1', '8', '3', '6', '4', '3', '6', '8', '5', '6', '3', '3', '5', '8', '2', '2', '4', '3', '4', '3', '7', '1', '1', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '0', '4', '7', '2', '0', '3', '4', '0', '2', '4', '8', '6', '3', '3', '1', '3', '6', '7', '3', '4', '7', '4', '4', '5', '5', '9', '0', '0', '4', '7', '9', '4', '0', '2', '0', '3', '1', '7', '3', '5', '7', '9', '6', '2', '1', '8', '4', '4', '2', '0', '1', '5', '2', '6', '9', '0', '8', '4', '6', '6', '7', '5', '2', '9', '0', '7', '2', '2', '5', '2', '8', '9', '5', '0', '3', '9', '0', '7', '5', '6', '2', '4', '0', '3', '3', '4', '1', '3', '8', '2', '2', '1', '0', '5', '9', '9', '1', '7', '9', '6', '6', '1', '4', '7', '"', ',']

theorem object_fragment0365076_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0365076Field007Chars00 ++ tail)) fragment0365076Acc00700 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0365076Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0365076_object_field_007"
  err.flush

noncomputable def fragment0365076Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0365076Field008Value00 : SourceJson := .str (String.ofList ['2', '6', '5', '0', '1', '7', '1', '5', '6', '9', '3', '6', '7', '0'])
noncomputable def fragment0365076Acc00900 : List (String × SourceJson) := (fragment0365076Field008Key00, fragment0365076Field008Value00) :: fragment0365076Acc00800
noncomputable def fragment0365076Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '6', '5', '0', '1', '7', '1', '5', '6', '9', '3', '6', '7', '0', '"', ',']

theorem object_fragment0365076_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0365076Field008Chars00 ++ tail)) fragment0365076Acc00800 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0365076Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0365076_object_field_008"
  err.flush

noncomputable def fragment0365076Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0365076Field009Value00 : SourceJson := .str (String.ofList ['1', '8', '6', '1', '5', '7', '6', '1', '7', '2', '4', '1', '8', '5', '8'])
noncomputable def fragment0365076Acc01000 : List (String × SourceJson) := (fragment0365076Field009Key00, fragment0365076Field009Value00) :: fragment0365076Acc00900
noncomputable def fragment0365076Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '6', '1', '5', '7', '6', '1', '7', '2', '4', '1', '8', '5', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0365076_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0365076Field009Chars00 ++ tail)) fragment0365076Acc00900 =
      .ok (.obj (fragment0365076Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0365076_object_field_009"
  err.flush

noncomputable def fragment0365076Chars : List Char := '{' :: (fragment0365076Field000Chars00 ++ fragment0365076Field001Chars00 ++ fragment0365076Field002Chars00 ++ fragment0365076Field003Chars00 ++ fragment0365076Field004Chars00 ++ fragment0365076Field005Chars00 ++ fragment0365076Field006Chars00 ++ fragment0365076Field007Chars00 ++ fragment0365076Field008Chars00 ++ fragment0365076Field009Chars00)
noncomputable def fragment0365076Value : SourceJson := .obj (fragment0365076Acc01000.reverse)

theorem value_fragment0365076 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 207) (fragment0365076Chars ++ tail) =
      .ok (fragment0365076Value, tail) := by
  have hinput : fragment0365076Chars ++ tail = '{' :: (fragment0365076Field000Chars00 ++ (fragment0365076Field001Chars00 ++ (fragment0365076Field002Chars00 ++ (fragment0365076Field003Chars00 ++ (fragment0365076Field004Chars00 ++ (fragment0365076Field005Chars00 ++ (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0365076Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 207) (fragment0365076Chars ++ tail) =
        SourceJson.value (fuel + 207) ('{' :: (fragment0365076Field000Chars00 ++ (fragment0365076Field001Chars00 ++ (fragment0365076Field002Chars00 ++ (fragment0365076Field003Chars00 ++ (fragment0365076Field004Chars00 ++ (fragment0365076Field005Chars00 ++ (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 207)) hinput
    _ = SourceJson.object (fuel + 206) (SourceJson.white (fragment0365076Field000Chars00 ++ (fragment0365076Field001Chars00 ++ (fragment0365076Field002Chars00 ++ (fragment0365076Field003Chars00 ++ (fragment0365076Field004Chars00 ++ (fragment0365076Field005Chars00 ++ (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail)))))))))))) fragment0365076Acc00000 := by rfl
    _ = SourceJson.object (fuel + 205) (SourceJson.white (fragment0365076Field001Chars00 ++ (fragment0365076Field002Chars00 ++ (fragment0365076Field003Chars00 ++ (fragment0365076Field004Chars00 ++ (fragment0365076Field005Chars00 ++ (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail))))))))))) fragment0365076Acc00100 := object_fragment0365076_field_000 fuel (fragment0365076Field001Chars00 ++ (fragment0365076Field002Chars00 ++ (fragment0365076Field003Chars00 ++ (fragment0365076Field004Chars00 ++ (fragment0365076Field005Chars00 ++ (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0365076Field002Chars00 ++ (fragment0365076Field003Chars00 ++ (fragment0365076Field004Chars00 ++ (fragment0365076Field005Chars00 ++ (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail)))))))))) fragment0365076Acc00200 := object_fragment0365076_field_001 fuel (fragment0365076Field002Chars00 ++ (fragment0365076Field003Chars00 ++ (fragment0365076Field004Chars00 ++ (fragment0365076Field005Chars00 ++ (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0365076Field003Chars00 ++ (fragment0365076Field004Chars00 ++ (fragment0365076Field005Chars00 ++ (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail))))))))) fragment0365076Acc00300 := object_fragment0365076_field_002 fuel (fragment0365076Field003Chars00 ++ (fragment0365076Field004Chars00 ++ (fragment0365076Field005Chars00 ++ (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0365076Field004Chars00 ++ (fragment0365076Field005Chars00 ++ (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail)))))))) fragment0365076Acc00400 := object_fragment0365076_field_003 fuel (fragment0365076Field004Chars00 ++ (fragment0365076Field005Chars00 ++ (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0365076Field005Chars00 ++ (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail))))))) fragment0365076Acc00500 := object_fragment0365076_field_004 fuel (fragment0365076Field005Chars00 ++ (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail)))))) fragment0365076Acc00600 := object_fragment0365076_field_005 fuel (fragment0365076Field006Chars00 ++ (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail))))) fragment0365076Acc00700 := object_fragment0365076_field_006 fuel (fragment0365076Field007Chars00 ++ (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail)))) fragment0365076Acc00800 := object_fragment0365076_field_007 fuel (fragment0365076Field008Chars00 ++ (fragment0365076Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0365076Field009Chars00 ++ (tail))) fragment0365076Acc00900 := object_fragment0365076_field_008 fuel (fragment0365076Field009Chars00 ++ (tail))
    _ = .ok (fragment0365076Value, tail) := object_fragment0365076_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0081_before_reader"
  err.flush

noncomputable def chunk0081LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0081SuffixChars00 : List Char := [',']
noncomputable def chunk0081Chars00 : List Char := chunk0081LeadChars00 ++ fragment0363535Chars ++ chunk0081SuffixChars00
noncomputable def chunk0081Push00 (acc : List SourceJson) : List SourceJson := fragment0363535Value :: acc

noncomputable def chunk0081AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0081_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 523)
      (SourceJson.white (chunk0081LeadChars00 ++ (fragment0363535Chars ++ rest))) acc =
      (SourceJson.value (fuel + 522) (fragment0363535Chars ++ rest)).bind
        (chunk0081AfterValue00 (fuel + 522) acc) := by rfl

theorem array_chunk0081 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 523) (SourceJson.white (chunk0081Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 522) (SourceJson.white tail) (chunk0081Push00 acc) := by
  have hinput : chunk0081Chars00 ++ tail = chunk0081LeadChars00 ++ (fragment0363535Chars ++ (chunk0081SuffixChars00 ++ tail)) := by
    simp only [chunk0081Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 523) (SourceJson.white (chunk0081Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 523)
          (SourceJson.white (chunk0081LeadChars00 ++ (fragment0363535Chars ++ (chunk0081SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 523) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 522) (fragment0363535Chars ++ (chunk0081SuffixChars00 ++ tail))).bind
        (chunk0081AfterValue00 (fuel + 522) acc) := array_chunk0081_head fuel (chunk0081SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0363535Value, chunk0081SuffixChars00 ++ tail)).bind
        (chunk0081AfterValue00 (fuel + 522) acc) :=
      congrArg (fun result => result.bind (chunk0081AfterValue00 (fuel + 522) acc))
        (value_fragment0363535 (fuel + 330) (chunk0081SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 522) (SourceJson.white tail) (chunk0081Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0081_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0082_before_reader"
  err.flush

noncomputable def chunk0082LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0082SuffixChars00 : List Char := [',']
noncomputable def chunk0082Chars00 : List Char := chunk0082LeadChars00 ++ fragment0365076Chars ++ chunk0082SuffixChars00
noncomputable def chunk0082Push00 (acc : List SourceJson) : List SourceJson := fragment0365076Value :: acc

noncomputable def chunk0082AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0082_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 522)
      (SourceJson.white (chunk0082LeadChars00 ++ (fragment0365076Chars ++ rest))) acc =
      (SourceJson.value (fuel + 521) (fragment0365076Chars ++ rest)).bind
        (chunk0082AfterValue00 (fuel + 521) acc) := by rfl

theorem array_chunk0082 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 522) (SourceJson.white (chunk0082Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 521) (SourceJson.white tail) (chunk0082Push00 acc) := by
  have hinput : chunk0082Chars00 ++ tail = chunk0082LeadChars00 ++ (fragment0365076Chars ++ (chunk0082SuffixChars00 ++ tail)) := by
    simp only [chunk0082Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 522) (SourceJson.white (chunk0082Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 522)
          (SourceJson.white (chunk0082LeadChars00 ++ (fragment0365076Chars ++ (chunk0082SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 522) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 521) (fragment0365076Chars ++ (chunk0082SuffixChars00 ++ tail))).bind
        (chunk0082AfterValue00 (fuel + 521) acc) := array_chunk0082_head fuel (chunk0082SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0365076Value, chunk0082SuffixChars00 ++ tail)).bind
        (chunk0082AfterValue00 (fuel + 521) acc) :=
      congrArg (fun result => result.bind (chunk0082AfterValue00 (fuel + 521) acc))
        (value_fragment0365076 (fuel + 314) (chunk0082SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 521) (SourceJson.white tail) (chunk0082Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0082_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0081Chars00 ++ chunk0082Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0082Push00 (chunk0081Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 523) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 521) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0081Chars00 ++ (chunk0082Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 523) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 523) (SourceJson.white (chunk0081Chars00 ++ (chunk0082Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 523) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 522) (SourceJson.white (chunk0082Chars00 ++ (tail))) (chunk0081Push00 (acc)) := array_chunk0081 fuel (chunk0082Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 521) (SourceJson.white tail) (blockPush acc) := array_chunk0082 fuel (tail) (chunk0081Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 363529).take 3080 = blockChars := by rfl

theorem block_original_split : sourceRest 363529 = blockChars ++ sourceRest 366609 := by
  calc
    sourceRest 363529 = (sourceRest 363529).take 3080 ++ (sourceRest 363529).drop 3080 :=
      (List.take_append_drop 3080 (sourceRest 363529)).symm
    _ = blockChars ++ (sourceRest 363529).drop 3080 :=
      congrArg (fun part => part ++ (sourceRest 363529).drop 3080) block_original_prefix
    _ = blockChars ++ sourceRest 366609 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 363529 3080)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 523) (SourceJson.white (sourceRest 363529)) acc =
      SourceJson.array (fuel + 521) (SourceJson.white (sourceRest 366609)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 523) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 366609) acc)

#print axioms object_fragment0363535_field_000
#print axioms object_fragment0363535_field_001
#print axioms object_fragment0363535_field_002
#print axioms object_fragment0363535_field_003
#print axioms object_fragment0363535_field_004
#print axioms object_fragment0363535_field_005
#print axioms object_fragment0363535_field_006
#print axioms object_fragment0363535_field_007
#print axioms object_fragment0363535_field_008
#print axioms object_fragment0363535_field_009
#print axioms value_fragment0363535
#print axioms object_fragment0365076_field_000
#print axioms object_fragment0365076_field_001
#print axioms object_fragment0365076_field_002
#print axioms object_fragment0365076_field_003
#print axioms object_fragment0365076_field_004
#print axioms object_fragment0365076_field_005
#print axioms object_fragment0365076_field_006
#print axioms object_fragment0365076_field_007
#print axioms object_fragment0365076_field_008
#print axioms object_fragment0365076_field_009
#print axioms value_fragment0365076
#print axioms array_chunk0081_head
#print axioms array_chunk0081
#print axioms array_chunk0082_head
#print axioms array_chunk0082
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock041

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
