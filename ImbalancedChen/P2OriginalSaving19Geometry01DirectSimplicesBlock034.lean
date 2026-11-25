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

namespace SimplicesBlock034

noncomputable def fragment0339822Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0339822Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0339822Field000Value00 : SourceJson := .number (String.ofList ['6', '7'])
noncomputable def fragment0339822Acc00100 : List (String × SourceJson) := (fragment0339822Field000Key00, fragment0339822Field000Value00) :: fragment0339822Acc00000
noncomputable def fragment0339822Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '7', ',']

theorem object_fragment0339822_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0339822Field000Chars00 ++ tail)) fragment0339822Acc00000 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0339822Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0339822_object_field_000"
  err.flush

noncomputable def fragment0339822Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0339822Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0339822Acc00200 : List (String × SourceJson) := (fragment0339822Field001Key00, fragment0339822Field001Value00) :: fragment0339822Acc00100
noncomputable def fragment0339822Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0339822_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0339822Field001Chars00 ++ tail)) fragment0339822Acc00100 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0339822Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0339822_object_field_001"
  err.flush

noncomputable def fragment0339822Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0339822Field002Value00 : SourceJson := .str (String.ofList ['2', '0', '8', '9', '1', '1', '5', '2', '5', '0', '3', '9', '2', '9', '2', '8', '0', '2', '6', '6', '7', '2', '3', '5', '5', '4', '8', '1', '6', '6', '0', '1', '4', '9', '4', '3', '4', '5', '7', '/', '1', '2', '4', '4', '0', '6', '2', '7', '8', '9', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0339822Acc00300 : List (String × SourceJson) := (fragment0339822Field002Key00, fragment0339822Field002Value00) :: fragment0339822Acc00200
noncomputable def fragment0339822Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '0', '8', '9', '1', '1', '5', '2', '5', '0', '3', '9', '2', '9', '2', '8', '0', '2', '6', '6', '7', '2', '3', '5', '5', '4', '8', '1', '6', '6', '0', '1', '4', '9', '4', '3', '4', '5', '7', '/', '1', '2', '4', '4', '0', '6', '2', '7', '8', '9', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0339822_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0339822Field002Chars00 ++ tail)) fragment0339822Acc00200 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0339822Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0339822_object_field_002"
  err.flush

noncomputable def fragment0339822Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0339822Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0339822Acc00400 : List (String × SourceJson) := (fragment0339822Field003Key00, fragment0339822Field003Value00) :: fragment0339822Acc00300
noncomputable def fragment0339822Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0339822_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0339822Field003Chars00 ++ tail)) fragment0339822Acc00300 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0339822Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0339822_object_field_003"
  err.flush

noncomputable def fragment0339822Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0339822Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0339822Acc00500 : List (String × SourceJson) := (fragment0339822Field004Key00, fragment0339822Field004Value00) :: fragment0339822Acc00400
noncomputable def fragment0339822Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0339822_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0339822Field004Chars00 ++ tail)) fragment0339822Acc00400 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0339822Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0339822_object_field_004"
  err.flush

noncomputable def fragment0339822Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0339822Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '2', '9', '7', '4', '4', '1', '0', '1', '0', '5', '8', '4', '1', '/', '5', '5', '2', '5', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '5', '3', '2', '9', '8', '9', '2', '1', '4', '2', '0', '1', '/', '5', '5', '2', '5', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '5', '6', '8', '8', '0', '9', '9', '2', '7', '6', '7', '9', '/', '1', '2', '7', '5', '2', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '5', '2', '6', '1', '4', '5', '4', '5', '4', '5', '3', '/', '3', '3', '1', '5', '5', '3', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '9', '7', '5', '7', '9', '3', '5', '3', '9', '5', '1', '/', '1', '9', '5', '0', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '5', '4', '4', '5', '1', '3', '1', '2', '7', '6', '1', '7', '/', '3', '3', '1', '5', '5', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '3', '3', '6', '5', '2', '4', '4', '0', '0', '3', '/', '2', '9', '0', '8', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '4', '2', '6', '6', '2', '6', '0', '9', '6', '0', '3', '1', '/', '1', '6', '5', '7', '7', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '1', '1', '8', '8', '1', '3', '0', '0', '3', '0', '9', '7', '/', '1', '6', '5', '7', '7', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '7', '0', '6', '1', '9', '7', '3', '2', '2', '5', '7', '9', '/', '5', '5', '2', '5', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0339822Acc00600 : List (String × SourceJson) := (fragment0339822Field005Key00, fragment0339822Field005Value00) :: fragment0339822Acc00500
noncomputable def fragment0339822Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '9', '7', '4', '4', '1', '0', '1', '0', '5', '8', '4', '1', '/', '5', '5', '2', '5', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '5', '3', '2', '9', '8', '9', '2', '1', '4', '2', '0', '1', '/', '5', '5', '2', '5', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '5', '6', '8', '8', '0', '9', '9', '2', '7', '6', '7', '9', '/', '1', '2', '7', '5', '2', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '5', '2', '6', '1', '4', '5', '4', '5', '4', '5', '3', '/', '3', '3', '1', '5', '5', '3', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '7', '5', '7', '9', '3', '5', '3', '9', '5', '1', '/', '1', '9', '5', '0', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '5', '4', '4', '5', '1', '3', '1', '2', '7', '6', '1', '7', '/', '3', '3', '1', '5', '5', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '3', '3', '6', '5', '2', '4', '4', '0', '0', '3', '/', '2', '9', '0', '8', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '4', '2', '6', '6', '2', '6', '0', '9', '6', '0', '3', '1', '/', '1', '6', '5', '7', '7', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '1', '1', '8', '8', '1', '3', '0', '0', '3', '0', '9', '7', '/', '1', '6', '5', '7', '7', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '0', '6', '1', '9', '7', '3', '2', '2', '5', '7', '9', '/', '5', '5', '2', '5', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0339822_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0339822Field005Chars00 ++ tail)) fragment0339822Acc00500 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0339822Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0339822_object_field_005"
  err.flush

noncomputable def fragment0339822Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0339822Field006Value00 : SourceJson := .str (String.ofList ['7', '9', '9', '5', '9', '0', '5', '3', '4', '8', '4', '9', '5', '6', '0', '2', '0', '9', '7', '0', '3', '8', '8', '2', '7', '9', '8', '5', '7', '7', '7', '8', '7', '6', '3', '2', '0', '4', '3', '4', '4', '6', '0', '4', '5', '0', '0', '0', '/', '1', '2', '4', '5', '8', '3', '0', '8', '3', '4', '4', '6', '9', '4', '8', '4', '7', '3', '6', '4', '8', '2', '5', '9', '8', '8', '4', '6', '6', '7', '4', '7', '8', '9', '5', '9', '0', '1', '1', '3', '9', '4', '9', '6', '2', '7', '7', '4', '9', '0', '7', '3', '5', '4', '0', '3', '3', '7', '0', '9', '3', '5', '5', '5', '3'])
noncomputable def fragment0339822Acc00700 : List (String × SourceJson) := (fragment0339822Field006Key00, fragment0339822Field006Value00) :: fragment0339822Acc00600
noncomputable def fragment0339822Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '9', '9', '5', '9', '0', '5', '3', '4', '8', '4', '9', '5', '6', '0', '2', '0', '9', '7', '0', '3', '8', '8', '2', '7', '9', '8', '5', '7', '7', '7', '8', '7', '6', '3', '2', '0', '4', '3', '4', '4', '6', '0', '4', '5', '0', '0', '0', '/', '1', '2', '4', '5', '8', '3', '0', '8', '3', '4', '4', '6', '9', '4', '8', '4', '7', '3', '6', '4', '8', '2', '5', '9', '8', '8', '4', '6', '6', '7', '4', '7', '8', '9', '5', '9', '0', '1', '1', '3', '9', '4', '9', '6', '2', '7', '7', '4', '9', '0', '7', '3', '5', '4', '0', '3', '3', '7', '0', '9', '3', '5', '5', '5', '3', '"', ',']

theorem object_fragment0339822_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0339822Field006Chars00 ++ tail)) fragment0339822Acc00600 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0339822Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0339822_object_field_006"
  err.flush

noncomputable def fragment0339822Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0339822Field007Value00 : SourceJson := .str (String.ofList ['4', '2', '1', '4', '6', '9', '2', '0', '6', '6', '5', '6', '1', '8', '0', '3', '9', '2', '4', '8', '5', '5', '7', '2', '4', '1', '3', '5', '0', '9', '3', '6', '8', '6', '3', '7', '0', '5', '4', '5', '6', '1', '4', '3', '4', '1', '5', '8', '7', '7', '4', '5', '5', '8', '3', '0', '9', '8', '1', '4', '6', '3', '7', '7', '2', '1', '1', '2', '1', '5', '3', '7', '5', '2', '4', '7', '3', '5', '6', '0', '1', '4', '1', '7', '8', '3', '6', '3', '2', '8', '9', '0', '6', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '0', '0', '7', '7', '3', '9', '0', '1', '9', '4', '5', '0', '5', '9', '6', '5', '4', '4', '7', '3', '4', '0', '3', '1', '4', '5', '1', '1', '2', '5', '5', '7', '5', '4', '4', '8', '8', '3', '2', '7', '7', '2', '9', '3', '9', '7', '7', '3', '5', '4', '6', '1', '3', '7', '7', '2', '4', '8', '9', '2', '8', '5', '2', '0', '1', '5', '4', '3', '6', '8', '6', '9', '0', '8', '2', '5', '9', '7', '0', '4', '2', '4', '1', '3', '6', '8', '0', '0', '1', '9', '6', '3', '1', '9', '6', '8', '2', '0', '8', '0', '4', '1', '1', '4', '8', '5', '8', '6', '4', '2', '6', '7', '2', '0', '4', '5', '1', '4', '8', '0', '4', '8', '3', '0', '2', '5', '1', '4', '7'])
noncomputable def fragment0339822Acc00800 : List (String × SourceJson) := (fragment0339822Field007Key00, fragment0339822Field007Value00) :: fragment0339822Acc00700
noncomputable def fragment0339822Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '2', '1', '4', '6', '9', '2', '0', '6', '6', '5', '6', '1', '8', '0', '3', '9', '2', '4', '8', '5', '5', '7', '2', '4', '1', '3', '5', '0', '9', '3', '6', '8', '6', '3', '7', '0', '5', '4', '5', '6', '1', '4', '3', '4', '1', '5', '8', '7', '7', '4', '5', '5', '8', '3', '0', '9', '8', '1', '4', '6', '3', '7', '7', '2', '1', '1', '2', '1', '5', '3', '7', '5', '2', '4', '7', '3', '5', '6', '0', '1', '4', '1', '7', '8', '3', '6', '3', '2', '8', '9', '0', '6', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '0', '0', '7', '7', '3', '9', '0', '1', '9', '4', '5', '0', '5', '9', '6', '5', '4', '4', '7', '3', '4', '0', '3', '1', '4', '5', '1', '1', '2', '5', '5', '7', '5', '4', '4', '8', '8', '3', '2', '7', '7', '2', '9', '3', '9', '7', '7', '3', '5', '4', '6', '1', '3', '7', '7', '2', '4', '8', '9', '2', '8', '5', '2', '0', '1', '5', '4', '3', '6', '8', '6', '9', '0', '8', '2', '5', '9', '7', '0', '4', '2', '4', '1', '3', '6', '8', '0', '0', '1', '9', '6', '3', '1', '9', '6', '8', '2', '0', '8', '0', '4', '1', '1', '4', '8', '5', '8', '6', '4', '2', '6', '7', '2', '0', '4', '5', '1', '4', '8', '0', '4', '8', '3', '0', '2', '5', '1', '4', '7', '"', ',']

theorem object_fragment0339822_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0339822Field007Chars00 ++ tail)) fragment0339822Acc00700 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0339822Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0339822_object_field_007"
  err.flush

noncomputable def fragment0339822Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0339822Field008Value00 : SourceJson := .str (String.ofList ['5', '0', '8', '4', '9', '6', '7', '1', '6', '3', '0', '5', '0'])
noncomputable def fragment0339822Acc00900 : List (String × SourceJson) := (fragment0339822Field008Key00, fragment0339822Field008Value00) :: fragment0339822Acc00800
noncomputable def fragment0339822Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '0', '8', '4', '9', '6', '7', '1', '6', '3', '0', '5', '0', '"', ',']

theorem object_fragment0339822_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0339822Field008Chars00 ++ tail)) fragment0339822Acc00800 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0339822Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0339822_object_field_008"
  err.flush

noncomputable def fragment0339822Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0339822Field009Value00 : SourceJson := .str (String.ofList ['4', '7', '6', '5', '0', '5', '0', '5', '6', '8', '6', '6', '8', '5'])
noncomputable def fragment0339822Acc01000 : List (String × SourceJson) := (fragment0339822Field009Key00, fragment0339822Field009Value00) :: fragment0339822Acc00900
noncomputable def fragment0339822Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '7', '6', '5', '0', '5', '0', '5', '6', '8', '6', '6', '8', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0339822_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0339822Field009Chars00 ++ tail)) fragment0339822Acc00900 =
      .ok (.obj (fragment0339822Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0339822_object_field_009"
  err.flush

noncomputable def fragment0339822Chars : List Char := '{' :: (fragment0339822Field000Chars00 ++ fragment0339822Field001Chars00 ++ fragment0339822Field002Chars00 ++ fragment0339822Field003Chars00 ++ fragment0339822Field004Chars00 ++ fragment0339822Field005Chars00 ++ fragment0339822Field006Chars00 ++ fragment0339822Field007Chars00 ++ fragment0339822Field008Chars00 ++ fragment0339822Field009Chars00)
noncomputable def fragment0339822Value : SourceJson := .obj (fragment0339822Acc01000.reverse)

theorem value_fragment0339822 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 257) (fragment0339822Chars ++ tail) =
      .ok (fragment0339822Value, tail) := by
  have hinput : fragment0339822Chars ++ tail = '{' :: (fragment0339822Field000Chars00 ++ (fragment0339822Field001Chars00 ++ (fragment0339822Field002Chars00 ++ (fragment0339822Field003Chars00 ++ (fragment0339822Field004Chars00 ++ (fragment0339822Field005Chars00 ++ (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0339822Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 257) (fragment0339822Chars ++ tail) =
        SourceJson.value (fuel + 257) ('{' :: (fragment0339822Field000Chars00 ++ (fragment0339822Field001Chars00 ++ (fragment0339822Field002Chars00 ++ (fragment0339822Field003Chars00 ++ (fragment0339822Field004Chars00 ++ (fragment0339822Field005Chars00 ++ (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 257)) hinput
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0339822Field000Chars00 ++ (fragment0339822Field001Chars00 ++ (fragment0339822Field002Chars00 ++ (fragment0339822Field003Chars00 ++ (fragment0339822Field004Chars00 ++ (fragment0339822Field005Chars00 ++ (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail)))))))))))) fragment0339822Acc00000 := by rfl
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0339822Field001Chars00 ++ (fragment0339822Field002Chars00 ++ (fragment0339822Field003Chars00 ++ (fragment0339822Field004Chars00 ++ (fragment0339822Field005Chars00 ++ (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail))))))))))) fragment0339822Acc00100 := object_fragment0339822_field_000 fuel (fragment0339822Field001Chars00 ++ (fragment0339822Field002Chars00 ++ (fragment0339822Field003Chars00 ++ (fragment0339822Field004Chars00 ++ (fragment0339822Field005Chars00 ++ (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0339822Field002Chars00 ++ (fragment0339822Field003Chars00 ++ (fragment0339822Field004Chars00 ++ (fragment0339822Field005Chars00 ++ (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail)))))))))) fragment0339822Acc00200 := object_fragment0339822_field_001 fuel (fragment0339822Field002Chars00 ++ (fragment0339822Field003Chars00 ++ (fragment0339822Field004Chars00 ++ (fragment0339822Field005Chars00 ++ (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0339822Field003Chars00 ++ (fragment0339822Field004Chars00 ++ (fragment0339822Field005Chars00 ++ (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail))))))))) fragment0339822Acc00300 := object_fragment0339822_field_002 fuel (fragment0339822Field003Chars00 ++ (fragment0339822Field004Chars00 ++ (fragment0339822Field005Chars00 ++ (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0339822Field004Chars00 ++ (fragment0339822Field005Chars00 ++ (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail)))))))) fragment0339822Acc00400 := object_fragment0339822_field_003 fuel (fragment0339822Field004Chars00 ++ (fragment0339822Field005Chars00 ++ (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0339822Field005Chars00 ++ (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail))))))) fragment0339822Acc00500 := object_fragment0339822_field_004 fuel (fragment0339822Field005Chars00 ++ (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail)))))) fragment0339822Acc00600 := object_fragment0339822_field_005 fuel (fragment0339822Field006Chars00 ++ (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail))))) fragment0339822Acc00700 := object_fragment0339822_field_006 fuel (fragment0339822Field007Chars00 ++ (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail)))) fragment0339822Acc00800 := object_fragment0339822_field_007 fuel (fragment0339822Field008Chars00 ++ (fragment0339822Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0339822Field009Chars00 ++ (tail))) fragment0339822Acc00900 := object_fragment0339822_field_008 fuel (fragment0339822Field009Chars00 ++ (tail))
    _ = .ok (fragment0339822Value, tail) := object_fragment0339822_field_009 fuel (tail)

noncomputable def fragment0341465Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0341465Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0341465Field000Value00 : SourceJson := .number (String.ofList ['6', '8'])
noncomputable def fragment0341465Acc00100 : List (String × SourceJson) := (fragment0341465Field000Key00, fragment0341465Field000Value00) :: fragment0341465Acc00000
noncomputable def fragment0341465Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '8', ',']

theorem object_fragment0341465_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 403) (SourceJson.white (fragment0341465Field000Chars00 ++ tail)) fragment0341465Acc00000 =
      SourceJson.object (fuel + 402) (SourceJson.white tail) fragment0341465Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0341465_object_field_000"
  err.flush

noncomputable def fragment0341465Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0341465Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0341465Acc00200 : List (String × SourceJson) := (fragment0341465Field001Key00, fragment0341465Field001Value00) :: fragment0341465Acc00100
noncomputable def fragment0341465Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0341465_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 402) (SourceJson.white (fragment0341465Field001Chars00 ++ tail)) fragment0341465Acc00100 =
      SourceJson.object (fuel + 401) (SourceJson.white tail) fragment0341465Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0341465_object_field_001"
  err.flush

noncomputable def fragment0341465Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0341465Field002Value00 : SourceJson := .str (String.ofList ['6', '2', '4', '5', '6', '5', '8', '0', '1', '1', '7', '8', '9', '0', '3', '8', '7', '3', '1', '7', '3', '1', '5', '6', '0', '7', '9', '2', '4', '8', '9', '0', '1', '6', '9', '7', '7', '5', '2', '9', '/', '1', '8', '7', '1', '8', '3', '6', '0', '1', '2', '7', '0', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0341465Acc00300 : List (String × SourceJson) := (fragment0341465Field002Key00, fragment0341465Field002Value00) :: fragment0341465Acc00200
noncomputable def fragment0341465Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '2', '4', '5', '6', '5', '8', '0', '1', '1', '7', '8', '9', '0', '3', '8', '7', '3', '1', '7', '3', '1', '5', '6', '0', '7', '9', '2', '4', '8', '9', '0', '1', '6', '9', '7', '7', '5', '2', '9', '/', '1', '8', '7', '1', '8', '3', '6', '0', '1', '2', '7', '0', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0341465_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 401) (SourceJson.white (fragment0341465Field002Chars00 ++ tail)) fragment0341465Acc00200 =
      SourceJson.object (fuel + 400) (SourceJson.white tail) fragment0341465Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0341465_object_field_002"
  err.flush

noncomputable def fragment0341465Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0341465Field003Value00 : SourceJson := .str (String.ofList ['6', '6', '3', '6', '9', '1', '0', '9', '/', '9', '9', '7', '5', '6', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0341465Acc00400 : List (String × SourceJson) := (fragment0341465Field003Key00, fragment0341465Field003Value00) :: fragment0341465Acc00300
noncomputable def fragment0341465Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '6', '3', '6', '9', '1', '0', '9', '/', '9', '9', '7', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0341465_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0341465Field003Chars00 ++ tail)) fragment0341465Acc00300 =
      SourceJson.object (fuel + 399) (SourceJson.white tail) fragment0341465Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0341465_object_field_003"
  err.flush

noncomputable def fragment0341465Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0341465Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '7', '/', '2', '0', '8', '6', '4']), .str (String.ofList ['9', '5', '7', '/', '2', '0', '8', '6', '4'])]
noncomputable def fragment0341465Acc00500 : List (String × SourceJson) := (fragment0341465Field004Key00, fragment0341465Field004Value00) :: fragment0341465Acc00400
noncomputable def fragment0341465Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '/', '2', '0', '8', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '/', '2', '0', '8', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0341465_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 399) (SourceJson.white (fragment0341465Field004Chars00 ++ tail)) fragment0341465Acc00400 =
      SourceJson.object (fuel + 398) (SourceJson.white tail) fragment0341465Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0341465_object_field_004"
  err.flush

noncomputable def fragment0341465Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0341465Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '7', '4', '4', '2', '1', '9', '7', '1', '1', '4', '5', '2', '8', '2', '8', '9', '4', '0', '7', '/', '6', '3', '6', '9', '0', '5', '2', '1', '6', '2', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '3', '9', '8', '6', '4', '5', '2', '1', '6', '6', '0', '2', '5', '2', '6', '2', '2', '0', '3', '/', '1', '2', '1', '0', '1', '1', '9', '9', '1', '0', '8', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '0', '0', '3', '1', '2', '7', '9', '8', '2', '2', '6', '5', '8', '5', '2', '6', '7', '2', '1', '/', '3', '6', '3', '0', '3', '5', '9', '7', '3', '2', '5', '0', '9', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '6', '6', '6', '3', '1', '4', '1', '6', '1', '9', '2', '5', '7', '4', '4', '2', '5', '8', '9', '/', '3', '6', '3', '0', '3', '5', '9', '7', '3', '2', '5', '0', '9', '8', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '9', '3', '8', '8', '1', '1', '8', '0', '6', '0', '3', '5', '9', '3', '2', '9', '/', '4', '4', '4', '8', '9', '7', '0', '2', '6', '0', '4', '2', '8', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '0', '0', '4', '6', '4', '6', '8', '7', '7', '6', '6', '2', '0', '1', '5', '0', '6', '9', '7', '/', '7', '2', '6', '0', '7', '1', '9', '4', '6', '5', '0', '1', '9', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '8', '2', '3', '3', '5', '2', '4', '1', '9', '6', '9', '9', '8', '8', '3', '7', '1', '1', '/', '7', '5', '6', '3', '2', '4', '9', '4', '4', '2', '7', '2', '8', '8', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '0', '0', '6', '7', '9', '8', '6', '7', '2', '4', '3', '2', '0', '8', '9', '5', '4', '2', '9', '/', '1', '8', '1', '5', '1', '7', '9', '8', '6', '6', '2', '5', '4', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '1', '8', '9', '8', '5', '5', '5', '3', '2', '4', '4', '3', '0', '4', '2', '2', '5', '3', '3', '1', '/', '3', '6', '3', '0', '3', '5', '9', '7', '3', '2', '5', '0', '9', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '1', '8', '9', '8', '0', '7', '1', '2', '7', '6', '4', '6', '6', '0', '8', '7', '8', '8', '5', '1', '/', '3', '6', '3', '0', '3', '5', '9', '7', '3', '2', '5', '0', '9', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0341465Acc00600 : List (String × SourceJson) := (fragment0341465Field005Key00, fragment0341465Field005Value00) :: fragment0341465Acc00500
noncomputable def fragment0341465Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '4', '4', '2', '1', '9', '7', '1', '1', '4', '5', '2', '8', '2', '8', '9', '4', '0', '7', '/', '6', '3', '6', '9', '0', '5', '2', '1', '6', '2', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '3', '9', '8', '6', '4', '5', '2', '1', '6', '6', '0', '2', '5', '2', '6', '2', '2', '0', '3', '/', '1', '2', '1', '0', '1', '1', '9', '9', '1', '0', '8', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '0', '0', '3', '1', '2', '7', '9', '8', '2', '2', '6', '5', '8', '5', '2', '6', '7', '2', '1', '/', '3', '6', '3', '0', '3', '5', '9', '7', '3', '2', '5', '0', '9', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '6', '6', '6', '3', '1', '4', '1', '6', '1', '9', '2', '5', '7', '4', '4', '2', '5', '8', '9', '/', '3', '6', '3', '0', '3', '5', '9', '7', '3', '2', '5', '0', '9', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '9', '3', '8', '8', '1', '1', '8', '0', '6', '0', '3', '5', '9', '3', '2', '9', '/', '4', '4', '4', '8', '9', '7', '0', '2', '6', '0', '4', '2', '8', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '0', '0', '4', '6', '4', '6', '8', '7', '7', '6', '6', '2', '0', '1', '5', '0', '6', '9', '7', '/', '7', '2', '6', '0', '7', '1', '9', '4', '6', '5', '0', '1', '9', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '8', '2', '3', '3', '5', '2', '4', '1', '9', '6', '9', '9', '8', '8', '3', '7', '1', '1', '/', '7', '5', '6', '3', '2', '4', '9', '4', '4', '2', '7', '2', '8', '8', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '0', '0', '6', '7', '9', '8', '6', '7', '2', '4', '3', '2', '0', '8', '9', '5', '4', '2', '9', '/', '1', '8', '1', '5', '1', '7', '9', '8', '6', '6', '2', '5', '4', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '8', '9', '8', '5', '5', '5', '3', '2', '4', '4', '3', '0', '4', '2', '2', '5', '3', '3', '1', '/', '3', '6', '3', '0', '3', '5', '9', '7', '3', '2', '5', '0', '9', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '8', '9', '8', '0', '7', '1', '2', '7', '6', '4', '6', '6', '0', '8', '7', '8', '8', '5', '1', '/', '3', '6', '3', '0', '3', '5', '9', '7', '3', '2', '5', '0', '9', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0341465_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 398) (SourceJson.white (fragment0341465Field005Chars00 ++ tail)) fragment0341465Acc00500 =
      SourceJson.object (fuel + 397) (SourceJson.white tail) fragment0341465Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0341465_object_field_005"
  err.flush

noncomputable def fragment0341465Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0341465Field006Value00 : SourceJson := .str (String.ofList ['3', '5', '1', '2', '9', '4', '6', '7', '7', '0', '8', '4', '7', '9', '2', '5', '6', '0', '0', '7', '7', '5', '5', '5', '6', '7', '4', '0', '9', '9', '9', '1', '8', '5', '8', '1', '8', '6', '3', '8', '2', '7', '3', '0', '2', '2', '4', '/', '2', '3', '6', '5', '1', '5', '9', '2', '5', '2', '1', '3', '7', '2', '0', '9', '1', '2', '7', '7', '7', '8', '1', '7', '9', '8', '1', '4', '2', '6', '4', '2', '6', '9', '2', '0', '0', '9', '1', '4', '8', '8', '6', '5', '1', '6', '4', '7', '4', '6', '5', '0', '9', '5', '0', '6', '1', '5', '2', '3', '4', '3', '7', '5'])
noncomputable def fragment0341465Acc00700 : List (String × SourceJson) := (fragment0341465Field006Key00, fragment0341465Field006Value00) :: fragment0341465Acc00600
noncomputable def fragment0341465Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '5', '1', '2', '9', '4', '6', '7', '7', '0', '8', '4', '7', '9', '2', '5', '6', '0', '0', '7', '7', '5', '5', '5', '6', '7', '4', '0', '9', '9', '9', '1', '8', '5', '8', '1', '8', '6', '3', '8', '2', '7', '3', '0', '2', '2', '4', '/', '2', '3', '6', '5', '1', '5', '9', '2', '5', '2', '1', '3', '7', '2', '0', '9', '1', '2', '7', '7', '7', '8', '1', '7', '9', '8', '1', '4', '2', '6', '4', '2', '6', '9', '2', '0', '0', '9', '1', '4', '8', '8', '6', '5', '1', '6', '4', '7', '4', '6', '5', '0', '9', '5', '0', '6', '1', '5', '2', '3', '4', '3', '7', '5', '"', ',']

theorem object_fragment0341465_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 397) (SourceJson.white (fragment0341465Field006Chars00 ++ tail)) fragment0341465Acc00600 =
      SourceJson.object (fuel + 396) (SourceJson.white tail) fragment0341465Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0341465_object_field_006"
  err.flush

noncomputable def fragment0341465Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0341465Field007Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '7', '7', '8', '8', '5', '8', '4', '4', '6', '7', '9', '8', '7', '8', '0', '0', '3', '3', '0', '4', '8', '4', '8', '5', '4', '5', '3', '9', '3', '0', '0', '8', '9', '2', '0', '6', '3', '0', '4', '7', '3', '4', '0', '8', '4', '6', '7', '7', '5', '0', '9', '7', '6', '9', '4', '1', '3', '3', '4', '0', '0', '7', '1', '7', '9', '3', '2', '2', '1', '2', '5', '6', '3', '4', '6', '4', '5', '9', '3', '3', '3', '6', '4', '0', '0', '8', '7', '7', '1', '2', '6', '8', '0', '0', '1', '5', '8', '1', '8', '0', '0', '2', '1', '0', '7', '1', '1', '3', '9', '6', '2', '5', '2', '2', '9', '1', '0', '2', '1', '1', '5', '1', '4', '4', '7', '2', '9', '3', '5', '9', '7', '5', '5', '1', '6', '1', '9', '7', '6', '9', '7', '2', '0', '4', '6', '0', '8', '0', '0', '6', '9', '8', '1', '9', '5', '1', '2', '8', '9', '9', '2', '3', '3', '8', '6', '7', '1', '1', '6', '6', '9', '9', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '3', '3', '8', '7', '1', '1', '0', '3', '4', '4', '0', '5', '2', '4', '5', '1', '7', '3', '8', '7', '4', '6', '6', '2', '9', '1', '5', '4', '8', '9', '9', '1', '2', '2', '4', '3', '7', '8', '2', '8', '0', '0', '5', '2', '5', '7', '0', '9', '7', '0', '5', '9', '9', '9', '9', '6', '0', '5', '4', '7', '5', '9', '2', '4', '3', '5', '4', '4', '8', '4', '5', '2', '6', '4', '8', '9', '3', '4', '9', '6', '4', '2', '5', '4', '9', '2', '9', '0', '2', '4', '6', '9', '5', '9', '6', '2', '0', '2', '6', '4', '6', '0', '0', '4', '0', '4', '0', '6', '3', '1', '0', '0', '4', '1', '9', '3', '0', '4', '6', '2', '9', '7', '1', '6', '1', '3', '4', '3', '1', '6', '3', '0', '6', '3', '8', '9', '1', '7', '0', '5', '1', '1', '9', '9', '5', '8', '8', '3', '6', '6', '9', '5', '8', '7', '9', '6', '4', '1', '9', '3', '3', '7', '5', '7', '3', '0', '2', '1', '0', '6', '0', '5', '2', '4', '3', '1', '4', '9', '3', '5', '3', '5', '7', '4', '9', '1', '5', '4', '7', '7', '8', '5', '5', '1', '8', '7', '0', '2', '2', '3', '3', '9'])
noncomputable def fragment0341465Acc00800 : List (String × SourceJson) := (fragment0341465Field007Key00, fragment0341465Field007Value00) :: fragment0341465Acc00700
noncomputable def fragment0341465Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '3', '7', '7', '8', '8', '5', '8', '4', '4', '6', '7', '9', '8', '7', '8', '0', '0', '3', '3', '0', '4', '8', '4', '8', '5', '4', '5', '3', '9', '3', '0', '0', '8', '9', '2', '0', '6', '3', '0', '4', '7', '3', '4', '0', '8', '4', '6', '7', '7', '5', '0', '9', '7', '6', '9', '4', '1', '3', '3', '4', '0', '0', '7', '1', '7', '9', '3', '2', '2', '1', '2', '5', '6', '3', '4', '6', '4', '5', '9', '3', '3', '3', '6', '4', '0', '0', '8', '7', '7', '1', '2', '6', '8', '0', '0', '1', '5', '8', '1', '8', '0', '0', '2', '1', '0', '7', '1', '1', '3', '9', '6', '2', '5', '2', '2', '9', '1', '0', '2', '1', '1', '5', '1', '4', '4', '7', '2', '9', '3', '5', '9', '7', '5', '5', '1', '6', '1', '9', '7', '6', '9', '7', '2', '0', '4', '6', '0', '8', '0', '0', '6', '9', '8', '1', '9', '5', '1', '2', '8', '9', '9', '2', '3', '3', '8', '6', '7', '1', '1', '6', '6', '9', '9', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '3', '3', '8', '7', '1', '1', '0', '3', '4', '4', '0', '5', '2', '4', '5', '1', '7', '3', '8', '7', '4', '6', '6', '2', '9', '1', '5', '4', '8', '9', '9', '1', '2', '2', '4', '3', '7', '8', '2', '8', '0', '0', '5', '2', '5', '7', '0', '9', '7', '0', '5', '9', '9', '9', '9', '6', '0', '5', '4', '7', '5', '9', '2', '4', '3', '5', '4', '4', '8', '4', '5', '2', '6', '4', '8', '9', '3', '4', '9', '6', '4', '2', '5', '4', '9', '2', '9', '0', '2', '4', '6', '9', '5', '9', '6', '2', '0', '2', '6', '4', '6', '0', '0', '4', '0', '4', '0', '6', '3', '1', '0', '0', '4', '1', '9', '3', '0', '4', '6', '2', '9', '7', '1', '6', '1', '3', '4', '3', '1', '6', '3', '0', '6', '3', '8', '9', '1', '7', '0', '5', '1', '1', '9', '9', '5', '8', '8', '3', '6', '6', '9', '5', '8', '7', '9', '6', '4', '1', '9', '3', '3', '7', '5', '7', '3', '0', '2', '1', '0', '6', '0', '5', '2', '4', '3', '1', '4', '9', '3', '5', '3', '5', '7', '4', '9', '1', '5', '4', '7', '7', '8', '5', '5', '1', '8', '7', '0', '2', '2', '3', '3', '9', '"', ',']

theorem object_fragment0341465_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 396) (SourceJson.white (fragment0341465Field007Chars00 ++ tail)) fragment0341465Acc00700 =
      SourceJson.object (fuel + 395) (SourceJson.white tail) fragment0341465Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0341465_object_field_007"
  err.flush

noncomputable def fragment0341465Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0341465Field008Value00 : SourceJson := .str (String.ofList ['1', '1', '7', '6', '7', '6', '7', '7', '6', '9', '0', '7', '6'])
noncomputable def fragment0341465Acc00900 : List (String × SourceJson) := (fragment0341465Field008Key00, fragment0341465Field008Value00) :: fragment0341465Acc00800
noncomputable def fragment0341465Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '7', '6', '7', '6', '7', '7', '6', '9', '0', '7', '6', '"', ',']

theorem object_fragment0341465_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 395) (SourceJson.white (fragment0341465Field008Chars00 ++ tail)) fragment0341465Acc00800 =
      SourceJson.object (fuel + 394) (SourceJson.white tail) fragment0341465Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0341465_object_field_008"
  err.flush

noncomputable def fragment0341465Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0341465Field009Value00 : SourceJson := .str (String.ofList ['1', '1', '0', '1', '8', '1', '3', '8', '2', '6', '2', '3', '3', '2'])
noncomputable def fragment0341465Acc01000 : List (String × SourceJson) := (fragment0341465Field009Key00, fragment0341465Field009Value00) :: fragment0341465Acc00900
noncomputable def fragment0341465Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '0', '1', '8', '1', '3', '8', '2', '6', '2', '3', '3', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0341465_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 394) (SourceJson.white (fragment0341465Field009Chars00 ++ tail)) fragment0341465Acc00900 =
      .ok (.obj (fragment0341465Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0341465_object_field_009"
  err.flush

noncomputable def fragment0341465Chars : List Char := '{' :: (fragment0341465Field000Chars00 ++ fragment0341465Field001Chars00 ++ fragment0341465Field002Chars00 ++ fragment0341465Field003Chars00 ++ fragment0341465Field004Chars00 ++ fragment0341465Field005Chars00 ++ fragment0341465Field006Chars00 ++ fragment0341465Field007Chars00 ++ fragment0341465Field008Chars00 ++ fragment0341465Field009Chars00)
noncomputable def fragment0341465Value : SourceJson := .obj (fragment0341465Acc01000.reverse)

theorem value_fragment0341465 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 404) (fragment0341465Chars ++ tail) =
      .ok (fragment0341465Value, tail) := by
  have hinput : fragment0341465Chars ++ tail = '{' :: (fragment0341465Field000Chars00 ++ (fragment0341465Field001Chars00 ++ (fragment0341465Field002Chars00 ++ (fragment0341465Field003Chars00 ++ (fragment0341465Field004Chars00 ++ (fragment0341465Field005Chars00 ++ (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0341465Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 404) (fragment0341465Chars ++ tail) =
        SourceJson.value (fuel + 404) ('{' :: (fragment0341465Field000Chars00 ++ (fragment0341465Field001Chars00 ++ (fragment0341465Field002Chars00 ++ (fragment0341465Field003Chars00 ++ (fragment0341465Field004Chars00 ++ (fragment0341465Field005Chars00 ++ (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 404)) hinput
    _ = SourceJson.object (fuel + 403) (SourceJson.white (fragment0341465Field000Chars00 ++ (fragment0341465Field001Chars00 ++ (fragment0341465Field002Chars00 ++ (fragment0341465Field003Chars00 ++ (fragment0341465Field004Chars00 ++ (fragment0341465Field005Chars00 ++ (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail)))))))))))) fragment0341465Acc00000 := by rfl
    _ = SourceJson.object (fuel + 402) (SourceJson.white (fragment0341465Field001Chars00 ++ (fragment0341465Field002Chars00 ++ (fragment0341465Field003Chars00 ++ (fragment0341465Field004Chars00 ++ (fragment0341465Field005Chars00 ++ (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail))))))))))) fragment0341465Acc00100 := object_fragment0341465_field_000 fuel (fragment0341465Field001Chars00 ++ (fragment0341465Field002Chars00 ++ (fragment0341465Field003Chars00 ++ (fragment0341465Field004Chars00 ++ (fragment0341465Field005Chars00 ++ (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 401) (SourceJson.white (fragment0341465Field002Chars00 ++ (fragment0341465Field003Chars00 ++ (fragment0341465Field004Chars00 ++ (fragment0341465Field005Chars00 ++ (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail)))))))))) fragment0341465Acc00200 := object_fragment0341465_field_001 fuel (fragment0341465Field002Chars00 ++ (fragment0341465Field003Chars00 ++ (fragment0341465Field004Chars00 ++ (fragment0341465Field005Chars00 ++ (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0341465Field003Chars00 ++ (fragment0341465Field004Chars00 ++ (fragment0341465Field005Chars00 ++ (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail))))))))) fragment0341465Acc00300 := object_fragment0341465_field_002 fuel (fragment0341465Field003Chars00 ++ (fragment0341465Field004Chars00 ++ (fragment0341465Field005Chars00 ++ (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 399) (SourceJson.white (fragment0341465Field004Chars00 ++ (fragment0341465Field005Chars00 ++ (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail)))))))) fragment0341465Acc00400 := object_fragment0341465_field_003 fuel (fragment0341465Field004Chars00 ++ (fragment0341465Field005Chars00 ++ (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 398) (SourceJson.white (fragment0341465Field005Chars00 ++ (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail))))))) fragment0341465Acc00500 := object_fragment0341465_field_004 fuel (fragment0341465Field005Chars00 ++ (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 397) (SourceJson.white (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail)))))) fragment0341465Acc00600 := object_fragment0341465_field_005 fuel (fragment0341465Field006Chars00 ++ (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 396) (SourceJson.white (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail))))) fragment0341465Acc00700 := object_fragment0341465_field_006 fuel (fragment0341465Field007Chars00 ++ (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 395) (SourceJson.white (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail)))) fragment0341465Acc00800 := object_fragment0341465_field_007 fuel (fragment0341465Field008Chars00 ++ (fragment0341465Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 394) (SourceJson.white (fragment0341465Field009Chars00 ++ (tail))) fragment0341465Acc00900 := object_fragment0341465_field_008 fuel (fragment0341465Field009Chars00 ++ (tail))
    _ = .ok (fragment0341465Value, tail) := object_fragment0341465_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0067_before_reader"
  err.flush

noncomputable def chunk0067LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0067SuffixChars00 : List Char := [',']
noncomputable def chunk0067Chars00 : List Char := chunk0067LeadChars00 ++ fragment0339822Chars ++ chunk0067SuffixChars00
noncomputable def chunk0067Push00 (acc : List SourceJson) : List SourceJson := fragment0339822Value :: acc

noncomputable def chunk0067AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0067_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 537)
      (SourceJson.white (chunk0067LeadChars00 ++ (fragment0339822Chars ++ rest))) acc =
      (SourceJson.value (fuel + 536) (fragment0339822Chars ++ rest)).bind
        (chunk0067AfterValue00 (fuel + 536) acc) := by rfl

theorem array_chunk0067 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 537) (SourceJson.white (chunk0067Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 536) (SourceJson.white tail) (chunk0067Push00 acc) := by
  have hinput : chunk0067Chars00 ++ tail = chunk0067LeadChars00 ++ (fragment0339822Chars ++ (chunk0067SuffixChars00 ++ tail)) := by
    simp only [chunk0067Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 537) (SourceJson.white (chunk0067Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 537)
          (SourceJson.white (chunk0067LeadChars00 ++ (fragment0339822Chars ++ (chunk0067SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 537) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 536) (fragment0339822Chars ++ (chunk0067SuffixChars00 ++ tail))).bind
        (chunk0067AfterValue00 (fuel + 536) acc) := array_chunk0067_head fuel (chunk0067SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0339822Value, chunk0067SuffixChars00 ++ tail)).bind
        (chunk0067AfterValue00 (fuel + 536) acc) :=
      congrArg (fun result => result.bind (chunk0067AfterValue00 (fuel + 536) acc))
        (value_fragment0339822 (fuel + 279) (chunk0067SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 536) (SourceJson.white tail) (chunk0067Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0067_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0068_before_reader"
  err.flush

noncomputable def chunk0068LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0068SuffixChars00 : List Char := [',']
noncomputable def chunk0068Chars00 : List Char := chunk0068LeadChars00 ++ fragment0341465Chars ++ chunk0068SuffixChars00
noncomputable def chunk0068Push00 (acc : List SourceJson) : List SourceJson := fragment0341465Value :: acc

noncomputable def chunk0068AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0068_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 536)
      (SourceJson.white (chunk0068LeadChars00 ++ (fragment0341465Chars ++ rest))) acc =
      (SourceJson.value (fuel + 535) (fragment0341465Chars ++ rest)).bind
        (chunk0068AfterValue00 (fuel + 535) acc) := by rfl

theorem array_chunk0068 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 536) (SourceJson.white (chunk0068Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 535) (SourceJson.white tail) (chunk0068Push00 acc) := by
  have hinput : chunk0068Chars00 ++ tail = chunk0068LeadChars00 ++ (fragment0341465Chars ++ (chunk0068SuffixChars00 ++ tail)) := by
    simp only [chunk0068Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 536) (SourceJson.white (chunk0068Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 536)
          (SourceJson.white (chunk0068LeadChars00 ++ (fragment0341465Chars ++ (chunk0068SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 536) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 535) (fragment0341465Chars ++ (chunk0068SuffixChars00 ++ tail))).bind
        (chunk0068AfterValue00 (fuel + 535) acc) := array_chunk0068_head fuel (chunk0068SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0341465Value, chunk0068SuffixChars00 ++ tail)).bind
        (chunk0068AfterValue00 (fuel + 535) acc) :=
      congrArg (fun result => result.bind (chunk0068AfterValue00 (fuel + 535) acc))
        (value_fragment0341465 (fuel + 131) (chunk0068SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 535) (SourceJson.white tail) (chunk0068Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0068_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0067Chars00 ++ chunk0068Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0068Push00 (chunk0067Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 537) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 535) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0067Chars00 ++ (chunk0068Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 537) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 537) (SourceJson.white (chunk0067Chars00 ++ (chunk0068Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 537) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 536) (SourceJson.white (chunk0068Chars00 ++ (tail))) (chunk0067Push00 (acc)) := array_chunk0067 fuel (chunk0068Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 535) (SourceJson.white tail) (blockPush acc) := array_chunk0068 fuel (tail) (chunk0067Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 339816).take 3566 = blockChars := by rfl

theorem block_original_split : sourceRest 339816 = blockChars ++ sourceRest 343382 := by
  calc
    sourceRest 339816 = (sourceRest 339816).take 3566 ++ (sourceRest 339816).drop 3566 :=
      (List.take_append_drop 3566 (sourceRest 339816)).symm
    _ = blockChars ++ (sourceRest 339816).drop 3566 :=
      congrArg (fun part => part ++ (sourceRest 339816).drop 3566) block_original_prefix
    _ = blockChars ++ sourceRest 343382 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 339816 3566)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 537) (SourceJson.white (sourceRest 339816)) acc =
      SourceJson.array (fuel + 535) (SourceJson.white (sourceRest 343382)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 537) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 343382) acc)

#print axioms object_fragment0339822_field_000
#print axioms object_fragment0339822_field_001
#print axioms object_fragment0339822_field_002
#print axioms object_fragment0339822_field_003
#print axioms object_fragment0339822_field_004
#print axioms object_fragment0339822_field_005
#print axioms object_fragment0339822_field_006
#print axioms object_fragment0339822_field_007
#print axioms object_fragment0339822_field_008
#print axioms object_fragment0339822_field_009
#print axioms value_fragment0339822
#print axioms object_fragment0341465_field_000
#print axioms object_fragment0341465_field_001
#print axioms object_fragment0341465_field_002
#print axioms object_fragment0341465_field_003
#print axioms object_fragment0341465_field_004
#print axioms object_fragment0341465_field_005
#print axioms object_fragment0341465_field_006
#print axioms object_fragment0341465_field_007
#print axioms object_fragment0341465_field_008
#print axioms object_fragment0341465_field_009
#print axioms value_fragment0341465
#print axioms array_chunk0067_head
#print axioms array_chunk0067
#print axioms array_chunk0068_head
#print axioms array_chunk0068
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock034

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
