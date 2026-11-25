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

namespace SimplicesBlock066

noncomputable def fragment0447212Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0447212Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0447212Field000Value00 : SourceJson := .number (String.ofList ['1', '3', '0'])
noncomputable def fragment0447212Acc00100 : List (String × SourceJson) := (fragment0447212Field000Key00, fragment0447212Field000Value00) :: fragment0447212Acc00000
noncomputable def fragment0447212Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '0', ',']

theorem object_fragment0447212_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 181) (SourceJson.white (fragment0447212Field000Chars00 ++ tail)) fragment0447212Acc00000 =
      SourceJson.object (fuel + 180) (SourceJson.white tail) fragment0447212Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0447212_object_field_000"
  err.flush

noncomputable def fragment0447212Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0447212Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0447212Acc00200 : List (String × SourceJson) := (fragment0447212Field001Key00, fragment0447212Field001Value00) :: fragment0447212Acc00100
noncomputable def fragment0447212Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0447212_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 180) (SourceJson.white (fragment0447212Field001Chars00 ++ tail)) fragment0447212Acc00100 =
      SourceJson.object (fuel + 179) (SourceJson.white tail) fragment0447212Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0447212_object_field_001"
  err.flush

noncomputable def fragment0447212Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0447212Field002Value00 : SourceJson := .str (String.ofList ['1', '3', '1', '9', '8', '0', '4', '7', '5', '8', '1', '4', '0', '1', '5', '5', '0', '9', '0', '9', '4', '6', '3', '2', '4', '8', '2', '4', '6', '9', '0', '3', '/', '4', '1', '7', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0447212Acc00300 : List (String × SourceJson) := (fragment0447212Field002Key00, fragment0447212Field002Value00) :: fragment0447212Acc00200
noncomputable def fragment0447212Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '3', '1', '9', '8', '0', '4', '7', '5', '8', '1', '4', '0', '1', '5', '5', '0', '9', '0', '9', '4', '6', '3', '2', '4', '8', '2', '4', '6', '9', '0', '3', '/', '4', '1', '7', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0447212_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 179) (SourceJson.white (fragment0447212Field002Chars00 ++ tail)) fragment0447212Acc00200 =
      SourceJson.object (fuel + 178) (SourceJson.white tail) fragment0447212Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0447212_object_field_002"
  err.flush

noncomputable def fragment0447212Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0447212Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0447212Acc00400 : List (String × SourceJson) := (fragment0447212Field003Key00, fragment0447212Field003Value00) :: fragment0447212Acc00300
noncomputable def fragment0447212Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0447212_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 178) (SourceJson.white (fragment0447212Field003Chars00 ++ tail)) fragment0447212Acc00300 =
      SourceJson.object (fuel + 177) (SourceJson.white tail) fragment0447212Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0447212_object_field_003"
  err.flush

noncomputable def fragment0447212Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0447212Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '1', '5', '6', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0447212Acc00500 : List (String × SourceJson) := (fragment0447212Field004Key00, fragment0447212Field004Value00) :: fragment0447212Acc00400
noncomputable def fragment0447212Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '5', '6', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0447212_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 177) (SourceJson.white (fragment0447212Field004Chars00 ++ tail)) fragment0447212Acc00400 =
      SourceJson.object (fuel + 176) (SourceJson.white tail) fragment0447212Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0447212_object_field_004"
  err.flush

noncomputable def fragment0447212Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0447212Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '6', '1', '6', '8', '2', '9', '9', '1', '6', '9', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '6', '7', '7', '6', '4', '1', '8', '2', '1', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '5', '8', '9', '4', '7', '7', '/', '1', '6', '1', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '9', '3', '0', '4', '0', '8', '0', '1', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '4', '6', '0', '2', '5', '3', '/', '2', '4', '7', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '1', '0', '3', '6', '1', '5', '7', '7', '/', '8', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '7', '9', '8', '4', '5', '5', '6', '8', '9', '/', '2', '5', '1', '9', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '3', '7', '8', '6', '7', '/', '2', '0', '9', '9', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '1', '4', '1', '4', '4', '8', '1', '/', '8', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '4', '4', '2', '2', '6', '6', '4', '7', '/', '2', '5', '1', '9', '4', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0447212Acc00600 : List (String × SourceJson) := (fragment0447212Field005Key00, fragment0447212Field005Value00) :: fragment0447212Acc00500
noncomputable def fragment0447212Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '1', '6', '8', '2', '9', '9', '1', '6', '9', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '6', '7', '7', '6', '4', '1', '8', '2', '1', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '5', '8', '9', '4', '7', '7', '/', '1', '6', '1', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '9', '3', '0', '4', '0', '8', '0', '1', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '4', '6', '0', '2', '5', '3', '/', '2', '4', '7', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '1', '0', '3', '6', '1', '5', '7', '7', '/', '8', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '9', '8', '4', '5', '5', '6', '8', '9', '/', '2', '5', '1', '9', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '3', '7', '8', '6', '7', '/', '2', '0', '9', '9', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '1', '4', '1', '4', '4', '8', '1', '/', '8', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '4', '4', '2', '2', '6', '6', '4', '7', '/', '2', '5', '1', '9', '4', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0447212_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 176) (SourceJson.white (fragment0447212Field005Chars00 ++ tail)) fragment0447212Acc00500 =
      SourceJson.object (fuel + 175) (SourceJson.white tail) fragment0447212Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0447212_object_field_005"
  err.flush

noncomputable def fragment0447212Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0447212Field006Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '5', '5', '4', '9', '8', '1', '4', '3', '2', '9', '3', '3', '8', '4', '4', '6', '0', '1', '2', '2', '9', '0', '9', '0', '6', '1', '2', '6', '0', '7', '1', '4', '4', '7', '9', '6', '0', '5', '7', '6', '0', '0', '0', '/', '9', '6', '4', '0', '7', '4', '8', '1', '8', '9', '3', '0', '8', '9', '6', '7', '2', '4', '3', '0', '7', '9', '3', '0', '5', '8', '6', '9', '3', '6', '8', '8', '7', '3', '7', '9', '9', '3', '0', '2', '7', '8', '8', '0', '1', '0', '1', '1', '7', '1', '1', '2', '2', '7', '1', '4', '9', '6', '7', '0', '9', '7'])
noncomputable def fragment0447212Acc00700 : List (String × SourceJson) := (fragment0447212Field006Key00, fragment0447212Field006Value00) :: fragment0447212Acc00600
noncomputable def fragment0447212Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '5', '5', '4', '9', '8', '1', '4', '3', '2', '9', '3', '3', '8', '4', '4', '6', '0', '1', '2', '2', '9', '0', '9', '0', '6', '1', '2', '6', '0', '7', '1', '4', '4', '7', '9', '6', '0', '5', '7', '6', '0', '0', '0', '/', '9', '6', '4', '0', '7', '4', '8', '1', '8', '9', '3', '0', '8', '9', '6', '7', '2', '4', '3', '0', '7', '9', '3', '0', '5', '8', '6', '9', '3', '6', '8', '8', '7', '3', '7', '9', '9', '3', '0', '2', '7', '8', '8', '0', '1', '0', '1', '1', '7', '1', '1', '2', '2', '7', '1', '4', '9', '6', '7', '0', '9', '7', '"', ',']

theorem object_fragment0447212_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 175) (SourceJson.white (fragment0447212Field006Chars00 ++ tail)) fragment0447212Acc00600 =
      SourceJson.object (fuel + 174) (SourceJson.white tail) fragment0447212Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0447212_object_field_006"
  err.flush

noncomputable def fragment0447212Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0447212Field007Value00 : SourceJson := .str (String.ofList ['1', '2', '6', '0', '5', '7', '5', '6', '9', '1', '8', '6', '3', '6', '4', '9', '8', '6', '0', '3', '0', '4', '3', '2', '6', '7', '9', '0', '2', '4', '1', '1', '7', '1', '9', '9', '4', '7', '8', '3', '4', '8', '2', '2', '0', '4', '0', '8', '9', '4', '9', '4', '3', '2', '9', '6', '3', '6', '3', '6', '3', '3', '2', '6', '5', '0', '9', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '1', '2', '3', '1', '0', '7', '8', '2', '0', '9', '5', '0', '7', '9', '7', '8', '1', '4', '6', '0', '4', '2', '0', '4', '4', '4', '2', '5', '7', '1', '2', '0', '7', '7', '9', '7', '8', '6', '8', '7', '9', '7', '3', '3', '9', '6', '1', '9', '3', '8', '6', '7', '5', '4', '8', '2', '8', '1', '6', '9', '1', '2', '9', '2', '1', '3', '1', '0', '7', '7', '2', '8', '9', '8', '7', '2', '0', '2', '0', '9', '7', '6', '0', '4', '8', '5', '8', '7', '7', '9'])
noncomputable def fragment0447212Acc00800 : List (String × SourceJson) := (fragment0447212Field007Key00, fragment0447212Field007Value00) :: fragment0447212Acc00700
noncomputable def fragment0447212Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '6', '0', '5', '7', '5', '6', '9', '1', '8', '6', '3', '6', '4', '9', '8', '6', '0', '3', '0', '4', '3', '2', '6', '7', '9', '0', '2', '4', '1', '1', '7', '1', '9', '9', '4', '7', '8', '3', '4', '8', '2', '2', '0', '4', '0', '8', '9', '4', '9', '4', '3', '2', '9', '6', '3', '6', '3', '6', '3', '3', '2', '6', '5', '0', '9', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '1', '2', '3', '1', '0', '7', '8', '2', '0', '9', '5', '0', '7', '9', '7', '8', '1', '4', '6', '0', '4', '2', '0', '4', '4', '4', '2', '5', '7', '1', '2', '0', '7', '7', '9', '7', '8', '6', '8', '7', '9', '7', '3', '3', '9', '6', '1', '9', '3', '8', '6', '7', '5', '4', '8', '2', '8', '1', '6', '9', '1', '2', '9', '2', '1', '3', '1', '0', '7', '7', '2', '8', '9', '8', '7', '2', '0', '2', '0', '9', '7', '6', '0', '4', '8', '5', '8', '7', '7', '9', '"', ',']

theorem object_fragment0447212_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 174) (SourceJson.white (fragment0447212Field007Chars00 ++ tail)) fragment0447212Acc00700 =
      SourceJson.object (fuel + 173) (SourceJson.white tail) fragment0447212Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0447212_object_field_007"
  err.flush

noncomputable def fragment0447212Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0447212Field008Value00 : SourceJson := .str (String.ofList ['1', '1', '7', '8', '1', '8', '5', '4', '3', '2', '9', '7', '6', '3', '0'])
noncomputable def fragment0447212Acc00900 : List (String × SourceJson) := (fragment0447212Field008Key00, fragment0447212Field008Value00) :: fragment0447212Acc00800
noncomputable def fragment0447212Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '7', '8', '1', '8', '5', '4', '3', '2', '9', '7', '6', '3', '0', '"', ',']

theorem object_fragment0447212_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 173) (SourceJson.white (fragment0447212Field008Chars00 ++ tail)) fragment0447212Acc00800 =
      SourceJson.object (fuel + 172) (SourceJson.white tail) fragment0447212Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0447212_object_field_008"
  err.flush

noncomputable def fragment0447212Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0447212Field009Value00 : SourceJson := .str (String.ofList ['9', '8', '6', '5', '8', '5', '3', '2', '0', '8', '6', '1', '7', '1', '1'])
noncomputable def fragment0447212Acc01000 : List (String × SourceJson) := (fragment0447212Field009Key00, fragment0447212Field009Value00) :: fragment0447212Acc00900
noncomputable def fragment0447212Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '8', '6', '5', '8', '5', '3', '2', '0', '8', '6', '1', '7', '1', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0447212_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 172) (SourceJson.white (fragment0447212Field009Chars00 ++ tail)) fragment0447212Acc00900 =
      .ok (.obj (fragment0447212Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0447212_object_field_009"
  err.flush

noncomputable def fragment0447212Chars : List Char := '{' :: (fragment0447212Field000Chars00 ++ fragment0447212Field001Chars00 ++ fragment0447212Field002Chars00 ++ fragment0447212Field003Chars00 ++ fragment0447212Field004Chars00 ++ fragment0447212Field005Chars00 ++ fragment0447212Field006Chars00 ++ fragment0447212Field007Chars00 ++ fragment0447212Field008Chars00 ++ fragment0447212Field009Chars00)
noncomputable def fragment0447212Value : SourceJson := .obj (fragment0447212Acc01000.reverse)

theorem value_fragment0447212 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 182) (fragment0447212Chars ++ tail) =
      .ok (fragment0447212Value, tail) := by
  have hinput : fragment0447212Chars ++ tail = '{' :: (fragment0447212Field000Chars00 ++ (fragment0447212Field001Chars00 ++ (fragment0447212Field002Chars00 ++ (fragment0447212Field003Chars00 ++ (fragment0447212Field004Chars00 ++ (fragment0447212Field005Chars00 ++ (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0447212Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 182) (fragment0447212Chars ++ tail) =
        SourceJson.value (fuel + 182) ('{' :: (fragment0447212Field000Chars00 ++ (fragment0447212Field001Chars00 ++ (fragment0447212Field002Chars00 ++ (fragment0447212Field003Chars00 ++ (fragment0447212Field004Chars00 ++ (fragment0447212Field005Chars00 ++ (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 182)) hinput
    _ = SourceJson.object (fuel + 181) (SourceJson.white (fragment0447212Field000Chars00 ++ (fragment0447212Field001Chars00 ++ (fragment0447212Field002Chars00 ++ (fragment0447212Field003Chars00 ++ (fragment0447212Field004Chars00 ++ (fragment0447212Field005Chars00 ++ (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail)))))))))))) fragment0447212Acc00000 := by rfl
    _ = SourceJson.object (fuel + 180) (SourceJson.white (fragment0447212Field001Chars00 ++ (fragment0447212Field002Chars00 ++ (fragment0447212Field003Chars00 ++ (fragment0447212Field004Chars00 ++ (fragment0447212Field005Chars00 ++ (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail))))))))))) fragment0447212Acc00100 := object_fragment0447212_field_000 fuel (fragment0447212Field001Chars00 ++ (fragment0447212Field002Chars00 ++ (fragment0447212Field003Chars00 ++ (fragment0447212Field004Chars00 ++ (fragment0447212Field005Chars00 ++ (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 179) (SourceJson.white (fragment0447212Field002Chars00 ++ (fragment0447212Field003Chars00 ++ (fragment0447212Field004Chars00 ++ (fragment0447212Field005Chars00 ++ (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail)))))))))) fragment0447212Acc00200 := object_fragment0447212_field_001 fuel (fragment0447212Field002Chars00 ++ (fragment0447212Field003Chars00 ++ (fragment0447212Field004Chars00 ++ (fragment0447212Field005Chars00 ++ (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 178) (SourceJson.white (fragment0447212Field003Chars00 ++ (fragment0447212Field004Chars00 ++ (fragment0447212Field005Chars00 ++ (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail))))))))) fragment0447212Acc00300 := object_fragment0447212_field_002 fuel (fragment0447212Field003Chars00 ++ (fragment0447212Field004Chars00 ++ (fragment0447212Field005Chars00 ++ (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 177) (SourceJson.white (fragment0447212Field004Chars00 ++ (fragment0447212Field005Chars00 ++ (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail)))))))) fragment0447212Acc00400 := object_fragment0447212_field_003 fuel (fragment0447212Field004Chars00 ++ (fragment0447212Field005Chars00 ++ (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 176) (SourceJson.white (fragment0447212Field005Chars00 ++ (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail))))))) fragment0447212Acc00500 := object_fragment0447212_field_004 fuel (fragment0447212Field005Chars00 ++ (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 175) (SourceJson.white (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail)))))) fragment0447212Acc00600 := object_fragment0447212_field_005 fuel (fragment0447212Field006Chars00 ++ (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 174) (SourceJson.white (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail))))) fragment0447212Acc00700 := object_fragment0447212_field_006 fuel (fragment0447212Field007Chars00 ++ (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 173) (SourceJson.white (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail)))) fragment0447212Acc00800 := object_fragment0447212_field_007 fuel (fragment0447212Field008Chars00 ++ (fragment0447212Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 172) (SourceJson.white (fragment0447212Field009Chars00 ++ (tail))) fragment0447212Acc00900 := object_fragment0447212_field_008 fuel (fragment0447212Field009Chars00 ++ (tail))
    _ = .ok (fragment0447212Value, tail) := object_fragment0447212_field_009 fuel (tail)

noncomputable def fragment0448680Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0448680Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0448680Field000Value00 : SourceJson := .number (String.ofList ['1', '3', '1'])
noncomputable def fragment0448680Acc00100 : List (String × SourceJson) := (fragment0448680Field000Key00, fragment0448680Field000Value00) :: fragment0448680Acc00000
noncomputable def fragment0448680Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '1', ',']

theorem object_fragment0448680_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 191) (SourceJson.white (fragment0448680Field000Chars00 ++ tail)) fragment0448680Acc00000 =
      SourceJson.object (fuel + 190) (SourceJson.white tail) fragment0448680Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0448680_object_field_000"
  err.flush

noncomputable def fragment0448680Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0448680Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0448680Acc00200 : List (String × SourceJson) := (fragment0448680Field001Key00, fragment0448680Field001Value00) :: fragment0448680Acc00100
noncomputable def fragment0448680Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0448680_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 190) (SourceJson.white (fragment0448680Field001Chars00 ++ tail)) fragment0448680Acc00100 =
      SourceJson.object (fuel + 189) (SourceJson.white tail) fragment0448680Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0448680_object_field_001"
  err.flush

noncomputable def fragment0448680Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0448680Field002Value00 : SourceJson := .str (String.ofList ['9', '8', '1', '7', '8', '6', '0', '3', '4', '2', '0', '4', '2', '6', '4', '4', '8', '4', '2', '0', '6', '4', '2', '7', '5', '7', '7', '0', '0', '1', '0', '4', '3', '/', '1', '4', '2', '8', '8', '4', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0448680Acc00300 : List (String × SourceJson) := (fragment0448680Field002Key00, fragment0448680Field002Value00) :: fragment0448680Acc00200
noncomputable def fragment0448680Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '8', '1', '7', '8', '6', '0', '3', '4', '2', '0', '4', '2', '6', '4', '4', '8', '4', '2', '0', '6', '4', '2', '7', '5', '7', '7', '0', '0', '1', '0', '4', '3', '/', '1', '4', '2', '8', '8', '4', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0448680_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 189) (SourceJson.white (fragment0448680Field002Chars00 ++ tail)) fragment0448680Acc00200 =
      SourceJson.object (fuel + 188) (SourceJson.white tail) fragment0448680Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0448680_object_field_002"
  err.flush

noncomputable def fragment0448680Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0448680Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0448680Acc00400 : List (String × SourceJson) := (fragment0448680Field003Key00, fragment0448680Field003Value00) :: fragment0448680Acc00300
noncomputable def fragment0448680Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0448680_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 188) (SourceJson.white (fragment0448680Field003Chars00 ++ tail)) fragment0448680Acc00300 =
      SourceJson.object (fuel + 187) (SourceJson.white tail) fragment0448680Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0448680_object_field_003"
  err.flush

noncomputable def fragment0448680Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0448680Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '1', '5', '6', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0448680Acc00500 : List (String × SourceJson) := (fragment0448680Field004Key00, fragment0448680Field004Value00) :: fragment0448680Acc00400
noncomputable def fragment0448680Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '5', '6', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0448680_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 187) (SourceJson.white (fragment0448680Field004Chars00 ++ tail)) fragment0448680Acc00400 =
      SourceJson.object (fuel + 186) (SourceJson.white tail) fragment0448680Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0448680_object_field_004"
  err.flush

noncomputable def fragment0448680Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0448680Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '9', '9', '1', '6', '7', '9', '9', '7', '2', '3', '/', '1', '0', '0', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '9', '3', '5', '4', '8', '5', '0', '2', '7', '/', '1', '0', '0', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '6', '0', '1', '7', '6', '6', '3', '1', '/', '7', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '4', '4', '6', '4', '4', '8', '2', '8', '7', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '9', '4', '5', '7', '7', '8', '5', '3', '/', '5', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '4', '4', '0', '3', '7', '9', '2', '0', '1', '/', '1', '0', '0', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '4', '4', '0', '0', '1', '3', '1', '/', '1', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '8', '0', '5', '3', '9', '2', '6', '7', '/', '2', '0', '1', '5', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '0', '9', '6', '1', '7', '6', '4', '7', '/', '3', '3', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '8', '2', '8', '7', '8', '5', '7', '5', '7', '/', '1', '0', '0', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0448680Acc00600 : List (String × SourceJson) := (fragment0448680Field005Key00, fragment0448680Field005Value00) :: fragment0448680Acc00500
noncomputable def fragment0448680Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '9', '1', '6', '7', '9', '9', '7', '2', '3', '/', '1', '0', '0', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '3', '5', '4', '8', '5', '0', '2', '7', '/', '1', '0', '0', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '6', '0', '1', '7', '6', '6', '3', '1', '/', '7', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '4', '4', '6', '4', '4', '8', '2', '8', '7', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '9', '4', '5', '7', '7', '8', '5', '3', '/', '5', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '4', '4', '0', '3', '7', '9', '2', '0', '1', '/', '1', '0', '0', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '4', '4', '0', '0', '1', '3', '1', '/', '1', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '8', '0', '5', '3', '9', '2', '6', '7', '/', '2', '0', '1', '5', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '0', '9', '6', '1', '7', '6', '4', '7', '/', '3', '3', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '8', '2', '8', '7', '8', '5', '7', '5', '7', '/', '1', '0', '0', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0448680_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 186) (SourceJson.white (fragment0448680Field005Chars00 ++ tail)) fragment0448680Acc00500 =
      SourceJson.object (fuel + 185) (SourceJson.white tail) fragment0448680Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0448680_object_field_005"
  err.flush

noncomputable def fragment0448680Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0448680Field006Value00 : SourceJson := .str (String.ofList ['3', '9', '9', '9', '2', '9', '3', '0', '8', '8', '3', '9', '7', '9', '5', '9', '0', '8', '6', '8', '3', '5', '7', '5', '4', '2', '9', '6', '5', '8', '6', '6', '6', '3', '5', '3', '6', '7', '5', '3', '7', '9', '9', '2', '9', '6', '0', '0', '0', '/', '1', '1', '9', '5', '6', '0', '9', '2', '5', '5', '7', '2', '0', '5', '8', '0', '2', '4', '4', '7', '3', '6', '0', '0', '7', '7', '3', '0', '1', '5', '4', '2', '7', '1', '9', '2', '4', '4', '7', '2', '6', '5', '7', '4', '6', '8', '5', '7', '1', '5', '9', '2', '3', '5', '9', '4', '7', '9', '5', '3', '3', '3', '2', '9', '9'])
noncomputable def fragment0448680Acc00700 : List (String × SourceJson) := (fragment0448680Field006Key00, fragment0448680Field006Value00) :: fragment0448680Acc00600
noncomputable def fragment0448680Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '9', '9', '9', '2', '9', '3', '0', '8', '8', '3', '9', '7', '9', '5', '9', '0', '8', '6', '8', '3', '5', '7', '5', '4', '2', '9', '6', '5', '8', '6', '6', '6', '3', '5', '3', '6', '7', '5', '3', '7', '9', '9', '2', '9', '6', '0', '0', '0', '/', '1', '1', '9', '5', '6', '0', '9', '2', '5', '5', '7', '2', '0', '5', '8', '0', '2', '4', '4', '7', '3', '6', '0', '0', '7', '7', '3', '0', '1', '5', '4', '2', '7', '1', '9', '2', '4', '4', '7', '2', '6', '5', '7', '4', '6', '8', '5', '7', '1', '5', '9', '2', '3', '5', '9', '4', '7', '9', '5', '3', '3', '3', '2', '9', '9', '"', ',']

theorem object_fragment0448680_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 185) (SourceJson.white (fragment0448680Field006Chars00 ++ tail)) fragment0448680Acc00600 =
      SourceJson.object (fuel + 184) (SourceJson.white tail) fragment0448680Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0448680_object_field_006"
  err.flush

noncomputable def fragment0448680Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0448680Field007Value00 : SourceJson := .str (String.ofList ['2', '5', '6', '7', '7', '4', '5', '4', '5', '0', '9', '8', '4', '6', '2', '9', '2', '5', '5', '1', '1', '9', '2', '9', '2', '0', '4', '1', '4', '3', '5', '3', '8', '5', '7', '8', '5', '7', '4', '8', '4', '9', '5', '6', '9', '8', '2', '7', '0', '1', '0', '4', '9', '2', '7', '9', '3', '8', '1', '2', '7', '3', '6', '9', '3', '3', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '8', '2', '1', '1', '0', '1', '0', '6', '2', '7', '0', '3', '0', '2', '0', '1', '9', '2', '6', '6', '0', '7', '6', '7', '9', '0', '2', '7', '2', '0', '5', '9', '8', '9', '9', '7', '7', '0', '8', '2', '8', '5', '3', '4', '7', '1', '6', '7', '6', '1', '6', '6', '8', '3', '3', '8', '3', '5', '5', '2', '6', '8', '6', '8', '4', '1', '6', '2', '1', '5', '4', '2', '7', '9', '5', '7', '7', '9', '7', '5', '2', '4', '4', '2', '4', '5', '9', '3', '6', '9', '4', '6', '3', '7', '4', '1'])
noncomputable def fragment0448680Acc00800 : List (String × SourceJson) := (fragment0448680Field007Key00, fragment0448680Field007Value00) :: fragment0448680Acc00700
noncomputable def fragment0448680Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '5', '6', '7', '7', '4', '5', '4', '5', '0', '9', '8', '4', '6', '2', '9', '2', '5', '5', '1', '1', '9', '2', '9', '2', '0', '4', '1', '4', '3', '5', '3', '8', '5', '7', '8', '5', '7', '4', '8', '4', '9', '5', '6', '9', '8', '2', '7', '0', '1', '0', '4', '9', '2', '7', '9', '3', '8', '1', '2', '7', '3', '6', '9', '3', '3', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '8', '2', '1', '1', '0', '1', '0', '6', '2', '7', '0', '3', '0', '2', '0', '1', '9', '2', '6', '6', '0', '7', '6', '7', '9', '0', '2', '7', '2', '0', '5', '9', '8', '9', '9', '7', '7', '0', '8', '2', '8', '5', '3', '4', '7', '1', '6', '7', '6', '1', '6', '6', '8', '3', '3', '8', '3', '5', '5', '2', '6', '8', '6', '8', '4', '1', '6', '2', '1', '5', '4', '2', '7', '9', '5', '7', '7', '9', '7', '5', '2', '4', '4', '2', '4', '5', '9', '3', '6', '9', '4', '6', '3', '7', '4', '1', '"', ',']

theorem object_fragment0448680_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 184) (SourceJson.white (fragment0448680Field007Chars00 ++ tail)) fragment0448680Acc00700 =
      SourceJson.object (fuel + 183) (SourceJson.white tail) fragment0448680Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0448680_object_field_007"
  err.flush

noncomputable def fragment0448680Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0448680Field008Value00 : SourceJson := .str (String.ofList ['2', '6', '5', '0', '1', '6', '8', '8', '6', '7', '7', '4', '4', '3'])
noncomputable def fragment0448680Acc00900 : List (String × SourceJson) := (fragment0448680Field008Key00, fragment0448680Field008Value00) :: fragment0448680Acc00800
noncomputable def fragment0448680Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '6', '5', '0', '1', '6', '8', '8', '6', '7', '7', '4', '4', '3', '"', ',']

theorem object_fragment0448680_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 183) (SourceJson.white (fragment0448680Field008Chars00 ++ tail)) fragment0448680Acc00800 =
      SourceJson.object (fuel + 182) (SourceJson.white tail) fragment0448680Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0448680_object_field_008"
  err.flush

noncomputable def fragment0448680Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0448680Field009Value00 : SourceJson := .str (String.ofList ['2', '0', '7', '1', '4', '3', '5', '2', '9', '6', '1', '7', '5', '2', '5'])
noncomputable def fragment0448680Acc01000 : List (String × SourceJson) := (fragment0448680Field009Key00, fragment0448680Field009Value00) :: fragment0448680Acc00900
noncomputable def fragment0448680Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '7', '1', '4', '3', '5', '2', '9', '6', '1', '7', '5', '2', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0448680_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 182) (SourceJson.white (fragment0448680Field009Chars00 ++ tail)) fragment0448680Acc00900 =
      .ok (.obj (fragment0448680Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0448680_object_field_009"
  err.flush

noncomputable def fragment0448680Chars : List Char := '{' :: (fragment0448680Field000Chars00 ++ fragment0448680Field001Chars00 ++ fragment0448680Field002Chars00 ++ fragment0448680Field003Chars00 ++ fragment0448680Field004Chars00 ++ fragment0448680Field005Chars00 ++ fragment0448680Field006Chars00 ++ fragment0448680Field007Chars00 ++ fragment0448680Field008Chars00 ++ fragment0448680Field009Chars00)
noncomputable def fragment0448680Value : SourceJson := .obj (fragment0448680Acc01000.reverse)

theorem value_fragment0448680 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 192) (fragment0448680Chars ++ tail) =
      .ok (fragment0448680Value, tail) := by
  have hinput : fragment0448680Chars ++ tail = '{' :: (fragment0448680Field000Chars00 ++ (fragment0448680Field001Chars00 ++ (fragment0448680Field002Chars00 ++ (fragment0448680Field003Chars00 ++ (fragment0448680Field004Chars00 ++ (fragment0448680Field005Chars00 ++ (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0448680Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 192) (fragment0448680Chars ++ tail) =
        SourceJson.value (fuel + 192) ('{' :: (fragment0448680Field000Chars00 ++ (fragment0448680Field001Chars00 ++ (fragment0448680Field002Chars00 ++ (fragment0448680Field003Chars00 ++ (fragment0448680Field004Chars00 ++ (fragment0448680Field005Chars00 ++ (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 192)) hinput
    _ = SourceJson.object (fuel + 191) (SourceJson.white (fragment0448680Field000Chars00 ++ (fragment0448680Field001Chars00 ++ (fragment0448680Field002Chars00 ++ (fragment0448680Field003Chars00 ++ (fragment0448680Field004Chars00 ++ (fragment0448680Field005Chars00 ++ (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail)))))))))))) fragment0448680Acc00000 := by rfl
    _ = SourceJson.object (fuel + 190) (SourceJson.white (fragment0448680Field001Chars00 ++ (fragment0448680Field002Chars00 ++ (fragment0448680Field003Chars00 ++ (fragment0448680Field004Chars00 ++ (fragment0448680Field005Chars00 ++ (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail))))))))))) fragment0448680Acc00100 := object_fragment0448680_field_000 fuel (fragment0448680Field001Chars00 ++ (fragment0448680Field002Chars00 ++ (fragment0448680Field003Chars00 ++ (fragment0448680Field004Chars00 ++ (fragment0448680Field005Chars00 ++ (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 189) (SourceJson.white (fragment0448680Field002Chars00 ++ (fragment0448680Field003Chars00 ++ (fragment0448680Field004Chars00 ++ (fragment0448680Field005Chars00 ++ (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail)))))))))) fragment0448680Acc00200 := object_fragment0448680_field_001 fuel (fragment0448680Field002Chars00 ++ (fragment0448680Field003Chars00 ++ (fragment0448680Field004Chars00 ++ (fragment0448680Field005Chars00 ++ (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 188) (SourceJson.white (fragment0448680Field003Chars00 ++ (fragment0448680Field004Chars00 ++ (fragment0448680Field005Chars00 ++ (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail))))))))) fragment0448680Acc00300 := object_fragment0448680_field_002 fuel (fragment0448680Field003Chars00 ++ (fragment0448680Field004Chars00 ++ (fragment0448680Field005Chars00 ++ (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 187) (SourceJson.white (fragment0448680Field004Chars00 ++ (fragment0448680Field005Chars00 ++ (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail)))))))) fragment0448680Acc00400 := object_fragment0448680_field_003 fuel (fragment0448680Field004Chars00 ++ (fragment0448680Field005Chars00 ++ (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 186) (SourceJson.white (fragment0448680Field005Chars00 ++ (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail))))))) fragment0448680Acc00500 := object_fragment0448680_field_004 fuel (fragment0448680Field005Chars00 ++ (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 185) (SourceJson.white (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail)))))) fragment0448680Acc00600 := object_fragment0448680_field_005 fuel (fragment0448680Field006Chars00 ++ (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 184) (SourceJson.white (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail))))) fragment0448680Acc00700 := object_fragment0448680_field_006 fuel (fragment0448680Field007Chars00 ++ (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 183) (SourceJson.white (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail)))) fragment0448680Acc00800 := object_fragment0448680_field_007 fuel (fragment0448680Field008Chars00 ++ (fragment0448680Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 182) (SourceJson.white (fragment0448680Field009Chars00 ++ (tail))) fragment0448680Acc00900 := object_fragment0448680_field_008 fuel (fragment0448680Field009Chars00 ++ (tail))
    _ = .ok (fragment0448680Value, tail) := object_fragment0448680_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0130_before_reader"
  err.flush

noncomputable def chunk0130LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0130SuffixChars00 : List Char := [',']
noncomputable def chunk0130Chars00 : List Char := chunk0130LeadChars00 ++ fragment0447212Chars ++ chunk0130SuffixChars00
noncomputable def chunk0130Push00 (acc : List SourceJson) : List SourceJson := fragment0447212Value :: acc

noncomputable def chunk0130AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0130_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 474)
      (SourceJson.white (chunk0130LeadChars00 ++ (fragment0447212Chars ++ rest))) acc =
      (SourceJson.value (fuel + 473) (fragment0447212Chars ++ rest)).bind
        (chunk0130AfterValue00 (fuel + 473) acc) := by rfl

theorem array_chunk0130 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 474) (SourceJson.white (chunk0130Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 473) (SourceJson.white tail) (chunk0130Push00 acc) := by
  have hinput : chunk0130Chars00 ++ tail = chunk0130LeadChars00 ++ (fragment0447212Chars ++ (chunk0130SuffixChars00 ++ tail)) := by
    simp only [chunk0130Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 474) (SourceJson.white (chunk0130Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 474)
          (SourceJson.white (chunk0130LeadChars00 ++ (fragment0447212Chars ++ (chunk0130SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 474) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 473) (fragment0447212Chars ++ (chunk0130SuffixChars00 ++ tail))).bind
        (chunk0130AfterValue00 (fuel + 473) acc) := array_chunk0130_head fuel (chunk0130SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0447212Value, chunk0130SuffixChars00 ++ tail)).bind
        (chunk0130AfterValue00 (fuel + 473) acc) :=
      congrArg (fun result => result.bind (chunk0130AfterValue00 (fuel + 473) acc))
        (value_fragment0447212 (fuel + 291) (chunk0130SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 473) (SourceJson.white tail) (chunk0130Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0130_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0131_before_reader"
  err.flush

noncomputable def chunk0131LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0131SuffixChars00 : List Char := [',']
noncomputable def chunk0131Chars00 : List Char := chunk0131LeadChars00 ++ fragment0448680Chars ++ chunk0131SuffixChars00
noncomputable def chunk0131Push00 (acc : List SourceJson) : List SourceJson := fragment0448680Value :: acc

noncomputable def chunk0131AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0131_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (chunk0131LeadChars00 ++ (fragment0448680Chars ++ rest))) acc =
      (SourceJson.value (fuel + 472) (fragment0448680Chars ++ rest)).bind
        (chunk0131AfterValue00 (fuel + 472) acc) := by rfl

theorem array_chunk0131 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 473) (SourceJson.white (chunk0131Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 472) (SourceJson.white tail) (chunk0131Push00 acc) := by
  have hinput : chunk0131Chars00 ++ tail = chunk0131LeadChars00 ++ (fragment0448680Chars ++ (chunk0131SuffixChars00 ++ tail)) := by
    simp only [chunk0131Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 473) (SourceJson.white (chunk0131Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 473)
          (SourceJson.white (chunk0131LeadChars00 ++ (fragment0448680Chars ++ (chunk0131SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 473) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 472) (fragment0448680Chars ++ (chunk0131SuffixChars00 ++ tail))).bind
        (chunk0131AfterValue00 (fuel + 472) acc) := array_chunk0131_head fuel (chunk0131SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0448680Value, chunk0131SuffixChars00 ++ tail)).bind
        (chunk0131AfterValue00 (fuel + 472) acc) :=
      congrArg (fun result => result.bind (chunk0131AfterValue00 (fuel + 472) acc))
        (value_fragment0448680 (fuel + 280) (chunk0131SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 472) (SourceJson.white tail) (chunk0131Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0131_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0130Chars00 ++ chunk0131Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0131Push00 (chunk0130Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 474) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 472) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0130Chars00 ++ (chunk0131Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 474) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 474) (SourceJson.white (chunk0130Chars00 ++ (chunk0131Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 474) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 473) (SourceJson.white (chunk0131Chars00 ++ (tail))) (chunk0130Push00 (acc)) := array_chunk0130 fuel (chunk0131Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 472) (SourceJson.white tail) (blockPush acc) := array_chunk0131 fuel (tail) (chunk0130Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 447206).take 2979 = blockChars := by rfl

theorem block_original_split : sourceRest 447206 = blockChars ++ sourceRest 450185 := by
  calc
    sourceRest 447206 = (sourceRest 447206).take 2979 ++ (sourceRest 447206).drop 2979 :=
      (List.take_append_drop 2979 (sourceRest 447206)).symm
    _ = blockChars ++ (sourceRest 447206).drop 2979 :=
      congrArg (fun part => part ++ (sourceRest 447206).drop 2979) block_original_prefix
    _ = blockChars ++ sourceRest 450185 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 447206 2979)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 474) (SourceJson.white (sourceRest 447206)) acc =
      SourceJson.array (fuel + 472) (SourceJson.white (sourceRest 450185)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 474) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 450185) acc)

#print axioms object_fragment0447212_field_000
#print axioms object_fragment0447212_field_001
#print axioms object_fragment0447212_field_002
#print axioms object_fragment0447212_field_003
#print axioms object_fragment0447212_field_004
#print axioms object_fragment0447212_field_005
#print axioms object_fragment0447212_field_006
#print axioms object_fragment0447212_field_007
#print axioms object_fragment0447212_field_008
#print axioms object_fragment0447212_field_009
#print axioms value_fragment0447212
#print axioms object_fragment0448680_field_000
#print axioms object_fragment0448680_field_001
#print axioms object_fragment0448680_field_002
#print axioms object_fragment0448680_field_003
#print axioms object_fragment0448680_field_004
#print axioms object_fragment0448680_field_005
#print axioms object_fragment0448680_field_006
#print axioms object_fragment0448680_field_007
#print axioms object_fragment0448680_field_008
#print axioms object_fragment0448680_field_009
#print axioms value_fragment0448680
#print axioms array_chunk0130_head
#print axioms array_chunk0130
#print axioms array_chunk0131_head
#print axioms array_chunk0131
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock066

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
