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

namespace SimplicesBlock010

noncomputable def fragment0260005Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0260005Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0260005Field000Value00 : SourceJson := .number (String.ofList ['2', '0'])
noncomputable def fragment0260005Acc00100 : List (String × SourceJson) := (fragment0260005Field000Key00, fragment0260005Field000Value00) :: fragment0260005Acc00000
noncomputable def fragment0260005Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '0', ',']

theorem object_fragment0260005_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0260005Field000Chars00 ++ tail)) fragment0260005Acc00000 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0260005Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0260005_object_field_000"
  err.flush

noncomputable def fragment0260005Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0260005Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0260005Acc00200 : List (String × SourceJson) := (fragment0260005Field001Key00, fragment0260005Field001Value00) :: fragment0260005Acc00100
noncomputable def fragment0260005Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0260005_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0260005Field001Chars00 ++ tail)) fragment0260005Acc00100 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0260005Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0260005_object_field_001"
  err.flush

noncomputable def fragment0260005Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0260005Field002Value00 : SourceJson := .str (String.ofList ['2', '6', '9', '2', '6', '6', '3', '8', '1', '2', '6', '5', '3', '0', '0', '7', '9', '5', '0', '7', '6', '7', '9', '1', '8', '1', '3', '1', '8', '2', '4', '2', '2', '9', '/', '1', '1', '5', '8', '6', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0260005Acc00300 : List (String × SourceJson) := (fragment0260005Field002Key00, fragment0260005Field002Value00) :: fragment0260005Acc00200
noncomputable def fragment0260005Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '6', '9', '2', '6', '6', '3', '8', '1', '2', '6', '5', '3', '0', '0', '7', '9', '5', '0', '7', '6', '7', '9', '1', '8', '1', '3', '1', '8', '2', '4', '2', '2', '9', '/', '1', '1', '5', '8', '6', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0260005_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0260005Field002Chars00 ++ tail)) fragment0260005Acc00200 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0260005Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0260005_object_field_002"
  err.flush

noncomputable def fragment0260005Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0260005Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0260005Acc00400 : List (String × SourceJson) := (fragment0260005Field003Key00, fragment0260005Field003Value00) :: fragment0260005Acc00300
noncomputable def fragment0260005Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0260005_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0260005Field003Chars00 ++ tail)) fragment0260005Acc00300 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0260005Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0260005_object_field_003"
  err.flush

noncomputable def fragment0260005Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0260005Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0260005Acc00500 : List (String × SourceJson) := (fragment0260005Field004Key00, fragment0260005Field004Value00) :: fragment0260005Acc00400
noncomputable def fragment0260005Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0260005_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0260005Field004Chars00 ++ tail)) fragment0260005Acc00400 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0260005Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0260005_object_field_004"
  err.flush

noncomputable def fragment0260005Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0260005Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '3', '2', '3', '1', '2', '9', '3', '6', '9', '3', '8', '3', '/', '1', '4', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '3', '8', '1', '4', '1', '5', '7', '3', '8', '6', '3', '/', '1', '4', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '4', '2', '4', '3', '3', '7', '5', '8', '0', '1', '/', '1', '7', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '6', '7', '9', '1', '5', '1', '3', '3', '1', '6', '9', '/', '1', '4', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '5', '6', '3', '0', '7', '9', '7', '7', '8', '9', '/', '2', '6', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '5', '9', '6', '8', '9', '3', '9', '3', '0', '7', '/', '2', '2', '2', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '1', '2', '8', '1', '4', '8', '0', '9', '8', '7', '/', '2', '2', '2', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '6', '0', '7', '4', '8', '8', '2', '1', '7', '1', '9', '/', '4', '4', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '6', '7', '5', '3', '6', '1', '6', '1', '1', '9', '/', '4', '4', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '6', '7', '4', '4', '7', '0', '5', '3', '9', '9', '/', '4', '4', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0260005Acc00600 : List (String × SourceJson) := (fragment0260005Field005Key00, fragment0260005Field005Value00) :: fragment0260005Acc00500
noncomputable def fragment0260005Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '3', '1', '2', '9', '3', '6', '9', '3', '8', '3', '/', '1', '4', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '8', '1', '4', '1', '5', '7', '3', '8', '6', '3', '/', '1', '4', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '4', '2', '4', '3', '3', '7', '5', '8', '0', '1', '/', '1', '7', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '6', '7', '9', '1', '5', '1', '3', '3', '1', '6', '9', '/', '1', '4', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '6', '3', '0', '7', '9', '7', '7', '8', '9', '/', '2', '6', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '5', '9', '6', '8', '9', '3', '9', '3', '0', '7', '/', '2', '2', '2', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '1', '2', '8', '1', '4', '8', '0', '9', '8', '7', '/', '2', '2', '2', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '0', '7', '4', '8', '8', '2', '1', '7', '1', '9', '/', '4', '4', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '6', '7', '5', '3', '6', '1', '6', '1', '1', '9', '/', '4', '4', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '6', '7', '4', '4', '7', '0', '5', '3', '9', '9', '/', '4', '4', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0260005_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0260005Field005Chars00 ++ tail)) fragment0260005Acc00500 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0260005Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0260005_object_field_005"
  err.flush

noncomputable def fragment0260005Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0260005Field006Value00 : SourceJson := .str (String.ofList ['4', '8', '5', '8', '5', '1', '1', '9', '8', '9', '3', '5', '6', '1', '7', '3', '8', '7', '5', '4', '8', '0', '0', '1', '9', '2', '3', '3', '0', '3', '4', '2', '4', '5', '3', '3', '2', '4', '9', '3', '5', '0', '0', '0', '0', '0', '0', '/', '3', '9', '7', '4', '3', '9', '6', '9', '3', '6', '0', '7', '6', '5', '9', '6', '3', '9', '0', '0', '2', '6', '3', '5', '7', '6', '2', '6', '0', '5', '4', '1', '9', '7', '3', '3', '5', '4', '1', '9', '4', '9', '5', '3', '7', '7', '0', '6', '6', '7', '4', '3', '3', '4', '3', '1', '1', '2', '4', '7', '4', '7'])
noncomputable def fragment0260005Acc00700 : List (String × SourceJson) := (fragment0260005Field006Key00, fragment0260005Field006Value00) :: fragment0260005Acc00600
noncomputable def fragment0260005Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '8', '5', '8', '5', '1', '1', '9', '8', '9', '3', '5', '6', '1', '7', '3', '8', '7', '5', '4', '8', '0', '0', '1', '9', '2', '3', '3', '0', '3', '4', '2', '4', '5', '3', '3', '2', '4', '9', '3', '5', '0', '0', '0', '0', '0', '0', '/', '3', '9', '7', '4', '3', '9', '6', '9', '3', '6', '0', '7', '6', '5', '9', '6', '3', '9', '0', '0', '2', '6', '3', '5', '7', '6', '2', '6', '0', '5', '4', '1', '9', '7', '3', '3', '5', '4', '1', '9', '4', '9', '5', '3', '7', '7', '0', '6', '6', '7', '4', '3', '3', '4', '3', '1', '1', '2', '4', '7', '4', '7', '"', ',']

theorem object_fragment0260005_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0260005Field006Chars00 ++ tail)) fragment0260005Acc00600 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0260005Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0260005_object_field_006"
  err.flush

noncomputable def fragment0260005Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0260005Field007Value00 : SourceJson := .str (String.ofList ['3', '3', '7', '0', '3', '2', '9', '3', '5', '4', '7', '9', '2', '5', '3', '5', '8', '0', '9', '8', '9', '7', '1', '3', '0', '6', '1', '1', '3', '3', '6', '8', '3', '3', '4', '5', '6', '4', '1', '2', '6', '7', '5', '6', '3', '9', '1', '8', '6', '0', '8', '3', '9', '4', '0', '6', '0', '3', '6', '3', '9', '2', '3', '5', '6', '8', '4', '3', '4', '2', '9', '4', '3', '6', '1', '6', '8', '6', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '8', '5', '3', '3', '1', '1', '7', '1', '7', '0', '9', '4', '4', '8', '2', '8', '2', '8', '1', '4', '9', '5', '4', '4', '5', '6', '0', '2', '0', '6', '4', '3', '8', '9', '8', '1', '6', '0', '8', '5', '4', '4', '9', '4', '4', '8', '6', '8', '4', '0', '9', '6', '5', '5', '7', '9', '9', '8', '7', '4', '1', '9', '3', '6', '8', '5', '5', '9', '2', '6', '5', '0', '3', '6', '2', '7', '8', '9', '3', '1', '2', '1', '0', '4', '6', '6', '8', '2', '9', '1', '2', '9', '2', '4', '2', '4', '5', '9', '3', '1', '3', '4', '9', '9', '8', '5', '0', '8', '2', '2', '2', '8', '4', '8', '2', '5', '3', '9'])
noncomputable def fragment0260005Acc00800 : List (String × SourceJson) := (fragment0260005Field007Key00, fragment0260005Field007Value00) :: fragment0260005Acc00700
noncomputable def fragment0260005Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '3', '7', '0', '3', '2', '9', '3', '5', '4', '7', '9', '2', '5', '3', '5', '8', '0', '9', '8', '9', '7', '1', '3', '0', '6', '1', '1', '3', '3', '6', '8', '3', '3', '4', '5', '6', '4', '1', '2', '6', '7', '5', '6', '3', '9', '1', '8', '6', '0', '8', '3', '9', '4', '0', '6', '0', '3', '6', '3', '9', '2', '3', '5', '6', '8', '4', '3', '4', '2', '9', '4', '3', '6', '1', '6', '8', '6', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '8', '5', '3', '3', '1', '1', '7', '1', '7', '0', '9', '4', '4', '8', '2', '8', '2', '8', '1', '4', '9', '5', '4', '4', '5', '6', '0', '2', '0', '6', '4', '3', '8', '9', '8', '1', '6', '0', '8', '5', '4', '4', '9', '4', '4', '8', '6', '8', '4', '0', '9', '6', '5', '5', '7', '9', '9', '8', '7', '4', '1', '9', '3', '6', '8', '5', '5', '9', '2', '6', '5', '0', '3', '6', '2', '7', '8', '9', '3', '1', '2', '1', '0', '4', '6', '6', '8', '2', '9', '1', '2', '9', '2', '4', '2', '4', '5', '9', '3', '1', '3', '4', '9', '9', '8', '5', '0', '8', '2', '2', '2', '8', '4', '8', '2', '5', '3', '9', '"', ',']

theorem object_fragment0260005_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0260005Field007Chars00 ++ tail)) fragment0260005Acc00700 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0260005Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0260005_object_field_007"
  err.flush

noncomputable def fragment0260005Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0260005Field008Value00 : SourceJson := .str (String.ofList ['9', '6', '8', '5', '2', '6', '7', '5', '6', '7', '9', '1', '9', '4'])
noncomputable def fragment0260005Acc00900 : List (String × SourceJson) := (fragment0260005Field008Key00, fragment0260005Field008Value00) :: fragment0260005Acc00800
noncomputable def fragment0260005Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '6', '8', '5', '2', '6', '7', '5', '6', '7', '9', '1', '9', '4', '"', ',']

theorem object_fragment0260005_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0260005Field008Chars00 ++ tail)) fragment0260005Acc00800 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0260005Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0260005_object_field_008"
  err.flush

noncomputable def fragment0260005Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0260005Field009Value00 : SourceJson := .str (String.ofList ['7', '0', '5', '4', '2', '0', '4', '4', '9', '9', '8', '2', '7', '4', '4'])
noncomputable def fragment0260005Acc01000 : List (String × SourceJson) := (fragment0260005Field009Key00, fragment0260005Field009Value00) :: fragment0260005Acc00900
noncomputable def fragment0260005Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '0', '5', '4', '2', '0', '4', '4', '9', '9', '8', '2', '7', '4', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0260005_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0260005Field009Chars00 ++ tail)) fragment0260005Acc00900 =
      .ok (.obj (fragment0260005Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0260005_object_field_009"
  err.flush

noncomputable def fragment0260005Chars : List Char := '{' :: (fragment0260005Field000Chars00 ++ fragment0260005Field001Chars00 ++ fragment0260005Field002Chars00 ++ fragment0260005Field003Chars00 ++ fragment0260005Field004Chars00 ++ fragment0260005Field005Chars00 ++ fragment0260005Field006Chars00 ++ fragment0260005Field007Chars00 ++ fragment0260005Field008Chars00 ++ fragment0260005Field009Chars00)
noncomputable def fragment0260005Value : SourceJson := .obj (fragment0260005Acc01000.reverse)

theorem value_fragment0260005 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 238) (fragment0260005Chars ++ tail) =
      .ok (fragment0260005Value, tail) := by
  have hinput : fragment0260005Chars ++ tail = '{' :: (fragment0260005Field000Chars00 ++ (fragment0260005Field001Chars00 ++ (fragment0260005Field002Chars00 ++ (fragment0260005Field003Chars00 ++ (fragment0260005Field004Chars00 ++ (fragment0260005Field005Chars00 ++ (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0260005Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 238) (fragment0260005Chars ++ tail) =
        SourceJson.value (fuel + 238) ('{' :: (fragment0260005Field000Chars00 ++ (fragment0260005Field001Chars00 ++ (fragment0260005Field002Chars00 ++ (fragment0260005Field003Chars00 ++ (fragment0260005Field004Chars00 ++ (fragment0260005Field005Chars00 ++ (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 238)) hinput
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0260005Field000Chars00 ++ (fragment0260005Field001Chars00 ++ (fragment0260005Field002Chars00 ++ (fragment0260005Field003Chars00 ++ (fragment0260005Field004Chars00 ++ (fragment0260005Field005Chars00 ++ (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail)))))))))))) fragment0260005Acc00000 := by rfl
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0260005Field001Chars00 ++ (fragment0260005Field002Chars00 ++ (fragment0260005Field003Chars00 ++ (fragment0260005Field004Chars00 ++ (fragment0260005Field005Chars00 ++ (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail))))))))))) fragment0260005Acc00100 := object_fragment0260005_field_000 fuel (fragment0260005Field001Chars00 ++ (fragment0260005Field002Chars00 ++ (fragment0260005Field003Chars00 ++ (fragment0260005Field004Chars00 ++ (fragment0260005Field005Chars00 ++ (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0260005Field002Chars00 ++ (fragment0260005Field003Chars00 ++ (fragment0260005Field004Chars00 ++ (fragment0260005Field005Chars00 ++ (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail)))))))))) fragment0260005Acc00200 := object_fragment0260005_field_001 fuel (fragment0260005Field002Chars00 ++ (fragment0260005Field003Chars00 ++ (fragment0260005Field004Chars00 ++ (fragment0260005Field005Chars00 ++ (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0260005Field003Chars00 ++ (fragment0260005Field004Chars00 ++ (fragment0260005Field005Chars00 ++ (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail))))))))) fragment0260005Acc00300 := object_fragment0260005_field_002 fuel (fragment0260005Field003Chars00 ++ (fragment0260005Field004Chars00 ++ (fragment0260005Field005Chars00 ++ (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0260005Field004Chars00 ++ (fragment0260005Field005Chars00 ++ (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail)))))))) fragment0260005Acc00400 := object_fragment0260005_field_003 fuel (fragment0260005Field004Chars00 ++ (fragment0260005Field005Chars00 ++ (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0260005Field005Chars00 ++ (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail))))))) fragment0260005Acc00500 := object_fragment0260005_field_004 fuel (fragment0260005Field005Chars00 ++ (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail)))))) fragment0260005Acc00600 := object_fragment0260005_field_005 fuel (fragment0260005Field006Chars00 ++ (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail))))) fragment0260005Acc00700 := object_fragment0260005_field_006 fuel (fragment0260005Field007Chars00 ++ (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail)))) fragment0260005Acc00800 := object_fragment0260005_field_007 fuel (fragment0260005Field008Chars00 ++ (fragment0260005Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0260005Field009Chars00 ++ (tail))) fragment0260005Acc00900 := object_fragment0260005_field_008 fuel (fragment0260005Field009Chars00 ++ (tail))
    _ = .ok (fragment0260005Value, tail) := object_fragment0260005_field_009 fuel (tail)

noncomputable def fragment0261587Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0261587Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0261587Field000Value00 : SourceJson := .number (String.ofList ['2', '1'])
noncomputable def fragment0261587Acc00100 : List (String × SourceJson) := (fragment0261587Field000Key00, fragment0261587Field000Value00) :: fragment0261587Acc00000
noncomputable def fragment0261587Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '1', ',']

theorem object_fragment0261587_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 373) (SourceJson.white (fragment0261587Field000Chars00 ++ tail)) fragment0261587Acc00000 =
      SourceJson.object (fuel + 372) (SourceJson.white tail) fragment0261587Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261587_object_field_000"
  err.flush

noncomputable def fragment0261587Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0261587Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0261587Acc00200 : List (String × SourceJson) := (fragment0261587Field001Key00, fragment0261587Field001Value00) :: fragment0261587Acc00100
noncomputable def fragment0261587Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0261587_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 372) (SourceJson.white (fragment0261587Field001Chars00 ++ tail)) fragment0261587Acc00100 =
      SourceJson.object (fuel + 371) (SourceJson.white tail) fragment0261587Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261587_object_field_001"
  err.flush

noncomputable def fragment0261587Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0261587Field002Value00 : SourceJson := .str (String.ofList ['2', '8', '3', '3', '5', '3', '4', '0', '9', '6', '2', '6', '1', '9', '6', '3', '1', '6', '7', '4', '7', '9', '8', '4', '5', '4', '4', '5', '2', '0', '3', '3', '4', '1', '3', '1', '2', '7', '/', '2', '3', '1', '7', '3', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0261587Acc00300 : List (String × SourceJson) := (fragment0261587Field002Key00, fragment0261587Field002Value00) :: fragment0261587Acc00200
noncomputable def fragment0261587Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '8', '3', '3', '5', '3', '4', '0', '9', '6', '2', '6', '1', '9', '6', '3', '1', '6', '7', '4', '7', '9', '8', '4', '5', '4', '4', '5', '2', '0', '3', '3', '4', '1', '3', '1', '2', '7', '/', '2', '3', '1', '7', '3', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0261587_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 371) (SourceJson.white (fragment0261587Field002Chars00 ++ tail)) fragment0261587Acc00200 =
      SourceJson.object (fuel + 370) (SourceJson.white tail) fragment0261587Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261587_object_field_002"
  err.flush

noncomputable def fragment0261587Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0261587Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '4', '0', '2', '3', '/', '9', '3', '7', '1', '2', '5', '0', '0', '0'])
noncomputable def fragment0261587Acc00400 : List (String × SourceJson) := (fragment0261587Field003Key00, fragment0261587Field003Value00) :: fragment0261587Acc00300
noncomputable def fragment0261587Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '7', '4', '0', '2', '3', '/', '9', '3', '7', '1', '2', '5', '0', '0', '0', '"', ',']

theorem object_fragment0261587_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 370) (SourceJson.white (fragment0261587Field003Chars00 ++ tail)) fragment0261587Acc00300 =
      SourceJson.object (fuel + 369) (SourceJson.white tail) fragment0261587Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261587_object_field_003"
  err.flush

noncomputable def fragment0261587Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0261587Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0261587Acc00500 : List (String × SourceJson) := (fragment0261587Field004Key00, fragment0261587Field004Value00) :: fragment0261587Acc00400
noncomputable def fragment0261587Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0261587_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 369) (SourceJson.white (fragment0261587Field004Chars00 ++ tail)) fragment0261587Acc00400 =
      SourceJson.object (fuel + 368) (SourceJson.white tail) fragment0261587Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261587_object_field_004"
  err.flush

noncomputable def fragment0261587Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0261587Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '9', '9', '9', '6', '1', '3', '9', '9', '1', '6', '9', '5', '8', '1', '7', '3', '7', '/', '2', '2', '7', '8', '6', '4', '7', '1', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '7', '0', '8', '8', '3', '5', '6', '6', '4', '2', '0', '2', '0', '8', '7', '7', '3', '/', '1', '1', '1', '6', '5', '3', '7', '1', '2', '6', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '9', '8', '6', '6', '1', '3', '2', '0', '7', '2', '3', '3', '0', '4', '0', '3', '/', '6', '4', '4', '1', '5', '6', '0', '3', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '7', '1', '9', '3', '8', '7', '0', '1', '6', '0', '9', '6', '4', '0', '9', '3', '4', '9', '/', '1', '1', '1', '6', '5', '3', '7', '1', '2', '6', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '6', '9', '7', '8', '3', '8', '0', '2', '0', '7', '3', '2', '6', '8', '9', '9', '/', '1', '9', '7', '0', '3', '5', '9', '6', '3', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '8', '2', '5', '8', '7', '7', '5', '2', '0', '7', '6', '8', '6', '1', '1', '5', '1', '/', '8', '3', '7', '4', '0', '2', '8', '4', '4', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '2', '0', '3', '9', '3', '3', '9', '1', '9', '5', '3', '1', '1', '9', '3', '5', '1', '/', '8', '3', '7', '4', '0', '2', '8', '4', '4', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '6', '4', '3', '0', '2', '3', '6', '9', '2', '9', '8', '8', '0', '6', '3', '4', '9', '/', '3', '3', '4', '9', '6', '1', '1', '3', '7', '9', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '8', '9', '6', '8', '1', '1', '1', '5', '5', '0', '0', '0', '6', '8', '7', '2', '9', '/', '3', '3', '4', '9', '6', '1', '1', '3', '7', '9', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '1', '2', '1', '9', '7', '7', '8', '4', '4', '1', '2', '0', '3', '4', '0', '6', '9', '/', '3', '3', '4', '9', '6', '1', '1', '3', '7', '9', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0261587Acc00600 : List (String × SourceJson) := (fragment0261587Field005Key00, fragment0261587Field005Value00) :: fragment0261587Acc00500
noncomputable def fragment0261587Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '9', '9', '6', '1', '3', '9', '9', '1', '6', '9', '5', '8', '1', '7', '3', '7', '/', '2', '2', '7', '8', '6', '4', '7', '1', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '7', '0', '8', '8', '3', '5', '6', '6', '4', '2', '0', '2', '0', '8', '7', '7', '3', '/', '1', '1', '1', '6', '5', '3', '7', '1', '2', '6', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '9', '8', '6', '6', '1', '3', '2', '0', '7', '2', '3', '3', '0', '4', '0', '3', '/', '6', '4', '4', '1', '5', '6', '0', '3', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '1', '9', '3', '8', '7', '0', '1', '6', '0', '9', '6', '4', '0', '9', '3', '4', '9', '/', '1', '1', '1', '6', '5', '3', '7', '1', '2', '6', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '6', '9', '7', '8', '3', '8', '0', '2', '0', '7', '3', '2', '6', '8', '9', '9', '/', '1', '9', '7', '0', '3', '5', '9', '6', '3', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '8', '2', '5', '8', '7', '7', '5', '2', '0', '7', '6', '8', '6', '1', '1', '5', '1', '/', '8', '3', '7', '4', '0', '2', '8', '4', '4', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '0', '3', '9', '3', '3', '9', '1', '9', '5', '3', '1', '1', '9', '3', '5', '1', '/', '8', '3', '7', '4', '0', '2', '8', '4', '4', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '6', '4', '3', '0', '2', '3', '6', '9', '2', '9', '8', '8', '0', '6', '3', '4', '9', '/', '3', '3', '4', '9', '6', '1', '1', '3', '7', '9', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '8', '9', '6', '8', '1', '1', '1', '5', '5', '0', '0', '0', '6', '8', '7', '2', '9', '/', '3', '3', '4', '9', '6', '1', '1', '3', '7', '9', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '1', '2', '1', '9', '7', '7', '8', '4', '4', '1', '2', '0', '3', '4', '0', '6', '9', '/', '3', '3', '4', '9', '6', '1', '1', '3', '7', '9', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0261587_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 368) (SourceJson.white (fragment0261587Field005Chars00 ++ tail)) fragment0261587Acc00500 =
      SourceJson.object (fuel + 367) (SourceJson.white tail) fragment0261587Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261587_object_field_005"
  err.flush

noncomputable def fragment0261587Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0261587Field006Value00 : SourceJson := .str (String.ofList ['4', '6', '9', '5', '3', '4', '7', '5', '0', '5', '6', '0', '4', '4', '6', '7', '8', '0', '6', '2', '6', '9', '0', '0', '3', '6', '1', '1', '6', '5', '8', '7', '4', '0', '7', '2', '3', '4', '6', '4', '5', '5', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '/', '3', '5', '7', '6', '9', '3', '4', '2', '0', '5', '6', '6', '7', '7', '0', '6', '2', '6', '2', '8', '7', '3', '4', '0', '1', '1', '3', '0', '4', '6', '7', '3', '9', '2', '5', '3', '8', '4', '8', '1', '2', '4', '3', '4', '6', '7', '5', '8', '7', '0', '0', '2', '5', '4', '1', '9', '3', '4', '4', '1', '0', '4', '3'])
noncomputable def fragment0261587Acc00700 : List (String × SourceJson) := (fragment0261587Field006Key00, fragment0261587Field006Value00) :: fragment0261587Acc00600
noncomputable def fragment0261587Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '6', '9', '5', '3', '4', '7', '5', '0', '5', '6', '0', '4', '4', '6', '7', '8', '0', '6', '2', '6', '9', '0', '0', '3', '6', '1', '1', '6', '5', '8', '7', '4', '0', '7', '2', '3', '4', '6', '4', '5', '5', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '/', '3', '5', '7', '6', '9', '3', '4', '2', '0', '5', '6', '6', '7', '7', '0', '6', '2', '6', '2', '8', '7', '3', '4', '0', '1', '1', '3', '0', '4', '6', '7', '3', '9', '2', '5', '3', '8', '4', '8', '1', '2', '4', '3', '4', '6', '7', '5', '8', '7', '0', '0', '2', '5', '4', '1', '9', '3', '4', '4', '1', '0', '4', '3', '"', ',']

theorem object_fragment0261587_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 367) (SourceJson.white (fragment0261587Field006Chars00 ++ tail)) fragment0261587Acc00600 =
      SourceJson.object (fuel + 366) (SourceJson.white tail) fragment0261587Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261587_object_field_006"
  err.flush

noncomputable def fragment0261587Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0261587Field007Value00 : SourceJson := .str (String.ofList ['5', '3', '2', '6', '2', '8', '5', '5', '5', '2', '3', '1', '6', '0', '8', '7', '6', '4', '6', '0', '9', '7', '1', '3', '9', '2', '0', '3', '7', '1', '3', '5', '9', '1', '4', '7', '1', '4', '8', '8', '7', '8', '8', '1', '0', '7', '3', '9', '2', '8', '9', '4', '5', '6', '1', '4', '3', '8', '0', '6', '8', '3', '0', '7', '3', '5', '9', '5', '7', '2', '2', '6', '8', '4', '5', '4', '3', '7', '1', '2', '6', '0', '4', '7', '0', '2', '2', '7', '8', '2', '2', '9', '4', '7', '7', '0', '6', '1', '6', '5', '3', '2', '9', '5', '6', '4', '4', '4', '5', '8', '0', '2', '3', '3', '4', '7', '5', '4', '8', '4', '6', '5', '9', '2', '9', '9', '4', '9', '9', '2', '0', '8', '0', '0', '8', '1', '2', '1', '5', '8', '7', '8', '4', '7', '7', '1', '1', '9', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '4', '1', '1', '4', '6', '1', '0', '8', '1', '0', '5', '5', '0', '8', '7', '1', '3', '9', '5', '1', '4', '5', '2', '3', '7', '0', '2', '2', '3', '3', '1', '2', '0', '8', '0', '3', '7', '7', '9', '1', '8', '1', '0', '6', '4', '0', '0', '2', '4', '7', '1', '1', '8', '7', '6', '8', '5', '6', '8', '5', '1', '3', '3', '0', '2', '8', '6', '4', '7', '2', '2', '0', '6', '1', '1', '1', '4', '6', '3', '4', '4', '2', '2', '1', '1', '3', '9', '4', '4', '0', '4', '1', '1', '9', '2', '3', '0', '8', '8', '2', '9', '4', '4', '7', '7', '1', '2', '3', '1', '2', '0', '1', '0', '2', '7', '5', '2', '5', '8', '5', '5', '4', '4', '3', '4', '4', '3', '7', '5', '2', '2', '0', '1', '2', '9', '1', '0', '1', '5', '7', '2', '0', '8', '3', '6', '6', '7', '5', '7', '0', '0', '5', '9', '9', '9', '1', '3', '1', '2', '6', '9', '2', '7', '1', '9', '4', '4', '1', '1', '1', '3', '0', '6', '5', '1', '2', '0', '9', '3', '1', '2', '9', '8', '9', '7'])
noncomputable def fragment0261587Acc00800 : List (String × SourceJson) := (fragment0261587Field007Key00, fragment0261587Field007Value00) :: fragment0261587Acc00700
noncomputable def fragment0261587Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '3', '2', '6', '2', '8', '5', '5', '5', '2', '3', '1', '6', '0', '8', '7', '6', '4', '6', '0', '9', '7', '1', '3', '9', '2', '0', '3', '7', '1', '3', '5', '9', '1', '4', '7', '1', '4', '8', '8', '7', '8', '8', '1', '0', '7', '3', '9', '2', '8', '9', '4', '5', '6', '1', '4', '3', '8', '0', '6', '8', '3', '0', '7', '3', '5', '9', '5', '7', '2', '2', '6', '8', '4', '5', '4', '3', '7', '1', '2', '6', '0', '4', '7', '0', '2', '2', '7', '8', '2', '2', '9', '4', '7', '7', '0', '6', '1', '6', '5', '3', '2', '9', '5', '6', '4', '4', '4', '5', '8', '0', '2', '3', '3', '4', '7', '5', '4', '8', '4', '6', '5', '9', '2', '9', '9', '4', '9', '9', '2', '0', '8', '0', '0', '8', '1', '2', '1', '5', '8', '7', '8', '4', '7', '7', '1', '1', '9', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '4', '1', '1', '4', '6', '1', '0', '8', '1', '0', '5', '5', '0', '8', '7', '1', '3', '9', '5', '1', '4', '5', '2', '3', '7', '0', '2', '2', '3', '3', '1', '2', '0', '8', '0', '3', '7', '7', '9', '1', '8', '1', '0', '6', '4', '0', '0', '2', '4', '7', '1', '1', '8', '7', '6', '8', '5', '6', '8', '5', '1', '3', '3', '0', '2', '8', '6', '4', '7', '2', '2', '0', '6', '1', '1', '1', '4', '6', '3', '4', '4', '2', '2', '1', '1', '3', '9', '4', '4', '0', '4', '1', '1', '9', '2', '3', '0', '8', '8', '2', '9', '4', '4', '7', '7', '1', '2', '3', '1', '2', '0', '1', '0', '2', '7', '5', '2', '5', '8', '5', '5', '4', '4', '3', '4', '4', '3', '7', '5', '2', '2', '0', '1', '2', '9', '1', '0', '1', '5', '7', '2', '0', '8', '3', '6', '6', '7', '5', '7', '0', '0', '5', '9', '9', '9', '1', '3', '1', '2', '6', '9', '2', '7', '1', '9', '4', '4', '1', '1', '1', '3', '0', '6', '5', '1', '2', '0', '9', '3', '1', '2', '9', '8', '9', '7', '"', ',']

theorem object_fragment0261587_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 366) (SourceJson.white (fragment0261587Field007Chars00 ++ tail)) fragment0261587Acc00700 =
      SourceJson.object (fuel + 365) (SourceJson.white tail) fragment0261587Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261587_object_field_007"
  err.flush

noncomputable def fragment0261587Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0261587Field008Value00 : SourceJson := .str (String.ofList ['1', '0', '4', '0', '0', '0', '7', '2', '6', '2', '7', '7', '1', '3', '7', '2', '4', '5', '1'])
noncomputable def fragment0261587Acc00900 : List (String × SourceJson) := (fragment0261587Field008Key00, fragment0261587Field008Value00) :: fragment0261587Acc00800
noncomputable def fragment0261587Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '4', '0', '0', '0', '7', '2', '6', '2', '7', '7', '1', '3', '7', '2', '4', '5', '1', '"', ',']

theorem object_fragment0261587_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 365) (SourceJson.white (fragment0261587Field008Chars00 ++ tail)) fragment0261587Acc00800 =
      SourceJson.object (fuel + 364) (SourceJson.white tail) fragment0261587Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261587_object_field_008"
  err.flush

noncomputable def fragment0261587Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0261587Field009Value00 : SourceJson := .str (String.ofList ['7', '7', '9', '8', '1', '1', '2', '3', '9', '5', '4', '4', '2', '0', '1', '4', '2', '9', '6'])
noncomputable def fragment0261587Acc01000 : List (String × SourceJson) := (fragment0261587Field009Key00, fragment0261587Field009Value00) :: fragment0261587Acc00900
noncomputable def fragment0261587Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '7', '9', '8', '1', '1', '2', '3', '9', '5', '4', '4', '2', '0', '1', '4', '2', '9', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0261587_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 364) (SourceJson.white (fragment0261587Field009Chars00 ++ tail)) fragment0261587Acc00900 =
      .ok (.obj (fragment0261587Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261587_object_field_009"
  err.flush

noncomputable def fragment0261587Chars : List Char := '{' :: (fragment0261587Field000Chars00 ++ fragment0261587Field001Chars00 ++ fragment0261587Field002Chars00 ++ fragment0261587Field003Chars00 ++ fragment0261587Field004Chars00 ++ fragment0261587Field005Chars00 ++ fragment0261587Field006Chars00 ++ fragment0261587Field007Chars00 ++ fragment0261587Field008Chars00 ++ fragment0261587Field009Chars00)
noncomputable def fragment0261587Value : SourceJson := .obj (fragment0261587Acc01000.reverse)

theorem value_fragment0261587 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 374) (fragment0261587Chars ++ tail) =
      .ok (fragment0261587Value, tail) := by
  have hinput : fragment0261587Chars ++ tail = '{' :: (fragment0261587Field000Chars00 ++ (fragment0261587Field001Chars00 ++ (fragment0261587Field002Chars00 ++ (fragment0261587Field003Chars00 ++ (fragment0261587Field004Chars00 ++ (fragment0261587Field005Chars00 ++ (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0261587Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 374) (fragment0261587Chars ++ tail) =
        SourceJson.value (fuel + 374) ('{' :: (fragment0261587Field000Chars00 ++ (fragment0261587Field001Chars00 ++ (fragment0261587Field002Chars00 ++ (fragment0261587Field003Chars00 ++ (fragment0261587Field004Chars00 ++ (fragment0261587Field005Chars00 ++ (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 374)) hinput
    _ = SourceJson.object (fuel + 373) (SourceJson.white (fragment0261587Field000Chars00 ++ (fragment0261587Field001Chars00 ++ (fragment0261587Field002Chars00 ++ (fragment0261587Field003Chars00 ++ (fragment0261587Field004Chars00 ++ (fragment0261587Field005Chars00 ++ (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail)))))))))))) fragment0261587Acc00000 := by rfl
    _ = SourceJson.object (fuel + 372) (SourceJson.white (fragment0261587Field001Chars00 ++ (fragment0261587Field002Chars00 ++ (fragment0261587Field003Chars00 ++ (fragment0261587Field004Chars00 ++ (fragment0261587Field005Chars00 ++ (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail))))))))))) fragment0261587Acc00100 := object_fragment0261587_field_000 fuel (fragment0261587Field001Chars00 ++ (fragment0261587Field002Chars00 ++ (fragment0261587Field003Chars00 ++ (fragment0261587Field004Chars00 ++ (fragment0261587Field005Chars00 ++ (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 371) (SourceJson.white (fragment0261587Field002Chars00 ++ (fragment0261587Field003Chars00 ++ (fragment0261587Field004Chars00 ++ (fragment0261587Field005Chars00 ++ (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail)))))))))) fragment0261587Acc00200 := object_fragment0261587_field_001 fuel (fragment0261587Field002Chars00 ++ (fragment0261587Field003Chars00 ++ (fragment0261587Field004Chars00 ++ (fragment0261587Field005Chars00 ++ (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 370) (SourceJson.white (fragment0261587Field003Chars00 ++ (fragment0261587Field004Chars00 ++ (fragment0261587Field005Chars00 ++ (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail))))))))) fragment0261587Acc00300 := object_fragment0261587_field_002 fuel (fragment0261587Field003Chars00 ++ (fragment0261587Field004Chars00 ++ (fragment0261587Field005Chars00 ++ (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 369) (SourceJson.white (fragment0261587Field004Chars00 ++ (fragment0261587Field005Chars00 ++ (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail)))))))) fragment0261587Acc00400 := object_fragment0261587_field_003 fuel (fragment0261587Field004Chars00 ++ (fragment0261587Field005Chars00 ++ (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 368) (SourceJson.white (fragment0261587Field005Chars00 ++ (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail))))))) fragment0261587Acc00500 := object_fragment0261587_field_004 fuel (fragment0261587Field005Chars00 ++ (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 367) (SourceJson.white (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail)))))) fragment0261587Acc00600 := object_fragment0261587_field_005 fuel (fragment0261587Field006Chars00 ++ (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 366) (SourceJson.white (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail))))) fragment0261587Acc00700 := object_fragment0261587_field_006 fuel (fragment0261587Field007Chars00 ++ (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 365) (SourceJson.white (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail)))) fragment0261587Acc00800 := object_fragment0261587_field_007 fuel (fragment0261587Field008Chars00 ++ (fragment0261587Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 364) (SourceJson.white (fragment0261587Field009Chars00 ++ (tail))) fragment0261587Acc00900 := object_fragment0261587_field_008 fuel (fragment0261587Field009Chars00 ++ (tail))
    _ = .ok (fragment0261587Value, tail) := object_fragment0261587_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0020_before_reader"
  err.flush

noncomputable def chunk0020LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0020SuffixChars00 : List Char := [',']
noncomputable def chunk0020Chars00 : List Char := chunk0020LeadChars00 ++ fragment0260005Chars ++ chunk0020SuffixChars00
noncomputable def chunk0020Push00 (acc : List SourceJson) : List SourceJson := fragment0260005Value :: acc

noncomputable def chunk0020AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0020_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 584)
      (SourceJson.white (chunk0020LeadChars00 ++ (fragment0260005Chars ++ rest))) acc =
      (SourceJson.value (fuel + 583) (fragment0260005Chars ++ rest)).bind
        (chunk0020AfterValue00 (fuel + 583) acc) := by rfl

theorem array_chunk0020 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 584) (SourceJson.white (chunk0020Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 583) (SourceJson.white tail) (chunk0020Push00 acc) := by
  have hinput : chunk0020Chars00 ++ tail = chunk0020LeadChars00 ++ (fragment0260005Chars ++ (chunk0020SuffixChars00 ++ tail)) := by
    simp only [chunk0020Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 584) (SourceJson.white (chunk0020Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 584)
          (SourceJson.white (chunk0020LeadChars00 ++ (fragment0260005Chars ++ (chunk0020SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 584) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 583) (fragment0260005Chars ++ (chunk0020SuffixChars00 ++ tail))).bind
        (chunk0020AfterValue00 (fuel + 583) acc) := array_chunk0020_head fuel (chunk0020SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0260005Value, chunk0020SuffixChars00 ++ tail)).bind
        (chunk0020AfterValue00 (fuel + 583) acc) :=
      congrArg (fun result => result.bind (chunk0020AfterValue00 (fuel + 583) acc))
        (value_fragment0260005 (fuel + 345) (chunk0020SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 583) (SourceJson.white tail) (chunk0020Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0020_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0021_before_reader"
  err.flush

noncomputable def chunk0021LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0021SuffixChars00 : List Char := [',']
noncomputable def chunk0021Chars00 : List Char := chunk0021LeadChars00 ++ fragment0261587Chars ++ chunk0021SuffixChars00
noncomputable def chunk0021Push00 (acc : List SourceJson) : List SourceJson := fragment0261587Value :: acc

noncomputable def chunk0021AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0021_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 583)
      (SourceJson.white (chunk0021LeadChars00 ++ (fragment0261587Chars ++ rest))) acc =
      (SourceJson.value (fuel + 582) (fragment0261587Chars ++ rest)).bind
        (chunk0021AfterValue00 (fuel + 582) acc) := by rfl

theorem array_chunk0021 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 583) (SourceJson.white (chunk0021Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 582) (SourceJson.white tail) (chunk0021Push00 acc) := by
  have hinput : chunk0021Chars00 ++ tail = chunk0021LeadChars00 ++ (fragment0261587Chars ++ (chunk0021SuffixChars00 ++ tail)) := by
    simp only [chunk0021Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 583) (SourceJson.white (chunk0021Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 583)
          (SourceJson.white (chunk0021LeadChars00 ++ (fragment0261587Chars ++ (chunk0021SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 583) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 582) (fragment0261587Chars ++ (chunk0021SuffixChars00 ++ tail))).bind
        (chunk0021AfterValue00 (fuel + 582) acc) := array_chunk0021_head fuel (chunk0021SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0261587Value, chunk0021SuffixChars00 ++ tail)).bind
        (chunk0021AfterValue00 (fuel + 582) acc) :=
      congrArg (fun result => result.bind (chunk0021AfterValue00 (fuel + 582) acc))
        (value_fragment0261587 (fuel + 208) (chunk0021SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 582) (SourceJson.white tail) (chunk0021Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0021_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0020Chars00 ++ chunk0021Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0021Push00 (chunk0020Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 584) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 582) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0020Chars00 ++ (chunk0021Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 584) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 584) (SourceJson.white (chunk0020Chars00 ++ (chunk0021Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 584) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 583) (SourceJson.white (chunk0021Chars00 ++ (tail))) (chunk0020Push00 (acc)) := array_chunk0020 fuel (chunk0021Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 582) (SourceJson.white tail) (blockPush acc) := array_chunk0021 fuel (tail) (chunk0020Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 259999).take 3455 = blockChars := by rfl

theorem block_original_split : sourceRest 259999 = blockChars ++ sourceRest 263454 := by
  calc
    sourceRest 259999 = (sourceRest 259999).take 3455 ++ (sourceRest 259999).drop 3455 :=
      (List.take_append_drop 3455 (sourceRest 259999)).symm
    _ = blockChars ++ (sourceRest 259999).drop 3455 :=
      congrArg (fun part => part ++ (sourceRest 259999).drop 3455) block_original_prefix
    _ = blockChars ++ sourceRest 263454 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 259999 3455)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 584) (SourceJson.white (sourceRest 259999)) acc =
      SourceJson.array (fuel + 582) (SourceJson.white (sourceRest 263454)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 584) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 263454) acc)

#print axioms object_fragment0260005_field_000
#print axioms object_fragment0260005_field_001
#print axioms object_fragment0260005_field_002
#print axioms object_fragment0260005_field_003
#print axioms object_fragment0260005_field_004
#print axioms object_fragment0260005_field_005
#print axioms object_fragment0260005_field_006
#print axioms object_fragment0260005_field_007
#print axioms object_fragment0260005_field_008
#print axioms object_fragment0260005_field_009
#print axioms value_fragment0260005
#print axioms object_fragment0261587_field_000
#print axioms object_fragment0261587_field_001
#print axioms object_fragment0261587_field_002
#print axioms object_fragment0261587_field_003
#print axioms object_fragment0261587_field_004
#print axioms object_fragment0261587_field_005
#print axioms object_fragment0261587_field_006
#print axioms object_fragment0261587_field_007
#print axioms object_fragment0261587_field_008
#print axioms object_fragment0261587_field_009
#print axioms value_fragment0261587
#print axioms array_chunk0020_head
#print axioms array_chunk0020
#print axioms array_chunk0021_head
#print axioms array_chunk0021
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock010

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
