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

namespace SimplicesBlock061

noncomputable def fragment0430787Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0430787Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0430787Field000Value00 : SourceJson := .number (String.ofList ['1', '2', '0'])
noncomputable def fragment0430787Acc00100 : List (String × SourceJson) := (fragment0430787Field000Key00, fragment0430787Field000Value00) :: fragment0430787Acc00000
noncomputable def fragment0430787Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '0', ',']

theorem object_fragment0430787_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 366) (SourceJson.white (fragment0430787Field000Chars00 ++ tail)) fragment0430787Acc00000 =
      SourceJson.object (fuel + 365) (SourceJson.white tail) fragment0430787Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0430787_object_field_000"
  err.flush

noncomputable def fragment0430787Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0430787Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['5']), .number (String.ofList ['3'])]
noncomputable def fragment0430787Acc00200 : List (String × SourceJson) := (fragment0430787Field001Key00, fragment0430787Field001Value00) :: fragment0430787Acc00100
noncomputable def fragment0430787Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0430787_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 365) (SourceJson.white (fragment0430787Field001Chars00 ++ tail)) fragment0430787Acc00100 =
      SourceJson.object (fuel + 364) (SourceJson.white tail) fragment0430787Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0430787_object_field_001"
  err.flush

noncomputable def fragment0430787Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0430787Field002Value00 : SourceJson := .str (String.ofList ['1', '1', '5', '7', '5', '1', '9', '5', '5', '8', '5', '9', '0', '7', '6', '6', '8', '4', '5', '5', '2', '7', '2', '4', '6', '6', '2', '9', '9', '5', '6', '2', '9', '5', '6', '9', '9', '0', '5', '7', '5', '8', '5', '3', '2', '1', '/', '2', '8', '1', '7', '9', '7', '4', '5', '3', '8', '7', '1', '8', '3', '0', '7', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0430787Acc00300 : List (String × SourceJson) := (fragment0430787Field002Key00, fragment0430787Field002Value00) :: fragment0430787Acc00200
noncomputable def fragment0430787Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '1', '5', '7', '5', '1', '9', '5', '5', '8', '5', '9', '0', '7', '6', '6', '8', '4', '5', '5', '2', '7', '2', '4', '6', '6', '2', '9', '9', '5', '6', '2', '9', '5', '6', '9', '9', '0', '5', '7', '5', '8', '5', '3', '2', '1', '/', '2', '8', '1', '7', '9', '7', '4', '5', '3', '8', '7', '1', '8', '3', '0', '7', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0430787_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 364) (SourceJson.white (fragment0430787Field002Chars00 ++ tail)) fragment0430787Acc00200 =
      SourceJson.object (fuel + 363) (SourceJson.white tail) fragment0430787Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0430787_object_field_002"
  err.flush

noncomputable def fragment0430787Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0430787Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '0', '8', '3', '0', '3', '/', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0430787Acc00400 : List (String × SourceJson) := (fragment0430787Field003Key00, fragment0430787Field003Value00) :: fragment0430787Acc00300
noncomputable def fragment0430787Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '7', '0', '8', '3', '0', '3', '/', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0430787_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 363) (SourceJson.white (fragment0430787Field003Chars00 ++ tail)) fragment0430787Acc00300 =
      SourceJson.object (fuel + 362) (SourceJson.white tail) fragment0430787Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0430787_object_field_003"
  err.flush

noncomputable def fragment0430787Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0430787Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '7', '0', '3', '1', '7', '7', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '3', '9', '0', '5', '4', '9', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '4', '0', '4', '6', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '5', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0430787Acc00500 : List (String × SourceJson) := (fragment0430787Field004Key00, fragment0430787Field004Value00) :: fragment0430787Acc00400
noncomputable def fragment0430787Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '0', '3', '1', '7', '7', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '9', '0', '5', '4', '9', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '4', '0', '4', '6', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '5', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0430787_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 362) (SourceJson.white (fragment0430787Field004Chars00 ++ tail)) fragment0430787Acc00400 =
      SourceJson.object (fuel + 361) (SourceJson.white tail) fragment0430787Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0430787_object_field_004"
  err.flush

noncomputable def fragment0430787Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0430787Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '1', '3', '4', '8', '1', '7', '6', '1', '0', '4', '0', '5', '9', '9', '0', '0', '0', '7', '/', '3', '7', '4', '6', '4', '0', '6', '8', '8', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '5', '2', '1', '1', '2', '2', '9', '8', '7', '6', '0', '4', '8', '5', '0', '3', '2', '1', '/', '2', '9', '9', '7', '1', '2', '5', '5', '1', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '7', '2', '3', '3', '6', '8', '0', '3', '6', '0', '1', '8', '5', '9', '6', '7', '1', '/', '2', '1', '4', '0', '8', '0', '3', '9', '3', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '1', '2', '8', '1', '4', '0', '2', '1', '2', '0', '8', '0', '9', '8', '7', '4', '7', '3', '/', '2', '9', '9', '7', '1', '2', '5', '5', '1', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '5', '8', '9', '0', '8', '5', '7', '8', '3', '7', '7', '4', '8', '8', '6', '3', '/', '2', '5', '1', '8', '5', '9', '2', '8', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '6', '6', '2', '7', '1', '4', '0', '3', '0', '3', '4', '0', '7', '4', '6', '3', '9', '/', '7', '4', '9', '2', '8', '1', '3', '7', '7', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '0', '7', '4', '5', '2', '1', '7', '5', '4', '3', '6', '1', '0', '2', '3', '5', '6', '7', '/', '1', '7', '1', '2', '6', '4', '3', '1', '4', '8', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '1', '9', '1', '8', '3', '7', '1', '3', '4', '8', '9', '9', '6', '7', '5', '9', '7', '/', '1', '7', '1', '2', '6', '4', '3', '1', '4', '8', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '7', '0', '3', '5', '8', '6', '5', '2', '9', '9', '7', '6', '5', '5', '0', '1', '1', '/', '2', '9', '9', '7', '1', '2', '5', '5', '1', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '7', '0', '3', '3', '8', '6', '7', '2', '1', '6', '0', '9', '2', '1', '2', '5', '1', '/', '2', '9', '9', '7', '1', '2', '5', '5', '1', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0430787Acc00600 : List (String × SourceJson) := (fragment0430787Field005Key00, fragment0430787Field005Value00) :: fragment0430787Acc00500
noncomputable def fragment0430787Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '3', '4', '8', '1', '7', '6', '1', '0', '4', '0', '5', '9', '9', '0', '0', '0', '7', '/', '3', '7', '4', '6', '4', '0', '6', '8', '8', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '5', '2', '1', '1', '2', '2', '9', '8', '7', '6', '0', '4', '8', '5', '0', '3', '2', '1', '/', '2', '9', '9', '7', '1', '2', '5', '5', '1', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '7', '2', '3', '3', '6', '8', '0', '3', '6', '0', '1', '8', '5', '9', '6', '7', '1', '/', '2', '1', '4', '0', '8', '0', '3', '9', '3', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '1', '2', '8', '1', '4', '0', '2', '1', '2', '0', '8', '0', '9', '8', '7', '4', '7', '3', '/', '2', '9', '9', '7', '1', '2', '5', '5', '1', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '8', '9', '0', '8', '5', '7', '8', '3', '7', '7', '4', '8', '8', '6', '3', '/', '2', '5', '1', '8', '5', '9', '2', '8', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '6', '6', '2', '7', '1', '4', '0', '3', '0', '3', '4', '0', '7', '4', '6', '3', '9', '/', '7', '4', '9', '2', '8', '1', '3', '7', '7', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '7', '4', '5', '2', '1', '7', '5', '4', '3', '6', '1', '0', '2', '3', '5', '6', '7', '/', '1', '7', '1', '2', '6', '4', '3', '1', '4', '8', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '1', '9', '1', '8', '3', '7', '1', '3', '4', '8', '9', '9', '6', '7', '5', '9', '7', '/', '1', '7', '1', '2', '6', '4', '3', '1', '4', '8', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '7', '0', '3', '5', '8', '6', '5', '2', '9', '9', '7', '6', '5', '5', '0', '1', '1', '/', '2', '9', '9', '7', '1', '2', '5', '5', '1', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '7', '0', '3', '3', '8', '6', '7', '2', '1', '6', '0', '9', '2', '1', '2', '5', '1', '/', '2', '9', '9', '7', '1', '2', '5', '5', '1', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0430787_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 361) (SourceJson.white (fragment0430787Field005Chars00 ++ tail)) fragment0430787Acc00500 =
      SourceJson.object (fuel + 360) (SourceJson.white tail) fragment0430787Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0430787_object_field_005"
  err.flush

noncomputable def fragment0430787Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0430787Field006Value00 : SourceJson := .str (String.ofList ['1', '9', '3', '6', '7', '2', '9', '7', '1', '2', '7', '8', '3', '7', '7', '8', '8', '1', '0', '0', '4', '0', '6', '1', '7', '4', '4', '8', '3', '2', '8', '2', '6', '4', '2', '3', '4', '8', '6', '0', '2', '2', '4', '6', '9', '7', '7', '5', '3', '1', '6', '6', '0', '9', '3', '7', '5', '/', '2', '7', '8', '8', '2', '3', '4', '4', '4', '4', '9', '2', '2', '2', '5', '8', '2', '3', '9', '4', '8', '3', '5', '1', '5', '7', '9', '5', '6', '3', '0', '7', '1', '0', '8', '9', '5', '0', '1', '8', '1', '0', '9', '9', '8', '0', '2', '9', '0', '9', '9', '2', '8', '4', '0', '8', '2', '3', '6', '9', '1', '3', '4', '4', '4', '3', '4', '1', '9', '1', '3', '6'])
noncomputable def fragment0430787Acc00700 : List (String × SourceJson) := (fragment0430787Field006Key00, fragment0430787Field006Value00) :: fragment0430787Acc00600
noncomputable def fragment0430787Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '3', '6', '7', '2', '9', '7', '1', '2', '7', '8', '3', '7', '7', '8', '8', '1', '0', '0', '4', '0', '6', '1', '7', '4', '4', '8', '3', '2', '8', '2', '6', '4', '2', '3', '4', '8', '6', '0', '2', '2', '4', '6', '9', '7', '7', '5', '3', '1', '6', '6', '0', '9', '3', '7', '5', '/', '2', '7', '8', '8', '2', '3', '4', '4', '4', '4', '9', '2', '2', '2', '5', '8', '2', '3', '9', '4', '8', '3', '5', '1', '5', '7', '9', '5', '6', '3', '0', '7', '1', '0', '8', '9', '5', '0', '1', '8', '1', '0', '9', '9', '8', '0', '2', '9', '0', '9', '9', '2', '8', '4', '0', '8', '2', '3', '6', '9', '1', '3', '4', '4', '4', '3', '4', '1', '9', '1', '3', '6', '"', ',']

theorem object_fragment0430787_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 360) (SourceJson.white (fragment0430787Field006Chars00 ++ tail)) fragment0430787Acc00600 =
      SourceJson.object (fuel + 359) (SourceJson.white tail) fragment0430787Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0430787_object_field_006"
  err.flush

noncomputable def fragment0430787Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0430787Field007Value00 : SourceJson := .str (String.ofList ['4', '6', '2', '7', '2', '3', '5', '5', '7', '6', '2', '0', '3', '4', '4', '4', '1', '8', '3', '1', '2', '6', '2', '6', '6', '5', '3', '1', '0', '8', '5', '0', '4', '4', '5', '6', '8', '6', '5', '0', '5', '7', '7', '5', '5', '8', '4', '0', '1', '3', '0', '4', '5', '1', '7', '4', '1', '4', '4', '5', '1', '9', '0', '1', '9', '1', '0', '1', '7', '8', '0', '3', '5', '0', '5', '8', '9', '9', '8', '2', '4', '6', '7', '6', '2', '2', '9', '5', '6', '2', '0', '0', '5', '3', '6', '0', '4', '7', '9', '6', '8', '8', '0', '8', '6', '1', '0', '3', '1', '2', '7', '2', '0', '3', '9', '2', '2', '3', '6', '5', '3', '8', '0', '1', '3', '1', '9', '3', '0', '1', '3', '6', '7', '7', '5', '7', '1', '4', '9', '2', '7', '9', '3', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '0', '6', '4', '2', '8', '0', '9', '3', '6', '6', '3', '9', '6', '3', '6', '2', '2', '7', '7', '8', '0', '6', '8', '7', '7', '2', '3', '6', '4', '2', '3', '0', '5', '0', '5', '5', '2', '6', '6', '8', '2', '9', '7', '5', '3', '5', '7', '9', '6', '8', '4', '1', '9', '0', '9', '0', '1', '0', '4', '6', '9', '8', '2', '2', '9', '5', '1', '7', '6', '1', '9', '2', '2', '1', '6', '9', '6', '6', '3', '5', '8', '5', '5', '7', '6', '1', '1', '3', '2', '1', '3', '7', '5', '1', '7', '3', '6', '9', '1', '3', '2', '1', '9', '1', '2', '8', '8', '4', '2', '5', '9', '8', '2', '6', '5', '5', '2', '1', '4', '5', '9', '8', '8', '5', '0', '9', '9', '9', '1', '0', '3', '8', '5', '2', '1', '1', '3', '6', '8', '9', '9', '7', '4', '5', '0', '7', '9', '4', '0', '2', '4', '2', '9', '9', '5', '0', '9', '4', '4', '3', '7', '6', '1', '1', '3', '7', '7', '7', '5', '9', '0', '0', '0', '0', '3', '5', '5', '5', '6', '4', '8', '5', '3'])
noncomputable def fragment0430787Acc00800 : List (String × SourceJson) := (fragment0430787Field007Key00, fragment0430787Field007Value00) :: fragment0430787Acc00700
noncomputable def fragment0430787Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '6', '2', '7', '2', '3', '5', '5', '7', '6', '2', '0', '3', '4', '4', '4', '1', '8', '3', '1', '2', '6', '2', '6', '6', '5', '3', '1', '0', '8', '5', '0', '4', '4', '5', '6', '8', '6', '5', '0', '5', '7', '7', '5', '5', '8', '4', '0', '1', '3', '0', '4', '5', '1', '7', '4', '1', '4', '4', '5', '1', '9', '0', '1', '9', '1', '0', '1', '7', '8', '0', '3', '5', '0', '5', '8', '9', '9', '8', '2', '4', '6', '7', '6', '2', '2', '9', '5', '6', '2', '0', '0', '5', '3', '6', '0', '4', '7', '9', '6', '8', '8', '0', '8', '6', '1', '0', '3', '1', '2', '7', '2', '0', '3', '9', '2', '2', '3', '6', '5', '3', '8', '0', '1', '3', '1', '9', '3', '0', '1', '3', '6', '7', '7', '5', '7', '1', '4', '9', '2', '7', '9', '3', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '0', '6', '4', '2', '8', '0', '9', '3', '6', '6', '3', '9', '6', '3', '6', '2', '2', '7', '7', '8', '0', '6', '8', '7', '7', '2', '3', '6', '4', '2', '3', '0', '5', '0', '5', '5', '2', '6', '6', '8', '2', '9', '7', '5', '3', '5', '7', '9', '6', '8', '4', '1', '9', '0', '9', '0', '1', '0', '4', '6', '9', '8', '2', '2', '9', '5', '1', '7', '6', '1', '9', '2', '2', '1', '6', '9', '6', '6', '3', '5', '8', '5', '5', '7', '6', '1', '1', '3', '2', '1', '3', '7', '5', '1', '7', '3', '6', '9', '1', '3', '2', '1', '9', '1', '2', '8', '8', '4', '2', '5', '9', '8', '2', '6', '5', '5', '2', '1', '4', '5', '9', '8', '8', '5', '0', '9', '9', '9', '1', '0', '3', '8', '5', '2', '1', '1', '3', '6', '8', '9', '9', '7', '4', '5', '0', '7', '9', '4', '0', '2', '4', '2', '9', '9', '5', '0', '9', '4', '4', '3', '7', '6', '1', '1', '3', '7', '7', '7', '5', '9', '0', '0', '0', '0', '3', '5', '5', '5', '6', '4', '8', '5', '3', '"', ',']

theorem object_fragment0430787_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 359) (SourceJson.white (fragment0430787Field007Chars00 ++ tail)) fragment0430787Acc00700 =
      SourceJson.object (fuel + 358) (SourceJson.white tail) fragment0430787Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0430787_object_field_007"
  err.flush

noncomputable def fragment0430787Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0430787Field008Value00 : SourceJson := .str (String.ofList ['5', '5', '0', '3', '2', '5', '0', '8', '7', '2', '9', '7', '0', '1'])
noncomputable def fragment0430787Acc00900 : List (String × SourceJson) := (fragment0430787Field008Key00, fragment0430787Field008Value00) :: fragment0430787Acc00800
noncomputable def fragment0430787Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '5', '0', '3', '2', '5', '0', '8', '7', '2', '9', '7', '0', '1', '"', ',']

theorem object_fragment0430787_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 358) (SourceJson.white (fragment0430787Field008Chars00 ++ tail)) fragment0430787Acc00800 =
      SourceJson.object (fuel + 357) (SourceJson.white tail) fragment0430787Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0430787_object_field_008"
  err.flush

noncomputable def fragment0430787Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0430787Field009Value00 : SourceJson := .str (String.ofList ['3', '3', '1', '3', '4', '3', '1', '5', '2', '1', '8', '7', '3', '2', '6'])
noncomputable def fragment0430787Acc01000 : List (String × SourceJson) := (fragment0430787Field009Key00, fragment0430787Field009Value00) :: fragment0430787Acc00900
noncomputable def fragment0430787Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '1', '3', '4', '3', '1', '5', '2', '1', '8', '7', '3', '2', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0430787_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 357) (SourceJson.white (fragment0430787Field009Chars00 ++ tail)) fragment0430787Acc00900 =
      .ok (.obj (fragment0430787Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0430787_object_field_009"
  err.flush

noncomputable def fragment0430787Chars : List Char := '{' :: (fragment0430787Field000Chars00 ++ fragment0430787Field001Chars00 ++ fragment0430787Field002Chars00 ++ fragment0430787Field003Chars00 ++ fragment0430787Field004Chars00 ++ fragment0430787Field005Chars00 ++ fragment0430787Field006Chars00 ++ fragment0430787Field007Chars00 ++ fragment0430787Field008Chars00 ++ fragment0430787Field009Chars00)
noncomputable def fragment0430787Value : SourceJson := .obj (fragment0430787Acc01000.reverse)

theorem value_fragment0430787 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 367) (fragment0430787Chars ++ tail) =
      .ok (fragment0430787Value, tail) := by
  have hinput : fragment0430787Chars ++ tail = '{' :: (fragment0430787Field000Chars00 ++ (fragment0430787Field001Chars00 ++ (fragment0430787Field002Chars00 ++ (fragment0430787Field003Chars00 ++ (fragment0430787Field004Chars00 ++ (fragment0430787Field005Chars00 ++ (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0430787Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 367) (fragment0430787Chars ++ tail) =
        SourceJson.value (fuel + 367) ('{' :: (fragment0430787Field000Chars00 ++ (fragment0430787Field001Chars00 ++ (fragment0430787Field002Chars00 ++ (fragment0430787Field003Chars00 ++ (fragment0430787Field004Chars00 ++ (fragment0430787Field005Chars00 ++ (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 367)) hinput
    _ = SourceJson.object (fuel + 366) (SourceJson.white (fragment0430787Field000Chars00 ++ (fragment0430787Field001Chars00 ++ (fragment0430787Field002Chars00 ++ (fragment0430787Field003Chars00 ++ (fragment0430787Field004Chars00 ++ (fragment0430787Field005Chars00 ++ (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail)))))))))))) fragment0430787Acc00000 := by rfl
    _ = SourceJson.object (fuel + 365) (SourceJson.white (fragment0430787Field001Chars00 ++ (fragment0430787Field002Chars00 ++ (fragment0430787Field003Chars00 ++ (fragment0430787Field004Chars00 ++ (fragment0430787Field005Chars00 ++ (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail))))))))))) fragment0430787Acc00100 := object_fragment0430787_field_000 fuel (fragment0430787Field001Chars00 ++ (fragment0430787Field002Chars00 ++ (fragment0430787Field003Chars00 ++ (fragment0430787Field004Chars00 ++ (fragment0430787Field005Chars00 ++ (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 364) (SourceJson.white (fragment0430787Field002Chars00 ++ (fragment0430787Field003Chars00 ++ (fragment0430787Field004Chars00 ++ (fragment0430787Field005Chars00 ++ (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail)))))))))) fragment0430787Acc00200 := object_fragment0430787_field_001 fuel (fragment0430787Field002Chars00 ++ (fragment0430787Field003Chars00 ++ (fragment0430787Field004Chars00 ++ (fragment0430787Field005Chars00 ++ (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 363) (SourceJson.white (fragment0430787Field003Chars00 ++ (fragment0430787Field004Chars00 ++ (fragment0430787Field005Chars00 ++ (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail))))))))) fragment0430787Acc00300 := object_fragment0430787_field_002 fuel (fragment0430787Field003Chars00 ++ (fragment0430787Field004Chars00 ++ (fragment0430787Field005Chars00 ++ (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 362) (SourceJson.white (fragment0430787Field004Chars00 ++ (fragment0430787Field005Chars00 ++ (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail)))))))) fragment0430787Acc00400 := object_fragment0430787_field_003 fuel (fragment0430787Field004Chars00 ++ (fragment0430787Field005Chars00 ++ (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 361) (SourceJson.white (fragment0430787Field005Chars00 ++ (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail))))))) fragment0430787Acc00500 := object_fragment0430787_field_004 fuel (fragment0430787Field005Chars00 ++ (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 360) (SourceJson.white (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail)))))) fragment0430787Acc00600 := object_fragment0430787_field_005 fuel (fragment0430787Field006Chars00 ++ (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 359) (SourceJson.white (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail))))) fragment0430787Acc00700 := object_fragment0430787_field_006 fuel (fragment0430787Field007Chars00 ++ (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 358) (SourceJson.white (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail)))) fragment0430787Acc00800 := object_fragment0430787_field_007 fuel (fragment0430787Field008Chars00 ++ (fragment0430787Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 357) (SourceJson.white (fragment0430787Field009Chars00 ++ (tail))) fragment0430787Acc00900 := object_fragment0430787_field_008 fuel (fragment0430787Field009Chars00 ++ (tail))
    _ = .ok (fragment0430787Value, tail) := object_fragment0430787_field_009 fuel (tail)

noncomputable def fragment0432692Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0432692Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0432692Field000Value00 : SourceJson := .number (String.ofList ['1', '2', '1'])
noncomputable def fragment0432692Acc00100 : List (String × SourceJson) := (fragment0432692Field000Key00, fragment0432692Field000Value00) :: fragment0432692Acc00000
noncomputable def fragment0432692Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '1', ',']

theorem object_fragment0432692_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0432692Field000Chars00 ++ tail)) fragment0432692Acc00000 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0432692Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0432692_object_field_000"
  err.flush

noncomputable def fragment0432692Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0432692Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '5']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0432692Acc00200 : List (String × SourceJson) := (fragment0432692Field001Key00, fragment0432692Field001Value00) :: fragment0432692Acc00100
noncomputable def fragment0432692Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0432692_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0432692Field001Chars00 ++ tail)) fragment0432692Acc00100 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0432692Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0432692_object_field_001"
  err.flush

noncomputable def fragment0432692Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0432692Field002Value00 : SourceJson := .str (String.ofList ['2', '7', '0', '5', '9', '5', '3', '2', '3', '7', '4', '3', '9', '8', '7', '2', '7', '1', '1', '8', '6', '2', '2', '4', '6', '9', '5', '3', '8', '8', '7', '1', '9', '9', '6', '8', '1', '/', '2', '0', '7', '9', '2', '0', '0', '3', '7', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0432692Acc00300 : List (String × SourceJson) := (fragment0432692Field002Key00, fragment0432692Field002Value00) :: fragment0432692Acc00200
noncomputable def fragment0432692Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '7', '0', '5', '9', '5', '3', '2', '3', '7', '4', '3', '9', '8', '7', '2', '7', '1', '1', '8', '6', '2', '2', '4', '6', '9', '5', '3', '8', '8', '7', '1', '9', '9', '6', '8', '1', '/', '2', '0', '7', '9', '2', '0', '0', '3', '7', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0432692_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0432692Field002Chars00 ++ tail)) fragment0432692Acc00200 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0432692Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0432692_object_field_002"
  err.flush

noncomputable def fragment0432692Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0432692Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0432692Acc00400 : List (String × SourceJson) := (fragment0432692Field003Key00, fragment0432692Field003Value00) :: fragment0432692Acc00300
noncomputable def fragment0432692Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0432692_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0432692Field003Chars00 ++ tail)) fragment0432692Acc00300 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0432692Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0432692_object_field_003"
  err.flush

noncomputable def fragment0432692Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0432692Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '3', '7', '3', '/', '2', '0', '8', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0432692Acc00500 : List (String × SourceJson) := (fragment0432692Field004Key00, fragment0432692Field004Value00) :: fragment0432692Acc00400
noncomputable def fragment0432692Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '3', '7', '3', '/', '2', '0', '8', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0432692_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0432692Field004Chars00 ++ tail)) fragment0432692Acc00400 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0432692Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0432692_object_field_004"
  err.flush

noncomputable def fragment0432692Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0432692Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '1', '2', '6', '6', '7', '9', '2', '5', '6', '4', '4', '5', '1', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '6', '3', '4', '5', '9', '1', '5', '7', '4', '2', '1', '1', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '4', '1', '9', '3', '4', '8', '5', '7', '0', '7', '/', '1', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '9', '2', '9', '4', '2', '5', '4', '4', '7', '0', '3', '3', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '3', '2', '4', '7', '3', '2', '9', '9', '3', '3', '/', '3', '0', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '6', '6', '9', '9', '9', '0', '5', '0', '9', '8', '3', '/', '1', '8', '1', '9', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '3', '9', '1', '0', '5', '9', '5', '2', '8', '3', '9', '/', '6', '9', '3', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '8', '5', '9', '3', '3', '4', '8', '9', '6', '4', '7', '/', '2', '0', '7', '9', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '5', '0', '1', '3', '8', '9', '3', '6', '9', '2', '1', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '8', '3', '3', '7', '1', '5', '5', '9', '9', '8', '7', '/', '1', '2', '1', '2', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0432692Acc00600 : List (String × SourceJson) := (fragment0432692Field005Key00, fragment0432692Field005Value00) :: fragment0432692Acc00500
noncomputable def fragment0432692Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '2', '6', '6', '7', '9', '2', '5', '6', '4', '4', '5', '1', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '6', '3', '4', '5', '9', '1', '5', '7', '4', '2', '1', '1', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '4', '1', '9', '3', '4', '8', '5', '7', '0', '7', '/', '1', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '9', '2', '9', '4', '2', '5', '4', '4', '7', '0', '3', '3', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '2', '4', '7', '3', '2', '9', '9', '3', '3', '/', '3', '0', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '6', '6', '9', '9', '9', '0', '5', '0', '9', '8', '3', '/', '1', '8', '1', '9', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '3', '9', '1', '0', '5', '9', '5', '2', '8', '3', '9', '/', '6', '9', '3', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '8', '5', '9', '3', '3', '4', '8', '9', '6', '4', '7', '/', '2', '0', '7', '9', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '5', '0', '1', '3', '8', '9', '3', '6', '9', '2', '1', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '8', '3', '3', '7', '1', '5', '5', '9', '9', '8', '7', '/', '1', '2', '1', '2', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0432692_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0432692Field005Chars00 ++ tail)) fragment0432692Acc00500 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0432692Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0432692_object_field_005"
  err.flush

noncomputable def fragment0432692Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0432692Field006Value00 : SourceJson := .str (String.ofList ['1', '4', '6', '0', '5', '7', '4', '1', '6', '5', '8', '2', '6', '1', '2', '9', '6', '3', '3', '0', '0', '0', '1', '7', '0', '5', '8', '0', '8', '6', '8', '2', '7', '3', '3', '7', '7', '2', '0', '0', '1', '3', '2', '5', '0', '0', '/', '1', '7', '4', '6', '8', '6', '3', '4', '8', '6', '8', '5', '1', '7', '0', '3', '8', '3', '5', '1', '6', '8', '8', '7', '8', '9', '0', '0', '7', '8', '4', '3', '8', '1', '5', '6', '3', '5', '4', '7', '2', '9', '5', '0', '6', '8', '3', '1', '8', '3', '7', '7', '7', '2', '6', '8', '3', '7', '6', '6', '1'])
noncomputable def fragment0432692Acc00700 : List (String × SourceJson) := (fragment0432692Field006Key00, fragment0432692Field006Value00) :: fragment0432692Acc00600
noncomputable def fragment0432692Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '6', '0', '5', '7', '4', '1', '6', '5', '8', '2', '6', '1', '2', '9', '6', '3', '3', '0', '0', '0', '1', '7', '0', '5', '8', '0', '8', '6', '8', '2', '7', '3', '3', '7', '7', '2', '0', '0', '1', '3', '2', '5', '0', '0', '/', '1', '7', '4', '6', '8', '6', '3', '4', '8', '6', '8', '5', '1', '7', '0', '3', '8', '3', '5', '1', '6', '8', '8', '7', '8', '9', '0', '0', '7', '8', '4', '3', '8', '1', '5', '6', '3', '5', '4', '7', '2', '9', '5', '0', '6', '8', '3', '1', '8', '3', '7', '7', '7', '2', '6', '8', '3', '7', '6', '6', '1', '"', ',']

theorem object_fragment0432692_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0432692Field006Chars00 ++ tail)) fragment0432692Acc00600 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0432692Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0432692_object_field_006"
  err.flush

noncomputable def fragment0432692Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0432692Field007Value00 : SourceJson := .str (String.ofList ['3', '3', '1', '9', '5', '7', '4', '7', '8', '2', '1', '0', '2', '3', '7', '6', '1', '0', '6', '9', '5', '5', '5', '4', '0', '7', '8', '4', '4', '6', '2', '0', '7', '7', '2', '2', '2', '7', '3', '6', '1', '4', '3', '8', '9', '1', '6', '7', '8', '5', '0', '6', '4', '2', '9', '7', '8', '8', '1', '3', '1', '7', '2', '3', '9', '1', '5', '3', '7', '8', '3', '0', '1', '1', '8', '7', '5', '6', '6', '7', '9', '9', '9', '4', '5', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '4', '1', '5', '5', '6', '7', '5', '9', '7', '1', '2', '6', '4', '5', '7', '1', '1', '7', '8', '9', '7', '4', '5', '4', '4', '6', '2', '6', '3', '3', '2', '7', '4', '6', '8', '5', '1', '6', '5', '1', '9', '4', '9', '7', '6', '8', '5', '9', '7', '1', '2', '8', '7', '4', '4', '1', '3', '4', '3', '0', '2', '3', '1', '6', '1', '9', '8', '9', '4', '1', '9', '2', '5', '8', '4', '7', '6', '7', '5', '0', '4', '4', '5', '7', '6', '7', '3', '5', '8', '4', '6', '0', '8', '9', '8', '5', '2', '7', '0', '2', '6', '5', '2', '5', '0', '0', '1', '7', '1', '7', '8', '6', '9', '3', '2', '6', '9', '2', '5', '9', '9', '2', '0', '1', '5', '3'])
noncomputable def fragment0432692Acc00800 : List (String × SourceJson) := (fragment0432692Field007Key00, fragment0432692Field007Value00) :: fragment0432692Acc00700
noncomputable def fragment0432692Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '3', '1', '9', '5', '7', '4', '7', '8', '2', '1', '0', '2', '3', '7', '6', '1', '0', '6', '9', '5', '5', '5', '4', '0', '7', '8', '4', '4', '6', '2', '0', '7', '7', '2', '2', '2', '7', '3', '6', '1', '4', '3', '8', '9', '1', '6', '7', '8', '5', '0', '6', '4', '2', '9', '7', '8', '8', '1', '3', '1', '7', '2', '3', '9', '1', '5', '3', '7', '8', '3', '0', '1', '1', '8', '7', '5', '6', '6', '7', '9', '9', '9', '4', '5', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '4', '1', '5', '5', '6', '7', '5', '9', '7', '1', '2', '6', '4', '5', '7', '1', '1', '7', '8', '9', '7', '4', '5', '4', '4', '6', '2', '6', '3', '3', '2', '7', '4', '6', '8', '5', '1', '6', '5', '1', '9', '4', '9', '7', '6', '8', '5', '9', '7', '1', '2', '8', '7', '4', '4', '1', '3', '4', '3', '0', '2', '3', '1', '6', '1', '9', '8', '9', '4', '1', '9', '2', '5', '8', '4', '7', '6', '7', '5', '0', '4', '4', '5', '7', '6', '7', '3', '5', '8', '4', '6', '0', '8', '9', '8', '5', '2', '7', '0', '2', '6', '5', '2', '5', '0', '0', '1', '7', '1', '7', '8', '6', '9', '3', '2', '6', '9', '2', '5', '9', '9', '2', '0', '1', '5', '3', '"', ',']

theorem object_fragment0432692_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0432692Field007Chars00 ++ tail)) fragment0432692Acc00700 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0432692Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0432692_object_field_007"
  err.flush

noncomputable def fragment0432692Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0432692Field008Value00 : SourceJson := .str (String.ofList ['6', '6', '2', '4', '3', '6', '4', '6', '5', '3', '8', '6', '1', '0'])
noncomputable def fragment0432692Acc00900 : List (String × SourceJson) := (fragment0432692Field008Key00, fragment0432692Field008Value00) :: fragment0432692Acc00800
noncomputable def fragment0432692Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '2', '4', '3', '6', '4', '6', '5', '3', '8', '6', '1', '0', '"', ',']

theorem object_fragment0432692_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0432692Field008Chars00 ++ tail)) fragment0432692Acc00800 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0432692Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0432692_object_field_008"
  err.flush

noncomputable def fragment0432692Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0432692Field009Value00 : SourceJson := .str (String.ofList ['4', '8', '5', '6', '4', '4', '0', '3', '5', '6', '3', '9', '4', '2', '6'])
noncomputable def fragment0432692Acc01000 : List (String × SourceJson) := (fragment0432692Field009Key00, fragment0432692Field009Value00) :: fragment0432692Acc00900
noncomputable def fragment0432692Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '8', '5', '6', '4', '4', '0', '3', '5', '6', '3', '9', '4', '2', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0432692_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0432692Field009Chars00 ++ tail)) fragment0432692Acc00900 =
      .ok (.obj (fragment0432692Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0432692_object_field_009"
  err.flush

noncomputable def fragment0432692Chars : List Char := '{' :: (fragment0432692Field000Chars00 ++ fragment0432692Field001Chars00 ++ fragment0432692Field002Chars00 ++ fragment0432692Field003Chars00 ++ fragment0432692Field004Chars00 ++ fragment0432692Field005Chars00 ++ fragment0432692Field006Chars00 ++ fragment0432692Field007Chars00 ++ fragment0432692Field008Chars00 ++ fragment0432692Field009Chars00)
noncomputable def fragment0432692Value : SourceJson := .obj (fragment0432692Acc01000.reverse)

theorem value_fragment0432692 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 252) (fragment0432692Chars ++ tail) =
      .ok (fragment0432692Value, tail) := by
  have hinput : fragment0432692Chars ++ tail = '{' :: (fragment0432692Field000Chars00 ++ (fragment0432692Field001Chars00 ++ (fragment0432692Field002Chars00 ++ (fragment0432692Field003Chars00 ++ (fragment0432692Field004Chars00 ++ (fragment0432692Field005Chars00 ++ (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0432692Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 252) (fragment0432692Chars ++ tail) =
        SourceJson.value (fuel + 252) ('{' :: (fragment0432692Field000Chars00 ++ (fragment0432692Field001Chars00 ++ (fragment0432692Field002Chars00 ++ (fragment0432692Field003Chars00 ++ (fragment0432692Field004Chars00 ++ (fragment0432692Field005Chars00 ++ (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 252)) hinput
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0432692Field000Chars00 ++ (fragment0432692Field001Chars00 ++ (fragment0432692Field002Chars00 ++ (fragment0432692Field003Chars00 ++ (fragment0432692Field004Chars00 ++ (fragment0432692Field005Chars00 ++ (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail)))))))))))) fragment0432692Acc00000 := by rfl
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0432692Field001Chars00 ++ (fragment0432692Field002Chars00 ++ (fragment0432692Field003Chars00 ++ (fragment0432692Field004Chars00 ++ (fragment0432692Field005Chars00 ++ (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail))))))))))) fragment0432692Acc00100 := object_fragment0432692_field_000 fuel (fragment0432692Field001Chars00 ++ (fragment0432692Field002Chars00 ++ (fragment0432692Field003Chars00 ++ (fragment0432692Field004Chars00 ++ (fragment0432692Field005Chars00 ++ (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0432692Field002Chars00 ++ (fragment0432692Field003Chars00 ++ (fragment0432692Field004Chars00 ++ (fragment0432692Field005Chars00 ++ (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail)))))))))) fragment0432692Acc00200 := object_fragment0432692_field_001 fuel (fragment0432692Field002Chars00 ++ (fragment0432692Field003Chars00 ++ (fragment0432692Field004Chars00 ++ (fragment0432692Field005Chars00 ++ (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0432692Field003Chars00 ++ (fragment0432692Field004Chars00 ++ (fragment0432692Field005Chars00 ++ (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail))))))))) fragment0432692Acc00300 := object_fragment0432692_field_002 fuel (fragment0432692Field003Chars00 ++ (fragment0432692Field004Chars00 ++ (fragment0432692Field005Chars00 ++ (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0432692Field004Chars00 ++ (fragment0432692Field005Chars00 ++ (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail)))))))) fragment0432692Acc00400 := object_fragment0432692_field_003 fuel (fragment0432692Field004Chars00 ++ (fragment0432692Field005Chars00 ++ (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0432692Field005Chars00 ++ (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail))))))) fragment0432692Acc00500 := object_fragment0432692_field_004 fuel (fragment0432692Field005Chars00 ++ (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail)))))) fragment0432692Acc00600 := object_fragment0432692_field_005 fuel (fragment0432692Field006Chars00 ++ (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail))))) fragment0432692Acc00700 := object_fragment0432692_field_006 fuel (fragment0432692Field007Chars00 ++ (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail)))) fragment0432692Acc00800 := object_fragment0432692_field_007 fuel (fragment0432692Field008Chars00 ++ (fragment0432692Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0432692Field009Chars00 ++ (tail))) fragment0432692Acc00900 := object_fragment0432692_field_008 fuel (fragment0432692Field009Chars00 ++ (tail))
    _ = .ok (fragment0432692Value, tail) := object_fragment0432692_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0120_before_reader"
  err.flush

noncomputable def chunk0120LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0120SuffixChars00 : List Char := [',']
noncomputable def chunk0120Chars00 : List Char := chunk0120LeadChars00 ++ fragment0430787Chars ++ chunk0120SuffixChars00
noncomputable def chunk0120Push00 (acc : List SourceJson) : List SourceJson := fragment0430787Value :: acc

noncomputable def chunk0120AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0120_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 484)
      (SourceJson.white (chunk0120LeadChars00 ++ (fragment0430787Chars ++ rest))) acc =
      (SourceJson.value (fuel + 483) (fragment0430787Chars ++ rest)).bind
        (chunk0120AfterValue00 (fuel + 483) acc) := by rfl

theorem array_chunk0120 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 484) (SourceJson.white (chunk0120Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 483) (SourceJson.white tail) (chunk0120Push00 acc) := by
  have hinput : chunk0120Chars00 ++ tail = chunk0120LeadChars00 ++ (fragment0430787Chars ++ (chunk0120SuffixChars00 ++ tail)) := by
    simp only [chunk0120Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 484) (SourceJson.white (chunk0120Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 484)
          (SourceJson.white (chunk0120LeadChars00 ++ (fragment0430787Chars ++ (chunk0120SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 484) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 483) (fragment0430787Chars ++ (chunk0120SuffixChars00 ++ tail))).bind
        (chunk0120AfterValue00 (fuel + 483) acc) := array_chunk0120_head fuel (chunk0120SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0430787Value, chunk0120SuffixChars00 ++ tail)).bind
        (chunk0120AfterValue00 (fuel + 483) acc) :=
      congrArg (fun result => result.bind (chunk0120AfterValue00 (fuel + 483) acc))
        (value_fragment0430787 (fuel + 116) (chunk0120SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 483) (SourceJson.white tail) (chunk0120Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0120_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0121_before_reader"
  err.flush

noncomputable def chunk0121LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0121SuffixChars00 : List Char := [',']
noncomputable def chunk0121Chars00 : List Char := chunk0121LeadChars00 ++ fragment0432692Chars ++ chunk0121SuffixChars00
noncomputable def chunk0121Push00 (acc : List SourceJson) : List SourceJson := fragment0432692Value :: acc

noncomputable def chunk0121AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0121_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 483)
      (SourceJson.white (chunk0121LeadChars00 ++ (fragment0432692Chars ++ rest))) acc =
      (SourceJson.value (fuel + 482) (fragment0432692Chars ++ rest)).bind
        (chunk0121AfterValue00 (fuel + 482) acc) := by rfl

theorem array_chunk0121 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 483) (SourceJson.white (chunk0121Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 482) (SourceJson.white tail) (chunk0121Push00 acc) := by
  have hinput : chunk0121Chars00 ++ tail = chunk0121LeadChars00 ++ (fragment0432692Chars ++ (chunk0121SuffixChars00 ++ tail)) := by
    simp only [chunk0121Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 483) (SourceJson.white (chunk0121Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 483)
          (SourceJson.white (chunk0121LeadChars00 ++ (fragment0432692Chars ++ (chunk0121SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 483) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 482) (fragment0432692Chars ++ (chunk0121SuffixChars00 ++ tail))).bind
        (chunk0121AfterValue00 (fuel + 482) acc) := array_chunk0121_head fuel (chunk0121SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0432692Value, chunk0121SuffixChars00 ++ tail)).bind
        (chunk0121AfterValue00 (fuel + 482) acc) :=
      congrArg (fun result => result.bind (chunk0121AfterValue00 (fuel + 482) acc))
        (value_fragment0432692 (fuel + 230) (chunk0121SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 482) (SourceJson.white tail) (chunk0121Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0121_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0120Chars00 ++ chunk0121Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0121Push00 (chunk0120Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 484) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 482) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0120Chars00 ++ (chunk0121Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 484) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 484) (SourceJson.white (chunk0120Chars00 ++ (chunk0121Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 484) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 483) (SourceJson.white (chunk0121Chars00 ++ (tail))) (chunk0120Push00 (acc)) := array_chunk0120 fuel (chunk0121Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 482) (SourceJson.white tail) (blockPush acc) := array_chunk0121 fuel (tail) (chunk0120Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 430781).take 3517 = blockChars := by rfl

theorem block_original_split : sourceRest 430781 = blockChars ++ sourceRest 434298 := by
  calc
    sourceRest 430781 = (sourceRest 430781).take 3517 ++ (sourceRest 430781).drop 3517 :=
      (List.take_append_drop 3517 (sourceRest 430781)).symm
    _ = blockChars ++ (sourceRest 430781).drop 3517 :=
      congrArg (fun part => part ++ (sourceRest 430781).drop 3517) block_original_prefix
    _ = blockChars ++ sourceRest 434298 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 430781 3517)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 484) (SourceJson.white (sourceRest 430781)) acc =
      SourceJson.array (fuel + 482) (SourceJson.white (sourceRest 434298)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 484) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 434298) acc)

#print axioms object_fragment0430787_field_000
#print axioms object_fragment0430787_field_001
#print axioms object_fragment0430787_field_002
#print axioms object_fragment0430787_field_003
#print axioms object_fragment0430787_field_004
#print axioms object_fragment0430787_field_005
#print axioms object_fragment0430787_field_006
#print axioms object_fragment0430787_field_007
#print axioms object_fragment0430787_field_008
#print axioms object_fragment0430787_field_009
#print axioms value_fragment0430787
#print axioms object_fragment0432692_field_000
#print axioms object_fragment0432692_field_001
#print axioms object_fragment0432692_field_002
#print axioms object_fragment0432692_field_003
#print axioms object_fragment0432692_field_004
#print axioms object_fragment0432692_field_005
#print axioms object_fragment0432692_field_006
#print axioms object_fragment0432692_field_007
#print axioms object_fragment0432692_field_008
#print axioms object_fragment0432692_field_009
#print axioms value_fragment0432692
#print axioms array_chunk0120_head
#print axioms array_chunk0120
#print axioms array_chunk0121_head
#print axioms array_chunk0121
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock061

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
