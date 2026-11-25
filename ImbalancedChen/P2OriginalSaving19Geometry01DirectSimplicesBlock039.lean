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

namespace SimplicesBlock039

noncomputable def fragment0356975Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0356975Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0356975Field000Value00 : SourceJson := .number (String.ofList ['7', '7'])
noncomputable def fragment0356975Acc00100 : List (String × SourceJson) := (fragment0356975Field000Key00, fragment0356975Field000Value00) :: fragment0356975Acc00000
noncomputable def fragment0356975Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '7', ',']

theorem object_fragment0356975_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0356975Field000Chars00 ++ tail)) fragment0356975Acc00000 =
      SourceJson.object (fuel + 222) (SourceJson.white tail) fragment0356975Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0356975_object_field_000"
  err.flush

noncomputable def fragment0356975Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0356975Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0356975Acc00200 : List (String × SourceJson) := (fragment0356975Field001Key00, fragment0356975Field001Value00) :: fragment0356975Acc00100
noncomputable def fragment0356975Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0356975_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment0356975Field001Chars00 ++ tail)) fragment0356975Acc00100 =
      SourceJson.object (fuel + 221) (SourceJson.white tail) fragment0356975Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0356975_object_field_001"
  err.flush

noncomputable def fragment0356975Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0356975Field002Value00 : SourceJson := .str (String.ofList ['1', '3', '5', '4', '1', '2', '5', '8', '2', '7', '3', '7', '1', '4', '0', '7', '4', '7', '3', '4', '6', '4', '4', '0', '0', '4', '9', '4', '5', '3', '2', '3', '9', '9', '/', '4', '2', '8', '6', '5', '4', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0356975Acc00300 : List (String × SourceJson) := (fragment0356975Field002Key00, fragment0356975Field002Value00) :: fragment0356975Acc00200
noncomputable def fragment0356975Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '3', '5', '4', '1', '2', '5', '8', '2', '7', '3', '7', '1', '4', '0', '7', '4', '7', '3', '4', '6', '4', '4', '0', '0', '4', '9', '4', '5', '3', '2', '3', '9', '9', '/', '4', '2', '8', '6', '5', '4', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0356975_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 221) (SourceJson.white (fragment0356975Field002Chars00 ++ tail)) fragment0356975Acc00200 =
      SourceJson.object (fuel + 220) (SourceJson.white tail) fragment0356975Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0356975_object_field_002"
  err.flush

noncomputable def fragment0356975Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0356975Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0356975Acc00400 : List (String × SourceJson) := (fragment0356975Field003Key00, fragment0356975Field003Value00) :: fragment0356975Acc00300
noncomputable def fragment0356975Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0356975_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment0356975Field003Chars00 ++ tail)) fragment0356975Acc00300 =
      SourceJson.object (fuel + 219) (SourceJson.white tail) fragment0356975Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0356975_object_field_003"
  err.flush

noncomputable def fragment0356975Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0356975Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0356975Acc00500 : List (String × SourceJson) := (fragment0356975Field004Key00, fragment0356975Field004Value00) :: fragment0356975Acc00400
noncomputable def fragment0356975Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0356975_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 219) (SourceJson.white (fragment0356975Field004Chars00 ++ tail)) fragment0356975Acc00400 =
      SourceJson.object (fuel + 218) (SourceJson.white tail) fragment0356975Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0356975_object_field_004"
  err.flush

noncomputable def fragment0356975Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0356975Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '7', '5', '7', '1', '4', '7', '2', '8', '9', '/', '9', '4', '0', '5', '7', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '3', '0', '5', '6', '1', '4', '6', '0', '1', '/', '2', '3', '5', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '8', '7', '8', '1', '0', '0', '6', '1', '/', '1', '0', '8', '5', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '5', '8', '0', '2', '5', '8', '6', '9', '6', '3', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '2', '7', '2', '0', '7', '4', '5', '7', '/', '4', '1', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '2', '1', '5', '1', '0', '7', '3', '8', '6', '3', '/', '7', '0', '5', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '6', '7', '0', '0', '0', '2', '7', '2', '3', '7', '/', '4', '2', '3', '2', '5', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '0', '2', '4', '6', '8', '5', '1', '9', '0', '9', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '1', '3', '4', '9', '1', '2', '9', '2', '4', '9', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '1', '3', '4', '4', '8', '9', '6', '6', '5', '7', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0356975Acc00600 : List (String × SourceJson) := (fragment0356975Field005Key00, fragment0356975Field005Value00) :: fragment0356975Acc00500
noncomputable def fragment0356975Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '5', '7', '1', '4', '7', '2', '8', '9', '/', '9', '4', '0', '5', '7', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '3', '0', '5', '6', '1', '4', '6', '0', '1', '/', '2', '3', '5', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '8', '7', '8', '1', '0', '0', '6', '1', '/', '1', '0', '8', '5', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '5', '8', '0', '2', '5', '8', '6', '9', '6', '3', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '2', '7', '2', '0', '7', '4', '5', '7', '/', '4', '1', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '2', '1', '5', '1', '0', '7', '3', '8', '6', '3', '/', '7', '0', '5', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '6', '7', '0', '0', '0', '2', '7', '2', '3', '7', '/', '4', '2', '3', '2', '5', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '0', '2', '4', '6', '8', '5', '1', '9', '0', '9', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '1', '3', '4', '9', '1', '2', '9', '2', '4', '9', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '1', '3', '4', '4', '8', '9', '6', '6', '5', '7', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0356975_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0356975Field005Chars00 ++ tail)) fragment0356975Acc00500 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment0356975Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0356975_object_field_005"
  err.flush

noncomputable def fragment0356975Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0356975Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '4', '3', '2', '7', '9', '7', '2', '0', '2', '3', '5', '0', '2', '6', '3', '6', '4', '2', '9', '1', '1', '7', '4', '7', '0', '0', '1', '7', '1', '2', '0', '0', '4', '9', '5', '8', '3', '2', '7', '2', '9', '6', '0', '0', '0', '0', '/', '1', '2', '3', '9', '5', '2', '9', '1', '2', '9', '0', '4', '5', '4', '1', '7', '4', '0', '7', '6', '0', '8', '3', '8', '2', '0', '9', '1', '3', '9', '2', '0', '1', '6', '4', '6', '6', '1', '9', '2', '9', '4', '2', '2', '9', '8', '6', '9', '4', '4', '8', '0', '7', '5', '8', '6', '2', '7', '4', '2', '1', '5', '1'])
noncomputable def fragment0356975Acc00700 : List (String × SourceJson) := (fragment0356975Field006Key00, fragment0356975Field006Value00) :: fragment0356975Acc00600
noncomputable def fragment0356975Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '4', '3', '2', '7', '9', '7', '2', '0', '2', '3', '5', '0', '2', '6', '3', '6', '4', '2', '9', '1', '1', '7', '4', '7', '0', '0', '1', '7', '1', '2', '0', '0', '4', '9', '5', '8', '3', '2', '7', '2', '9', '6', '0', '0', '0', '0', '/', '1', '2', '3', '9', '5', '2', '9', '1', '2', '9', '0', '4', '5', '4', '1', '7', '4', '0', '7', '6', '0', '8', '3', '8', '2', '0', '9', '1', '3', '9', '2', '0', '1', '6', '4', '6', '6', '1', '9', '2', '9', '4', '2', '2', '9', '8', '6', '9', '4', '4', '8', '0', '7', '5', '8', '6', '2', '7', '4', '2', '1', '5', '1', '"', ',']

theorem object_fragment0356975_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0356975Field006Chars00 ++ tail)) fragment0356975Acc00600 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0356975Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0356975_object_field_006"
  err.flush

noncomputable def fragment0356975Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0356975Field007Value00 : SourceJson := .str (String.ofList ['2', '1', '1', '6', '5', '8', '1', '4', '8', '5', '4', '3', '4', '0', '0', '0', '3', '0', '2', '0', '7', '2', '4', '9', '0', '5', '2', '1', '2', '8', '7', '7', '4', '0', '9', '0', '3', '4', '4', '0', '6', '2', '6', '5', '5', '2', '9', '3', '0', '8', '1', '6', '2', '6', '8', '3', '9', '0', '4', '7', '2', '3', '4', '5', '7', '1', '5', '2', '9', '9', '0', '4', '8', '2', '5', '0', '4', '5', '8', '0', '4', '3', '8', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '9', '1', '7', '2', '3', '5', '8', '9', '5', '6', '5', '0', '7', '0', '5', '9', '5', '6', '7', '8', '1', '5', '9', '2', '5', '1', '7', '8', '3', '8', '4', '5', '7', '4', '8', '2', '0', '9', '4', '8', '0', '0', '0', '9', '2', '7', '0', '3', '6', '0', '2', '4', '2', '2', '3', '2', '6', '5', '5', '5', '7', '9', '7', '7', '3', '7', '2', '1', '5', '2', '1', '6', '0', '7', '5', '1', '8', '9', '9', '8', '4', '7', '1', '9', '4', '8', '4', '9', '8', '7', '7', '0', '8', '5', '8', '8', '7', '2', '3', '8', '6', '0', '0', '8', '1', '6', '5', '9', '4', '3', '3'])
noncomputable def fragment0356975Acc00800 : List (String × SourceJson) := (fragment0356975Field007Key00, fragment0356975Field007Value00) :: fragment0356975Acc00700
noncomputable def fragment0356975Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '1', '6', '5', '8', '1', '4', '8', '5', '4', '3', '4', '0', '0', '0', '3', '0', '2', '0', '7', '2', '4', '9', '0', '5', '2', '1', '2', '8', '7', '7', '4', '0', '9', '0', '3', '4', '4', '0', '6', '2', '6', '5', '5', '2', '9', '3', '0', '8', '1', '6', '2', '6', '8', '3', '9', '0', '4', '7', '2', '3', '4', '5', '7', '1', '5', '2', '9', '9', '0', '4', '8', '2', '5', '0', '4', '5', '8', '0', '4', '3', '8', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '9', '1', '7', '2', '3', '5', '8', '9', '5', '6', '5', '0', '7', '0', '5', '9', '5', '6', '7', '8', '1', '5', '9', '2', '5', '1', '7', '8', '3', '8', '4', '5', '7', '4', '8', '2', '0', '9', '4', '8', '0', '0', '0', '9', '2', '7', '0', '3', '6', '0', '2', '4', '2', '2', '3', '2', '6', '5', '5', '5', '7', '9', '7', '7', '3', '7', '2', '1', '5', '2', '1', '6', '0', '7', '5', '1', '8', '9', '9', '8', '4', '7', '1', '9', '4', '8', '4', '9', '8', '7', '7', '0', '8', '5', '8', '8', '7', '2', '3', '8', '6', '0', '0', '8', '1', '6', '5', '9', '4', '3', '3', '"', ',']

theorem object_fragment0356975_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0356975Field007Chars00 ++ tail)) fragment0356975Acc00700 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment0356975Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0356975_object_field_007"
  err.flush

noncomputable def fragment0356975Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0356975Field008Value00 : SourceJson := .str (String.ofList ['1', '1', '7', '8', '1', '8', '6', '6', '3', '4', '0', '3', '6', '5', '5'])
noncomputable def fragment0356975Acc00900 : List (String × SourceJson) := (fragment0356975Field008Key00, fragment0356975Field008Value00) :: fragment0356975Acc00800
noncomputable def fragment0356975Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '7', '8', '1', '8', '6', '6', '3', '4', '0', '3', '6', '5', '5', '"', ',']

theorem object_fragment0356975_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0356975Field008Chars00 ++ tail)) fragment0356975Acc00800 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment0356975Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0356975_object_field_008"
  err.flush

noncomputable def fragment0356975Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0356975Field009Value00 : SourceJson := .str (String.ofList ['8', '8', '6', '4', '5', '5', '4', '1', '4', '6', '6', '8', '7', '0', '7'])
noncomputable def fragment0356975Acc01000 : List (String × SourceJson) := (fragment0356975Field009Key00, fragment0356975Field009Value00) :: fragment0356975Acc00900
noncomputable def fragment0356975Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '8', '6', '4', '5', '5', '4', '1', '4', '6', '6', '8', '7', '0', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0356975_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment0356975Field009Chars00 ++ tail)) fragment0356975Acc00900 =
      .ok (.obj (fragment0356975Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0356975_object_field_009"
  err.flush

noncomputable def fragment0356975Chars : List Char := '{' :: (fragment0356975Field000Chars00 ++ fragment0356975Field001Chars00 ++ fragment0356975Field002Chars00 ++ fragment0356975Field003Chars00 ++ fragment0356975Field004Chars00 ++ fragment0356975Field005Chars00 ++ fragment0356975Field006Chars00 ++ fragment0356975Field007Chars00 ++ fragment0356975Field008Chars00 ++ fragment0356975Field009Chars00)
noncomputable def fragment0356975Value : SourceJson := .obj (fragment0356975Acc01000.reverse)

theorem value_fragment0356975 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 224) (fragment0356975Chars ++ tail) =
      .ok (fragment0356975Value, tail) := by
  have hinput : fragment0356975Chars ++ tail = '{' :: (fragment0356975Field000Chars00 ++ (fragment0356975Field001Chars00 ++ (fragment0356975Field002Chars00 ++ (fragment0356975Field003Chars00 ++ (fragment0356975Field004Chars00 ++ (fragment0356975Field005Chars00 ++ (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0356975Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 224) (fragment0356975Chars ++ tail) =
        SourceJson.value (fuel + 224) ('{' :: (fragment0356975Field000Chars00 ++ (fragment0356975Field001Chars00 ++ (fragment0356975Field002Chars00 ++ (fragment0356975Field003Chars00 ++ (fragment0356975Field004Chars00 ++ (fragment0356975Field005Chars00 ++ (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 224)) hinput
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0356975Field000Chars00 ++ (fragment0356975Field001Chars00 ++ (fragment0356975Field002Chars00 ++ (fragment0356975Field003Chars00 ++ (fragment0356975Field004Chars00 ++ (fragment0356975Field005Chars00 ++ (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail)))))))))))) fragment0356975Acc00000 := by rfl
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment0356975Field001Chars00 ++ (fragment0356975Field002Chars00 ++ (fragment0356975Field003Chars00 ++ (fragment0356975Field004Chars00 ++ (fragment0356975Field005Chars00 ++ (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail))))))))))) fragment0356975Acc00100 := object_fragment0356975_field_000 fuel (fragment0356975Field001Chars00 ++ (fragment0356975Field002Chars00 ++ (fragment0356975Field003Chars00 ++ (fragment0356975Field004Chars00 ++ (fragment0356975Field005Chars00 ++ (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 221) (SourceJson.white (fragment0356975Field002Chars00 ++ (fragment0356975Field003Chars00 ++ (fragment0356975Field004Chars00 ++ (fragment0356975Field005Chars00 ++ (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail)))))))))) fragment0356975Acc00200 := object_fragment0356975_field_001 fuel (fragment0356975Field002Chars00 ++ (fragment0356975Field003Chars00 ++ (fragment0356975Field004Chars00 ++ (fragment0356975Field005Chars00 ++ (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment0356975Field003Chars00 ++ (fragment0356975Field004Chars00 ++ (fragment0356975Field005Chars00 ++ (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail))))))))) fragment0356975Acc00300 := object_fragment0356975_field_002 fuel (fragment0356975Field003Chars00 ++ (fragment0356975Field004Chars00 ++ (fragment0356975Field005Chars00 ++ (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 219) (SourceJson.white (fragment0356975Field004Chars00 ++ (fragment0356975Field005Chars00 ++ (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail)))))))) fragment0356975Acc00400 := object_fragment0356975_field_003 fuel (fragment0356975Field004Chars00 ++ (fragment0356975Field005Chars00 ++ (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0356975Field005Chars00 ++ (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail))))))) fragment0356975Acc00500 := object_fragment0356975_field_004 fuel (fragment0356975Field005Chars00 ++ (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail)))))) fragment0356975Acc00600 := object_fragment0356975_field_005 fuel (fragment0356975Field006Chars00 ++ (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail))))) fragment0356975Acc00700 := object_fragment0356975_field_006 fuel (fragment0356975Field007Chars00 ++ (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail)))) fragment0356975Acc00800 := object_fragment0356975_field_007 fuel (fragment0356975Field008Chars00 ++ (fragment0356975Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment0356975Field009Chars00 ++ (tail))) fragment0356975Acc00900 := object_fragment0356975_field_008 fuel (fragment0356975Field009Chars00 ++ (tail))
    _ = .ok (fragment0356975Value, tail) := object_fragment0356975_field_009 fuel (tail)

noncomputable def fragment0358531Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0358531Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0358531Field000Value00 : SourceJson := .number (String.ofList ['7', '8'])
noncomputable def fragment0358531Acc00100 : List (String × SourceJson) := (fragment0358531Field000Key00, fragment0358531Field000Value00) :: fragment0358531Acc00000
noncomputable def fragment0358531Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '8', ',']

theorem object_fragment0358531_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 367) (SourceJson.white (fragment0358531Field000Chars00 ++ tail)) fragment0358531Acc00000 =
      SourceJson.object (fuel + 366) (SourceJson.white tail) fragment0358531Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0358531_object_field_000"
  err.flush

noncomputable def fragment0358531Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0358531Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0358531Acc00200 : List (String × SourceJson) := (fragment0358531Field001Key00, fragment0358531Field001Value00) :: fragment0358531Acc00100
noncomputable def fragment0358531Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0358531_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 366) (SourceJson.white (fragment0358531Field001Chars00 ++ tail)) fragment0358531Acc00100 =
      SourceJson.object (fuel + 365) (SourceJson.white tail) fragment0358531Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0358531_object_field_001"
  err.flush

noncomputable def fragment0358531Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0358531Field002Value00 : SourceJson := .str (String.ofList ['4', '2', '7', '4', '9', '0', '6', '1', '5', '5', '5', '2', '0', '4', '3', '7', '0', '8', '2', '7', '2', '7', '6', '7', '5', '9', '4', '6', '3', '8', '0', '2', '8', '5', '6', '5', '1', '1', '/', '2', '5', '7', '1', '9', '2', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0358531Acc00300 : List (String × SourceJson) := (fragment0358531Field002Key00, fragment0358531Field002Value00) :: fragment0358531Acc00200
noncomputable def fragment0358531Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '2', '7', '4', '9', '0', '6', '1', '5', '5', '5', '2', '0', '4', '3', '7', '0', '8', '2', '7', '2', '7', '6', '7', '5', '9', '4', '6', '3', '8', '0', '2', '8', '5', '6', '5', '1', '1', '/', '2', '5', '7', '1', '9', '2', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0358531_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 365) (SourceJson.white (fragment0358531Field002Chars00 ++ tail)) fragment0358531Acc00200 =
      SourceJson.object (fuel + 364) (SourceJson.white tail) fragment0358531Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0358531_object_field_002"
  err.flush

noncomputable def fragment0358531Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0358531Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '4', '0', '2', '3', '/', '9', '3', '7', '1', '2', '5', '0', '0', '0'])
noncomputable def fragment0358531Acc00400 : List (String × SourceJson) := (fragment0358531Field003Key00, fragment0358531Field003Value00) :: fragment0358531Acc00300
noncomputable def fragment0358531Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '7', '4', '0', '2', '3', '/', '9', '3', '7', '1', '2', '5', '0', '0', '0', '"', ',']

theorem object_fragment0358531_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 364) (SourceJson.white (fragment0358531Field003Chars00 ++ tail)) fragment0358531Acc00300 =
      SourceJson.object (fuel + 363) (SourceJson.white tail) fragment0358531Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0358531_object_field_003"
  err.flush

noncomputable def fragment0358531Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0358531Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0358531Acc00500 : List (String × SourceJson) := (fragment0358531Field004Key00, fragment0358531Field004Value00) :: fragment0358531Acc00400
noncomputable def fragment0358531Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0358531_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 363) (SourceJson.white (fragment0358531Field004Chars00 ++ tail)) fragment0358531Acc00400 =
      SourceJson.object (fuel + 362) (SourceJson.white tail) fragment0358531Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0358531_object_field_004"
  err.flush

noncomputable def fragment0358531Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0358531Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '6', '4', '8', '6', '3', '2', '6', '4', '5', '5', '9', '1', '5', '6', '1', '3', '/', '2', '8', '8', '6', '2', '8', '6', '4', '4', '9', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '9', '8', '5', '7', '4', '1', '5', '2', '8', '6', '9', '4', '3', '7', '5', '0', '3', '/', '7', '0', '7', '1', '4', '0', '1', '8', '0', '0', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '3', '3', '1', '9', '3', '8', '9', '7', '6', '6', '0', '0', '5', '8', '9', '5', '7', '/', '1', '6', '3', '1', '8', '6', '1', '9', '5', '4', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '8', '7', '1', '7', '3', '0', '2', '6', '7', '2', '1', '4', '3', '0', '7', '5', '2', '1', '/', '3', '1', '8', '2', '1', '3', '0', '8', '1', '0', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '5', '2', '0', '6', '5', '5', '8', '1', '6', '2', '3', '0', '6', '9', '5', '3', '/', '4', '1', '5', '9', '6', '4', '8', '1', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '0', '5', '2', '9', '2', '9', '1', '8', '5', '9', '6', '0', '2', '9', '7', '4', '7', '/', '2', '1', '2', '1', '4', '2', '0', '5', '4', '0', '2', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '1', '2', '3', '2', '0', '1', '6', '1', '8', '8', '4', '7', '6', '5', '1', '5', '6', '1', '/', '6', '3', '6', '4', '2', '6', '1', '6', '2', '0', '6', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '2', '1', '0', '0', '8', '1', '1', '8', '9', '8', '4', '7', '0', '5', '8', '1', '7', '/', '6', '3', '6', '4', '2', '6', '1', '6', '2', '0', '6', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '5', '5', '9', '2', '2', '7', '7', '3', '6', '7', '6', '7', '1', '0', '4', '3', '3', '9', '/', '6', '3', '6', '4', '2', '6', '1', '6', '2', '0', '6', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '4', '4', '4', '0', '1', '8', '8', '1', '5', '3', '9', '9', '6', '7', '6', '9', '7', '/', '1', '2', '7', '2', '8', '5', '2', '3', '2', '4', '1', '3', '2', '4', '8', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0358531Acc00600 : List (String × SourceJson) := (fragment0358531Field005Key00, fragment0358531Field005Value00) :: fragment0358531Acc00500
noncomputable def fragment0358531Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '8', '6', '3', '2', '6', '4', '5', '5', '9', '1', '5', '6', '1', '3', '/', '2', '8', '8', '6', '2', '8', '6', '4', '4', '9', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '9', '8', '5', '7', '4', '1', '5', '2', '8', '6', '9', '4', '3', '7', '5', '0', '3', '/', '7', '0', '7', '1', '4', '0', '1', '8', '0', '0', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '3', '3', '1', '9', '3', '8', '9', '7', '6', '6', '0', '0', '5', '8', '9', '5', '7', '/', '1', '6', '3', '1', '8', '6', '1', '9', '5', '4', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '8', '7', '1', '7', '3', '0', '2', '6', '7', '2', '1', '4', '3', '0', '7', '5', '2', '1', '/', '3', '1', '8', '2', '1', '3', '0', '8', '1', '0', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '5', '2', '0', '6', '5', '5', '8', '1', '6', '2', '3', '0', '6', '9', '5', '3', '/', '4', '1', '5', '9', '6', '4', '8', '1', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '0', '5', '2', '9', '2', '9', '1', '8', '5', '9', '6', '0', '2', '9', '7', '4', '7', '/', '2', '1', '2', '1', '4', '2', '0', '5', '4', '0', '2', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '1', '2', '3', '2', '0', '1', '6', '1', '8', '8', '4', '7', '6', '5', '1', '5', '6', '1', '/', '6', '3', '6', '4', '2', '6', '1', '6', '2', '0', '6', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '2', '1', '0', '0', '8', '1', '1', '8', '9', '8', '4', '7', '0', '5', '8', '1', '7', '/', '6', '3', '6', '4', '2', '6', '1', '6', '2', '0', '6', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '5', '5', '9', '2', '2', '7', '7', '3', '6', '7', '6', '7', '1', '0', '4', '3', '3', '9', '/', '6', '3', '6', '4', '2', '6', '1', '6', '2', '0', '6', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '4', '4', '4', '0', '1', '8', '8', '1', '5', '3', '9', '9', '6', '7', '6', '9', '7', '/', '1', '2', '7', '2', '8', '5', '2', '3', '2', '4', '1', '3', '2', '4', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0358531_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 362) (SourceJson.white (fragment0358531Field005Chars00 ++ tail)) fragment0358531Acc00500 =
      SourceJson.object (fuel + 361) (SourceJson.white tail) fragment0358531Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0358531_object_field_005"
  err.flush

noncomputable def fragment0358531Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0358531Field006Value00 : SourceJson := .str (String.ofList ['4', '8', '4', '9', '3', '0', '2', '5', '5', '6', '4', '5', '9', '1', '8', '3', '6', '2', '8', '5', '2', '7', '2', '5', '3', '3', '2', '7', '7', '7', '9', '1', '6', '3', '7', '6', '9', '2', '4', '8', '4', '6', '5', '1', '3', '9', '7', '1', '2', '0', '0', '0', '0', '0', '/', '3', '0', '6', '4', '9', '3', '4', '5', '1', '8', '9', '4', '0', '8', '3', '3', '0', '2', '3', '7', '8', '8', '7', '5', '5', '7', '6', '8', '3', '8', '1', '3', '5', '9', '3', '8', '9', '6', '9', '5', '6', '8', '3', '5', '7', '9', '4', '1', '2', '1', '7', '1', '4', '7', '5', '6', '0', '4', '1', '9', '1', '1', '6', '2', '3'])
noncomputable def fragment0358531Acc00700 : List (String × SourceJson) := (fragment0358531Field006Key00, fragment0358531Field006Value00) :: fragment0358531Acc00600
noncomputable def fragment0358531Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '8', '4', '9', '3', '0', '2', '5', '5', '6', '4', '5', '9', '1', '8', '3', '6', '2', '8', '5', '2', '7', '2', '5', '3', '3', '2', '7', '7', '7', '9', '1', '6', '3', '7', '6', '9', '2', '4', '8', '4', '6', '5', '1', '3', '9', '7', '1', '2', '0', '0', '0', '0', '0', '/', '3', '0', '6', '4', '9', '3', '4', '5', '1', '8', '9', '4', '0', '8', '3', '3', '0', '2', '3', '7', '8', '8', '7', '5', '5', '7', '6', '8', '3', '8', '1', '3', '5', '9', '3', '8', '9', '6', '9', '5', '6', '8', '3', '5', '7', '9', '4', '1', '2', '1', '7', '1', '4', '7', '5', '6', '0', '4', '1', '9', '1', '1', '6', '2', '3', '"', ',']

theorem object_fragment0358531_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 361) (SourceJson.white (fragment0358531Field006Chars00 ++ tail)) fragment0358531Acc00600 =
      SourceJson.object (fuel + 360) (SourceJson.white tail) fragment0358531Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0358531_object_field_006"
  err.flush

noncomputable def fragment0358531Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0358531Field007Value00 : SourceJson := .str (String.ofList ['6', '7', '7', '5', '6', '4', '7', '2', '9', '6', '2', '3', '8', '2', '2', '2', '3', '2', '7', '7', '1', '4', '1', '1', '2', '8', '3', '9', '0', '0', '9', '5', '9', '2', '4', '9', '7', '5', '7', '9', '4', '6', '8', '9', '2', '3', '4', '4', '7', '2', '9', '5', '1', '7', '8', '3', '9', '2', '9', '5', '6', '7', '8', '5', '0', '9', '1', '3', '1', '5', '7', '1', '3', '2', '1', '9', '9', '8', '2', '7', '7', '6', '2', '6', '7', '7', '6', '0', '5', '5', '1', '3', '0', '1', '0', '1', '0', '4', '1', '7', '2', '7', '5', '4', '7', '4', '4', '7', '5', '0', '7', '6', '9', '4', '6', '2', '9', '8', '4', '0', '7', '4', '5', '0', '9', '4', '9', '5', '6', '7', '3', '0', '2', '8', '6', '4', '1', '8', '4', '6', '1', '1', '9', '3', '7', '2', '3', '2', '0', '9', '8', '1', '3', '3', '2', '7', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '4', '8', '4', '6', '0', '7', '4', '2', '2', '6', '7', '3', '3', '3', '7', '6', '7', '5', '5', '0', '8', '7', '6', '4', '5', '3', '0', '0', '6', '8', '5', '6', '9', '7', '6', '1', '9', '5', '7', '2', '3', '4', '5', '4', '6', '6', '7', '2', '2', '8', '4', '4', '5', '0', '7', '9', '0', '9', '3', '7', '4', '0', '6', '5', '8', '1', '6', '4', '9', '9', '4', '0', '5', '8', '8', '1', '7', '8', '8', '5', '0', '3', '1', '5', '1', '5', '5', '8', '9', '8', '6', '4', '6', '7', '5', '0', '5', '7', '2', '2', '6', '2', '2', '0', '2', '0', '4', '4', '3', '8', '4', '6', '7', '7', '6', '1', '0', '0', '1', '7', '5', '5', '1', '9', '5', '7', '3', '9', '7', '3', '8', '8', '7', '1', '8', '0', '0', '5', '4', '8', '6', '6', '0', '4', '0', '9', '9', '4', '3', '2', '4', '2', '4', '0', '2', '1', '9', '9', '1', '6', '0', '3', '2', '5', '2', '5', '6', '3', '1', '8', '5', '2', '9', '2', '5', '1', '7', '4', '7', '0', '1', '3'])
noncomputable def fragment0358531Acc00800 : List (String × SourceJson) := (fragment0358531Field007Key00, fragment0358531Field007Value00) :: fragment0358531Acc00700
noncomputable def fragment0358531Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '7', '7', '5', '6', '4', '7', '2', '9', '6', '2', '3', '8', '2', '2', '2', '3', '2', '7', '7', '1', '4', '1', '1', '2', '8', '3', '9', '0', '0', '9', '5', '9', '2', '4', '9', '7', '5', '7', '9', '4', '6', '8', '9', '2', '3', '4', '4', '7', '2', '9', '5', '1', '7', '8', '3', '9', '2', '9', '5', '6', '7', '8', '5', '0', '9', '1', '3', '1', '5', '7', '1', '3', '2', '1', '9', '9', '8', '2', '7', '7', '6', '2', '6', '7', '7', '6', '0', '5', '5', '1', '3', '0', '1', '0', '1', '0', '4', '1', '7', '2', '7', '5', '4', '7', '4', '4', '7', '5', '0', '7', '6', '9', '4', '6', '2', '9', '8', '4', '0', '7', '4', '5', '0', '9', '4', '9', '5', '6', '7', '3', '0', '2', '8', '6', '4', '1', '8', '4', '6', '1', '1', '9', '3', '7', '2', '3', '2', '0', '9', '8', '1', '3', '3', '2', '7', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '4', '8', '4', '6', '0', '7', '4', '2', '2', '6', '7', '3', '3', '3', '7', '6', '7', '5', '5', '0', '8', '7', '6', '4', '5', '3', '0', '0', '6', '8', '5', '6', '9', '7', '6', '1', '9', '5', '7', '2', '3', '4', '5', '4', '6', '6', '7', '2', '2', '8', '4', '4', '5', '0', '7', '9', '0', '9', '3', '7', '4', '0', '6', '5', '8', '1', '6', '4', '9', '9', '4', '0', '5', '8', '8', '1', '7', '8', '8', '5', '0', '3', '1', '5', '1', '5', '5', '8', '9', '8', '6', '4', '6', '7', '5', '0', '5', '7', '2', '2', '6', '2', '2', '0', '2', '0', '4', '4', '3', '8', '4', '6', '7', '7', '6', '1', '0', '0', '1', '7', '5', '5', '1', '9', '5', '7', '3', '9', '7', '3', '8', '8', '7', '1', '8', '0', '0', '5', '4', '8', '6', '6', '0', '4', '0', '9', '9', '4', '3', '2', '4', '2', '4', '0', '2', '1', '9', '9', '1', '6', '0', '3', '2', '5', '2', '5', '6', '3', '1', '8', '5', '2', '9', '2', '5', '1', '7', '4', '7', '0', '1', '3', '"', ',']

theorem object_fragment0358531_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 360) (SourceJson.white (fragment0358531Field007Chars00 ++ tail)) fragment0358531Acc00700 =
      SourceJson.object (fuel + 359) (SourceJson.white tail) fragment0358531Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0358531_object_field_007"
  err.flush

noncomputable def fragment0358531Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0358531Field008Value00 : SourceJson := .str (String.ofList ['1', '2', '5', '3', '5', '3', '8', '4', '6', '4', '3', '6', '0', '9', '1', '6', '8', '1', '4'])
noncomputable def fragment0358531Acc00900 : List (String × SourceJson) := (fragment0358531Field008Key00, fragment0358531Field008Value00) :: fragment0358531Acc00800
noncomputable def fragment0358531Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '5', '3', '5', '3', '8', '4', '6', '4', '3', '6', '0', '9', '1', '6', '8', '1', '4', '"', ',']

theorem object_fragment0358531_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 359) (SourceJson.white (fragment0358531Field008Chars00 ++ tail)) fragment0358531Acc00800 =
      SourceJson.object (fuel + 358) (SourceJson.white tail) fragment0358531Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0358531_object_field_008"
  err.flush

noncomputable def fragment0358531Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0358531Field009Value00 : SourceJson := .str (String.ofList ['9', '7', '8', '7', '7', '9', '4', '1', '6', '2', '0', '1', '1', '9', '9', '7', '7', '3', '0'])
noncomputable def fragment0358531Acc01000 : List (String × SourceJson) := (fragment0358531Field009Key00, fragment0358531Field009Value00) :: fragment0358531Acc00900
noncomputable def fragment0358531Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '7', '8', '7', '7', '9', '4', '1', '6', '2', '0', '1', '1', '9', '9', '7', '7', '3', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0358531_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 358) (SourceJson.white (fragment0358531Field009Chars00 ++ tail)) fragment0358531Acc00900 =
      .ok (.obj (fragment0358531Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0358531_object_field_009"
  err.flush

noncomputable def fragment0358531Chars : List Char := '{' :: (fragment0358531Field000Chars00 ++ fragment0358531Field001Chars00 ++ fragment0358531Field002Chars00 ++ fragment0358531Field003Chars00 ++ fragment0358531Field004Chars00 ++ fragment0358531Field005Chars00 ++ fragment0358531Field006Chars00 ++ fragment0358531Field007Chars00 ++ fragment0358531Field008Chars00 ++ fragment0358531Field009Chars00)
noncomputable def fragment0358531Value : SourceJson := .obj (fragment0358531Acc01000.reverse)

theorem value_fragment0358531 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 368) (fragment0358531Chars ++ tail) =
      .ok (fragment0358531Value, tail) := by
  have hinput : fragment0358531Chars ++ tail = '{' :: (fragment0358531Field000Chars00 ++ (fragment0358531Field001Chars00 ++ (fragment0358531Field002Chars00 ++ (fragment0358531Field003Chars00 ++ (fragment0358531Field004Chars00 ++ (fragment0358531Field005Chars00 ++ (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0358531Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 368) (fragment0358531Chars ++ tail) =
        SourceJson.value (fuel + 368) ('{' :: (fragment0358531Field000Chars00 ++ (fragment0358531Field001Chars00 ++ (fragment0358531Field002Chars00 ++ (fragment0358531Field003Chars00 ++ (fragment0358531Field004Chars00 ++ (fragment0358531Field005Chars00 ++ (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 368)) hinput
    _ = SourceJson.object (fuel + 367) (SourceJson.white (fragment0358531Field000Chars00 ++ (fragment0358531Field001Chars00 ++ (fragment0358531Field002Chars00 ++ (fragment0358531Field003Chars00 ++ (fragment0358531Field004Chars00 ++ (fragment0358531Field005Chars00 ++ (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail)))))))))))) fragment0358531Acc00000 := by rfl
    _ = SourceJson.object (fuel + 366) (SourceJson.white (fragment0358531Field001Chars00 ++ (fragment0358531Field002Chars00 ++ (fragment0358531Field003Chars00 ++ (fragment0358531Field004Chars00 ++ (fragment0358531Field005Chars00 ++ (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail))))))))))) fragment0358531Acc00100 := object_fragment0358531_field_000 fuel (fragment0358531Field001Chars00 ++ (fragment0358531Field002Chars00 ++ (fragment0358531Field003Chars00 ++ (fragment0358531Field004Chars00 ++ (fragment0358531Field005Chars00 ++ (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 365) (SourceJson.white (fragment0358531Field002Chars00 ++ (fragment0358531Field003Chars00 ++ (fragment0358531Field004Chars00 ++ (fragment0358531Field005Chars00 ++ (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail)))))))))) fragment0358531Acc00200 := object_fragment0358531_field_001 fuel (fragment0358531Field002Chars00 ++ (fragment0358531Field003Chars00 ++ (fragment0358531Field004Chars00 ++ (fragment0358531Field005Chars00 ++ (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 364) (SourceJson.white (fragment0358531Field003Chars00 ++ (fragment0358531Field004Chars00 ++ (fragment0358531Field005Chars00 ++ (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail))))))))) fragment0358531Acc00300 := object_fragment0358531_field_002 fuel (fragment0358531Field003Chars00 ++ (fragment0358531Field004Chars00 ++ (fragment0358531Field005Chars00 ++ (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 363) (SourceJson.white (fragment0358531Field004Chars00 ++ (fragment0358531Field005Chars00 ++ (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail)))))))) fragment0358531Acc00400 := object_fragment0358531_field_003 fuel (fragment0358531Field004Chars00 ++ (fragment0358531Field005Chars00 ++ (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 362) (SourceJson.white (fragment0358531Field005Chars00 ++ (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail))))))) fragment0358531Acc00500 := object_fragment0358531_field_004 fuel (fragment0358531Field005Chars00 ++ (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 361) (SourceJson.white (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail)))))) fragment0358531Acc00600 := object_fragment0358531_field_005 fuel (fragment0358531Field006Chars00 ++ (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 360) (SourceJson.white (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail))))) fragment0358531Acc00700 := object_fragment0358531_field_006 fuel (fragment0358531Field007Chars00 ++ (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 359) (SourceJson.white (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail)))) fragment0358531Acc00800 := object_fragment0358531_field_007 fuel (fragment0358531Field008Chars00 ++ (fragment0358531Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 358) (SourceJson.white (fragment0358531Field009Chars00 ++ (tail))) fragment0358531Acc00900 := object_fragment0358531_field_008 fuel (fragment0358531Field009Chars00 ++ (tail))
    _ = .ok (fragment0358531Value, tail) := object_fragment0358531_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0077_before_reader"
  err.flush

noncomputable def chunk0077LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0077SuffixChars00 : List Char := [',']
noncomputable def chunk0077Chars00 : List Char := chunk0077LeadChars00 ++ fragment0356975Chars ++ chunk0077SuffixChars00
noncomputable def chunk0077Push00 (acc : List SourceJson) : List SourceJson := fragment0356975Value :: acc

noncomputable def chunk0077AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0077_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 527)
      (SourceJson.white (chunk0077LeadChars00 ++ (fragment0356975Chars ++ rest))) acc =
      (SourceJson.value (fuel + 526) (fragment0356975Chars ++ rest)).bind
        (chunk0077AfterValue00 (fuel + 526) acc) := by rfl

theorem array_chunk0077 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 527) (SourceJson.white (chunk0077Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 526) (SourceJson.white tail) (chunk0077Push00 acc) := by
  have hinput : chunk0077Chars00 ++ tail = chunk0077LeadChars00 ++ (fragment0356975Chars ++ (chunk0077SuffixChars00 ++ tail)) := by
    simp only [chunk0077Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 527) (SourceJson.white (chunk0077Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 527)
          (SourceJson.white (chunk0077LeadChars00 ++ (fragment0356975Chars ++ (chunk0077SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 527) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 526) (fragment0356975Chars ++ (chunk0077SuffixChars00 ++ tail))).bind
        (chunk0077AfterValue00 (fuel + 526) acc) := array_chunk0077_head fuel (chunk0077SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0356975Value, chunk0077SuffixChars00 ++ tail)).bind
        (chunk0077AfterValue00 (fuel + 526) acc) :=
      congrArg (fun result => result.bind (chunk0077AfterValue00 (fuel + 526) acc))
        (value_fragment0356975 (fuel + 302) (chunk0077SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 526) (SourceJson.white tail) (chunk0077Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0077_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0078_before_reader"
  err.flush

noncomputable def chunk0078LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0078SuffixChars00 : List Char := [',']
noncomputable def chunk0078Chars00 : List Char := chunk0078LeadChars00 ++ fragment0358531Chars ++ chunk0078SuffixChars00
noncomputable def chunk0078Push00 (acc : List SourceJson) : List SourceJson := fragment0358531Value :: acc

noncomputable def chunk0078AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0078_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 526)
      (SourceJson.white (chunk0078LeadChars00 ++ (fragment0358531Chars ++ rest))) acc =
      (SourceJson.value (fuel + 525) (fragment0358531Chars ++ rest)).bind
        (chunk0078AfterValue00 (fuel + 525) acc) := by rfl

theorem array_chunk0078 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 526) (SourceJson.white (chunk0078Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 525) (SourceJson.white tail) (chunk0078Push00 acc) := by
  have hinput : chunk0078Chars00 ++ tail = chunk0078LeadChars00 ++ (fragment0358531Chars ++ (chunk0078SuffixChars00 ++ tail)) := by
    simp only [chunk0078Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 526) (SourceJson.white (chunk0078Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 526)
          (SourceJson.white (chunk0078LeadChars00 ++ (fragment0358531Chars ++ (chunk0078SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 526) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 525) (fragment0358531Chars ++ (chunk0078SuffixChars00 ++ tail))).bind
        (chunk0078AfterValue00 (fuel + 525) acc) := array_chunk0078_head fuel (chunk0078SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0358531Value, chunk0078SuffixChars00 ++ tail)).bind
        (chunk0078AfterValue00 (fuel + 525) acc) :=
      congrArg (fun result => result.bind (chunk0078AfterValue00 (fuel + 525) acc))
        (value_fragment0358531 (fuel + 157) (chunk0078SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 525) (SourceJson.white tail) (chunk0078Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0078_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0077Chars00 ++ chunk0078Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0078Push00 (chunk0077Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 527) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 525) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0077Chars00 ++ (chunk0078Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 527) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 527) (SourceJson.white (chunk0077Chars00 ++ (chunk0078Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 527) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 526) (SourceJson.white (chunk0078Chars00 ++ (tail))) (chunk0077Push00 (acc)) := array_chunk0077 fuel (chunk0078Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 525) (SourceJson.white tail) (blockPush acc) := array_chunk0078 fuel (tail) (chunk0077Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 356969).take 3434 = blockChars := by rfl

theorem block_original_split : sourceRest 356969 = blockChars ++ sourceRest 360403 := by
  calc
    sourceRest 356969 = (sourceRest 356969).take 3434 ++ (sourceRest 356969).drop 3434 :=
      (List.take_append_drop 3434 (sourceRest 356969)).symm
    _ = blockChars ++ (sourceRest 356969).drop 3434 :=
      congrArg (fun part => part ++ (sourceRest 356969).drop 3434) block_original_prefix
    _ = blockChars ++ sourceRest 360403 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 356969 3434)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 527) (SourceJson.white (sourceRest 356969)) acc =
      SourceJson.array (fuel + 525) (SourceJson.white (sourceRest 360403)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 527) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 360403) acc)

#print axioms object_fragment0356975_field_000
#print axioms object_fragment0356975_field_001
#print axioms object_fragment0356975_field_002
#print axioms object_fragment0356975_field_003
#print axioms object_fragment0356975_field_004
#print axioms object_fragment0356975_field_005
#print axioms object_fragment0356975_field_006
#print axioms object_fragment0356975_field_007
#print axioms object_fragment0356975_field_008
#print axioms object_fragment0356975_field_009
#print axioms value_fragment0356975
#print axioms object_fragment0358531_field_000
#print axioms object_fragment0358531_field_001
#print axioms object_fragment0358531_field_002
#print axioms object_fragment0358531_field_003
#print axioms object_fragment0358531_field_004
#print axioms object_fragment0358531_field_005
#print axioms object_fragment0358531_field_006
#print axioms object_fragment0358531_field_007
#print axioms object_fragment0358531_field_008
#print axioms object_fragment0358531_field_009
#print axioms value_fragment0358531
#print axioms array_chunk0077_head
#print axioms array_chunk0077
#print axioms array_chunk0078_head
#print axioms array_chunk0078
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock039

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
