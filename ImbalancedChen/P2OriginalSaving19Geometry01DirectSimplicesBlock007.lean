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

namespace SimplicesBlock007

noncomputable def fragment0250165Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0250165Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0250165Field000Value00 : SourceJson := .number (String.ofList ['1', '4'])
noncomputable def fragment0250165Acc00100 : List (String × SourceJson) := (fragment0250165Field000Key00, fragment0250165Field000Value00) :: fragment0250165Acc00000
noncomputable def fragment0250165Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '4', ',']

theorem object_fragment0250165_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0250165Field000Chars00 ++ tail)) fragment0250165Acc00000 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0250165Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250165_object_field_000"
  err.flush

noncomputable def fragment0250165Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0250165Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0250165Acc00200 : List (String × SourceJson) := (fragment0250165Field001Key00, fragment0250165Field001Value00) :: fragment0250165Acc00100
noncomputable def fragment0250165Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0250165_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0250165Field001Chars00 ++ tail)) fragment0250165Acc00100 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0250165Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250165_object_field_001"
  err.flush

noncomputable def fragment0250165Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0250165Field002Value00 : SourceJson := .str (String.ofList ['4', '1', '7', '7', '5', '2', '8', '8', '8', '2', '3', '5', '5', '6', '4', '6', '6', '1', '6', '8', '6', '0', '6', '6', '4', '0', '7', '9', '8', '3', '3', '0', '9', '2', '5', '7', '7', '6', '3', '7', '/', '1', '3', '8', '7', '2', '6', '6', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0250165Acc00300 : List (String × SourceJson) := (fragment0250165Field002Key00, fragment0250165Field002Value00) :: fragment0250165Acc00200
noncomputable def fragment0250165Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '1', '7', '7', '5', '2', '8', '8', '8', '2', '3', '5', '5', '6', '4', '6', '6', '1', '6', '8', '6', '0', '6', '6', '4', '0', '7', '9', '8', '3', '3', '0', '9', '2', '5', '7', '7', '6', '3', '7', '/', '1', '3', '8', '7', '2', '6', '6', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0250165_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0250165Field002Chars00 ++ tail)) fragment0250165Acc00200 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0250165Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250165_object_field_002"
  err.flush

noncomputable def fragment0250165Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0250165Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0250165Acc00400 : List (String × SourceJson) := (fragment0250165Field003Key00, fragment0250165Field003Value00) :: fragment0250165Acc00300
noncomputable def fragment0250165Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0250165_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0250165Field003Chars00 ++ tail)) fragment0250165Acc00300 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0250165Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250165_object_field_003"
  err.flush

noncomputable def fragment0250165Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0250165Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0250165Acc00500 : List (String × SourceJson) := (fragment0250165Field004Key00, fragment0250165Field004Value00) :: fragment0250165Acc00400
noncomputable def fragment0250165Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0250165_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0250165Field004Chars00 ++ tail)) fragment0250165Acc00400 =
      SourceJson.object (fuel + 222) (SourceJson.white tail) fragment0250165Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250165_object_field_004"
  err.flush

noncomputable def fragment0250165Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0250165Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '7', '6', '1', '1', '6', '1', '8', '8', '3', '9', '/', '4', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '6', '4', '9', '8', '2', '5', '7', '7', '9', '3', '/', '3', '0', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '4', '9', '1', '5', '9', '4', '3', '1', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '0', '6', '3', '7', '2', '4', '1', '5', '4', '3', '/', '3', '0', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '4', '6', '4', '8', '1', '9', '7', '3', '7', '1', '/', '9', '1', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '0', '1', '6', '8', '5', '3', '6', '8', '9', '/', '4', '5', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '0', '5', '4', '5', '6', '2', '0', '8', '6', '3', '/', '3', '6', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '2', '4', '4', '1', '8', '9', '6', '7', '5', '3', '3', '/', '3', '6', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '2', '2', '4', '3', '8', '1', '6', '0', '5', '7', '/', '9', '1', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '6', '7', '9', '8', '9', '0', '2', '5', '2', '1', '/', '9', '1', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0250165Acc00600 : List (String × SourceJson) := (fragment0250165Field005Key00, fragment0250165Field005Value00) :: fragment0250165Acc00500
noncomputable def fragment0250165Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '6', '1', '1', '6', '1', '8', '8', '3', '9', '/', '4', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '6', '4', '9', '8', '2', '5', '7', '7', '9', '3', '/', '3', '0', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '4', '9', '1', '5', '9', '4', '3', '1', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '0', '6', '3', '7', '2', '4', '1', '5', '4', '3', '/', '3', '0', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '4', '6', '4', '8', '1', '9', '7', '3', '7', '1', '/', '9', '1', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '0', '0', '1', '6', '8', '5', '3', '6', '8', '9', '/', '4', '5', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '0', '5', '4', '5', '6', '2', '0', '8', '6', '3', '/', '3', '6', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '4', '4', '1', '8', '9', '6', '7', '5', '3', '3', '/', '3', '6', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '2', '2', '4', '3', '8', '1', '6', '0', '5', '7', '/', '9', '1', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '6', '7', '9', '8', '9', '0', '2', '5', '2', '1', '/', '9', '1', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0250165_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment0250165Field005Chars00 ++ tail)) fragment0250165Acc00500 =
      SourceJson.object (fuel + 221) (SourceJson.white tail) fragment0250165Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250165_object_field_005"
  err.flush

noncomputable def fragment0250165Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0250165Field006Value00 : SourceJson := .str (String.ofList ['3', '7', '4', '5', '4', '8', '5', '2', '1', '2', '7', '0', '8', '6', '1', '4', '8', '9', '9', '7', '0', '4', '3', '9', '7', '8', '0', '0', '1', '1', '9', '2', '9', '3', '4', '1', '8', '8', '2', '9', '4', '5', '3', '0', '8', '0', '0', '0', '0', '0', '/', '1', '9', '8', '5', '4', '8', '3', '7', '9', '7', '6', '0', '9', '4', '1', '3', '9', '1', '7', '3', '5', '2', '6', '7', '2', '4', '8', '1', '1', '0', '2', '7', '3', '2', '6', '1', '0', '9', '8', '8', '5', '0', '0', '7', '3', '9', '7', '9', '6', '5', '5', '5', '0', '7', '8', '9', '2', '4', '2', '1', '7'])
noncomputable def fragment0250165Acc00700 : List (String × SourceJson) := (fragment0250165Field006Key00, fragment0250165Field006Value00) :: fragment0250165Acc00600
noncomputable def fragment0250165Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '7', '4', '5', '4', '8', '5', '2', '1', '2', '7', '0', '8', '6', '1', '4', '8', '9', '9', '7', '0', '4', '3', '9', '7', '8', '0', '0', '1', '1', '9', '2', '9', '3', '4', '1', '8', '8', '2', '9', '4', '5', '3', '0', '8', '0', '0', '0', '0', '0', '/', '1', '9', '8', '5', '4', '8', '3', '7', '9', '7', '6', '0', '9', '4', '1', '3', '9', '1', '7', '3', '5', '2', '6', '7', '2', '4', '8', '1', '1', '0', '2', '7', '3', '2', '6', '1', '0', '9', '8', '8', '5', '0', '0', '7', '3', '9', '7', '9', '6', '5', '5', '5', '0', '7', '8', '9', '2', '4', '2', '1', '7', '"', ',']

theorem object_fragment0250165_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 221) (SourceJson.white (fragment0250165Field006Chars00 ++ tail)) fragment0250165Acc00600 =
      SourceJson.object (fuel + 220) (SourceJson.white tail) fragment0250165Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250165_object_field_006"
  err.flush

noncomputable def fragment0250165Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0250165Field007Value00 : SourceJson := .str (String.ofList ['4', '2', '0', '3', '2', '3', '6', '4', '2', '4', '9', '2', '7', '5', '9', '1', '9', '2', '2', '5', '8', '5', '0', '2', '4', '1', '5', '4', '7', '3', '7', '6', '4', '0', '5', '4', '9', '0', '3', '1', '7', '5', '4', '9', '8', '8', '3', '9', '7', '9', '3', '1', '9', '8', '8', '4', '3', '8', '3', '3', '8', '0', '6', '5', '4', '1', '7', '1', '4', '0', '4', '9', '6', '5', '5', '1', '1', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '2', '6', '2', '4', '9', '8', '3', '2', '7', '0', '4', '6', '1', '2', '6', '4', '4', '7', '0', '5', '2', '8', '1', '7', '8', '2', '8', '6', '4', '9', '6', '4', '0', '8', '2', '0', '0', '6', '5', '6', '8', '5', '6', '9', '5', '6', '9', '3', '4', '7', '4', '4', '0', '5', '9', '1', '2', '6', '9', '4', '3', '9', '1', '3', '3', '7', '0', '3', '4', '0', '5', '0', '5', '0', '2', '5', '4', '1', '7', '1', '6', '9', '5', '8', '1', '4', '0', '4', '6', '4', '9', '8', '8', '1', '6', '3', '7', '5', '0', '8', '6', '9', '7', '9', '4', '5', '4', '7', '5', '4', '4', '9'])
noncomputable def fragment0250165Acc00800 : List (String × SourceJson) := (fragment0250165Field007Key00, fragment0250165Field007Value00) :: fragment0250165Acc00700
noncomputable def fragment0250165Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '2', '0', '3', '2', '3', '6', '4', '2', '4', '9', '2', '7', '5', '9', '1', '9', '2', '2', '5', '8', '5', '0', '2', '4', '1', '5', '4', '7', '3', '7', '6', '4', '0', '5', '4', '9', '0', '3', '1', '7', '5', '4', '9', '8', '8', '3', '9', '7', '9', '3', '1', '9', '8', '8', '4', '3', '8', '3', '3', '8', '0', '6', '5', '4', '1', '7', '1', '4', '0', '4', '9', '6', '5', '5', '1', '1', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '2', '6', '2', '4', '9', '8', '3', '2', '7', '0', '4', '6', '1', '2', '6', '4', '4', '7', '0', '5', '2', '8', '1', '7', '8', '2', '8', '6', '4', '9', '6', '4', '0', '8', '2', '0', '0', '6', '5', '6', '8', '5', '6', '9', '5', '6', '9', '3', '4', '7', '4', '4', '0', '5', '9', '1', '2', '6', '9', '4', '3', '9', '1', '3', '3', '7', '0', '3', '4', '0', '5', '0', '5', '0', '2', '5', '4', '1', '7', '1', '6', '9', '5', '8', '1', '4', '0', '4', '6', '4', '9', '8', '8', '1', '6', '3', '7', '5', '0', '8', '6', '9', '7', '9', '4', '5', '4', '7', '5', '4', '4', '9', '"', ',']

theorem object_fragment0250165_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment0250165Field007Chars00 ++ tail)) fragment0250165Acc00700 =
      SourceJson.object (fuel + 219) (SourceJson.white tail) fragment0250165Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250165_object_field_007"
  err.flush

noncomputable def fragment0250165Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0250165Field008Value00 : SourceJson := .str (String.ofList ['1', '4', '9', '4', '5', '8', '7', '4', '2', '2', '3', '9', '3', '2', '0', '2', '4', '0', '7'])
noncomputable def fragment0250165Acc00900 : List (String × SourceJson) := (fragment0250165Field008Key00, fragment0250165Field008Value00) :: fragment0250165Acc00800
noncomputable def fragment0250165Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '9', '4', '5', '8', '7', '4', '2', '2', '3', '9', '3', '2', '0', '2', '4', '0', '7', '"', ',']

theorem object_fragment0250165_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 219) (SourceJson.white (fragment0250165Field008Chars00 ++ tail)) fragment0250165Acc00800 =
      SourceJson.object (fuel + 218) (SourceJson.white tail) fragment0250165Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250165_object_field_008"
  err.flush

noncomputable def fragment0250165Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0250165Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '2', '0', '7', '3', '5', '2', '3', '1', '6', '4', '5', '4', '7', '0', '1', '9', '8', '4'])
noncomputable def fragment0250165Acc01000 : List (String × SourceJson) := (fragment0250165Field009Key00, fragment0250165Field009Value00) :: fragment0250165Acc00900
noncomputable def fragment0250165Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '2', '0', '7', '3', '5', '2', '3', '1', '6', '4', '5', '4', '7', '0', '1', '9', '8', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0250165_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0250165Field009Chars00 ++ tail)) fragment0250165Acc00900 =
      .ok (.obj (fragment0250165Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250165_object_field_009"
  err.flush

noncomputable def fragment0250165Chars : List Char := '{' :: (fragment0250165Field000Chars00 ++ fragment0250165Field001Chars00 ++ fragment0250165Field002Chars00 ++ fragment0250165Field003Chars00 ++ fragment0250165Field004Chars00 ++ fragment0250165Field005Chars00 ++ fragment0250165Field006Chars00 ++ fragment0250165Field007Chars00 ++ fragment0250165Field008Chars00 ++ fragment0250165Field009Chars00)
noncomputable def fragment0250165Value : SourceJson := .obj (fragment0250165Acc01000.reverse)

theorem value_fragment0250165 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 228) (fragment0250165Chars ++ tail) =
      .ok (fragment0250165Value, tail) := by
  have hinput : fragment0250165Chars ++ tail = '{' :: (fragment0250165Field000Chars00 ++ (fragment0250165Field001Chars00 ++ (fragment0250165Field002Chars00 ++ (fragment0250165Field003Chars00 ++ (fragment0250165Field004Chars00 ++ (fragment0250165Field005Chars00 ++ (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0250165Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 228) (fragment0250165Chars ++ tail) =
        SourceJson.value (fuel + 228) ('{' :: (fragment0250165Field000Chars00 ++ (fragment0250165Field001Chars00 ++ (fragment0250165Field002Chars00 ++ (fragment0250165Field003Chars00 ++ (fragment0250165Field004Chars00 ++ (fragment0250165Field005Chars00 ++ (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 228)) hinput
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0250165Field000Chars00 ++ (fragment0250165Field001Chars00 ++ (fragment0250165Field002Chars00 ++ (fragment0250165Field003Chars00 ++ (fragment0250165Field004Chars00 ++ (fragment0250165Field005Chars00 ++ (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail)))))))))))) fragment0250165Acc00000 := by rfl
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0250165Field001Chars00 ++ (fragment0250165Field002Chars00 ++ (fragment0250165Field003Chars00 ++ (fragment0250165Field004Chars00 ++ (fragment0250165Field005Chars00 ++ (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail))))))))))) fragment0250165Acc00100 := object_fragment0250165_field_000 fuel (fragment0250165Field001Chars00 ++ (fragment0250165Field002Chars00 ++ (fragment0250165Field003Chars00 ++ (fragment0250165Field004Chars00 ++ (fragment0250165Field005Chars00 ++ (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0250165Field002Chars00 ++ (fragment0250165Field003Chars00 ++ (fragment0250165Field004Chars00 ++ (fragment0250165Field005Chars00 ++ (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail)))))))))) fragment0250165Acc00200 := object_fragment0250165_field_001 fuel (fragment0250165Field002Chars00 ++ (fragment0250165Field003Chars00 ++ (fragment0250165Field004Chars00 ++ (fragment0250165Field005Chars00 ++ (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0250165Field003Chars00 ++ (fragment0250165Field004Chars00 ++ (fragment0250165Field005Chars00 ++ (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail))))))))) fragment0250165Acc00300 := object_fragment0250165_field_002 fuel (fragment0250165Field003Chars00 ++ (fragment0250165Field004Chars00 ++ (fragment0250165Field005Chars00 ++ (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0250165Field004Chars00 ++ (fragment0250165Field005Chars00 ++ (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail)))))))) fragment0250165Acc00400 := object_fragment0250165_field_003 fuel (fragment0250165Field004Chars00 ++ (fragment0250165Field005Chars00 ++ (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment0250165Field005Chars00 ++ (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail))))))) fragment0250165Acc00500 := object_fragment0250165_field_004 fuel (fragment0250165Field005Chars00 ++ (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 221) (SourceJson.white (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail)))))) fragment0250165Acc00600 := object_fragment0250165_field_005 fuel (fragment0250165Field006Chars00 ++ (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail))))) fragment0250165Acc00700 := object_fragment0250165_field_006 fuel (fragment0250165Field007Chars00 ++ (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 219) (SourceJson.white (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail)))) fragment0250165Acc00800 := object_fragment0250165_field_007 fuel (fragment0250165Field008Chars00 ++ (fragment0250165Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0250165Field009Chars00 ++ (tail))) fragment0250165Acc00900 := object_fragment0250165_field_008 fuel (fragment0250165Field009Chars00 ++ (tail))
    _ = .ok (fragment0250165Value, tail) := object_fragment0250165_field_009 fuel (tail)

noncomputable def fragment0251748Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0251748Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0251748Field000Value00 : SourceJson := .number (String.ofList ['1', '5'])
noncomputable def fragment0251748Acc00100 : List (String × SourceJson) := (fragment0251748Field000Key00, fragment0251748Field000Value00) :: fragment0251748Acc00000
noncomputable def fragment0251748Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '5', ',']

theorem object_fragment0251748_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0251748Field000Chars00 ++ tail)) fragment0251748Acc00000 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0251748Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251748_object_field_000"
  err.flush

noncomputable def fragment0251748Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0251748Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0251748Acc00200 : List (String × SourceJson) := (fragment0251748Field001Key00, fragment0251748Field001Value00) :: fragment0251748Acc00100
noncomputable def fragment0251748Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0251748_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0251748Field001Chars00 ++ tail)) fragment0251748Acc00100 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0251748Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251748_object_field_001"
  err.flush

noncomputable def fragment0251748Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0251748Field002Value00 : SourceJson := .str (String.ofList ['1', '1', '4', '9', '5', '7', '3', '5', '0', '0', '1', '7', '8', '1', '1', '1', '1', '9', '1', '2', '3', '0', '7', '0', '9', '4', '0', '4', '8', '1', '8', '5', '0', '6', '1', '4', '6', '5', '9', '5', '2', '5', '8', '5', '0', '9', '/', '2', '3', '4', '9', '2', '5', '1', '8', '1', '6', '3', '2', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0251748Acc00300 : List (String × SourceJson) := (fragment0251748Field002Key00, fragment0251748Field002Value00) :: fragment0251748Acc00200
noncomputable def fragment0251748Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '1', '4', '9', '5', '7', '3', '5', '0', '0', '1', '7', '8', '1', '1', '1', '1', '9', '1', '2', '3', '0', '7', '0', '9', '4', '0', '4', '8', '1', '8', '5', '0', '6', '1', '4', '6', '5', '9', '5', '2', '5', '8', '5', '0', '9', '/', '2', '3', '4', '9', '2', '5', '1', '8', '1', '6', '3', '2', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0251748_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0251748Field002Chars00 ++ tail)) fragment0251748Acc00200 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0251748Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251748_object_field_002"
  err.flush

noncomputable def fragment0251748Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0251748Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0251748Acc00400 : List (String × SourceJson) := (fragment0251748Field003Key00, fragment0251748Field003Value00) :: fragment0251748Acc00300
noncomputable def fragment0251748Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0251748_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0251748Field003Chars00 ++ tail)) fragment0251748Acc00300 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0251748Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251748_object_field_003"
  err.flush

noncomputable def fragment0251748Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0251748Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0251748Acc00500 : List (String × SourceJson) := (fragment0251748Field004Key00, fragment0251748Field004Value00) :: fragment0251748Acc00400
noncomputable def fragment0251748Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0251748_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0251748Field004Chars00 ++ tail)) fragment0251748Acc00400 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0251748Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251748_object_field_004"
  err.flush

noncomputable def fragment0251748Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0251748Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '8', '4', '8', '7', '8', '4', '9', '6', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '1', '8', '8', '9', '5', '0', '5', '8', '1', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '8', '3', '0', '5', '3', '0', '1', '3', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '2', '2', '7', '1', '9', '7', '9', '9', '3', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '1', '9', '5', '5', '7', '3', '7', '0', '9', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '1', '9', '1', '8', '4', '3', '5', '1', '/', '1', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '0', '5', '0', '1', '8', '4', '9', '9', '/', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '0', '6', '3', '0', '9', '0', '0', '2', '7', '/', '9', '4', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '6', '1', '0', '1', '1', '1', '8', '1', '/', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '5', '0', '5', '3', '8', '6', '3', '7', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0251748Acc00600 : List (String × SourceJson) := (fragment0251748Field005Key00, fragment0251748Field005Value00) :: fragment0251748Acc00500
noncomputable def fragment0251748Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '4', '8', '7', '8', '4', '9', '6', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '1', '8', '8', '9', '5', '0', '5', '8', '1', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '8', '3', '0', '5', '3', '0', '1', '3', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '2', '2', '7', '1', '9', '7', '9', '9', '3', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '9', '5', '5', '7', '3', '7', '0', '9', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '1', '9', '1', '8', '4', '3', '5', '1', '/', '1', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '0', '5', '0', '1', '8', '4', '9', '9', '/', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '0', '6', '3', '0', '9', '0', '0', '2', '7', '/', '9', '4', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '6', '1', '0', '1', '1', '1', '8', '1', '/', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '5', '0', '5', '3', '8', '6', '3', '7', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0251748_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0251748Field005Chars00 ++ tail)) fragment0251748Acc00500 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0251748Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251748_object_field_005"
  err.flush

noncomputable def fragment0251748Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0251748Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '5', '2', '0', '0', '9', '6', '1', '0', '2', '1', '0', '3', '8', '1', '8', '6', '4', '8', '3', '9', '8', '1', '6', '5', '9', '8', '7', '3', '2', '1', '8', '4', '1', '5', '3', '9', '7', '7', '1', '6', '6', '8', '9', '0', '3', '7', '5', '9', '2', '8', '1', '2', '5', '/', '6', '3', '5', '3', '5', '8', '8', '7', '1', '7', '8', '5', '8', '5', '7', '9', '0', '9', '7', '5', '9', '9', '8', '1', '6', '6', '5', '3', '5', '7', '5', '3', '5', '2', '4', '0', '7', '6', '6', '8', '8', '3', '3', '6', '5', '6', '7', '8', '4', '8', '4', '2', '4', '8', '1', '4', '4', '2', '8', '2', '9', '0', '0', '8', '4'])
noncomputable def fragment0251748Acc00700 : List (String × SourceJson) := (fragment0251748Field006Key00, fragment0251748Field006Value00) :: fragment0251748Acc00600
noncomputable def fragment0251748Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '5', '2', '0', '0', '9', '6', '1', '0', '2', '1', '0', '3', '8', '1', '8', '6', '4', '8', '3', '9', '8', '1', '6', '5', '9', '8', '7', '3', '2', '1', '8', '4', '1', '5', '3', '9', '7', '7', '1', '6', '6', '8', '9', '0', '3', '7', '5', '9', '2', '8', '1', '2', '5', '/', '6', '3', '5', '3', '5', '8', '8', '7', '1', '7', '8', '5', '8', '5', '7', '9', '0', '9', '7', '5', '9', '9', '8', '1', '6', '6', '5', '3', '5', '7', '5', '3', '5', '2', '4', '0', '7', '6', '6', '8', '8', '3', '3', '6', '5', '6', '7', '8', '4', '8', '4', '2', '4', '8', '1', '4', '4', '2', '8', '2', '9', '0', '0', '8', '4', '"', ',']

theorem object_fragment0251748_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0251748Field006Chars00 ++ tail)) fragment0251748Acc00600 =
      SourceJson.object (fuel + 194) (SourceJson.white tail) fragment0251748Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251748_object_field_006"
  err.flush

noncomputable def fragment0251748Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0251748Field007Value00 : SourceJson := .str (String.ofList ['7', '5', '2', '6', '2', '3', '3', '0', '2', '5', '7', '0', '3', '0', '5', '9', '7', '3', '4', '8', '9', '6', '4', '3', '0', '0', '8', '8', '6', '1', '2', '8', '5', '3', '6', '7', '4', '1', '7', '0', '2', '4', '6', '5', '2', '9', '0', '5', '5', '8', '4', '0', '1', '4', '6', '3', '6', '2', '3', '1', '9', '3', '7', '2', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '1', '2', '0', '6', '8', '4', '2', '0', '7', '7', '8', '3', '8', '5', '7', '6', '4', '5', '2', '5', '7', '5', '5', '4', '1', '0', '2', '1', '4', '4', '2', '3', '4', '5', '2', '4', '0', '2', '4', '9', '9', '9', '3', '6', '4', '6', '6', '2', '5', '8', '5', '6', '5', '8', '9', '3', '5', '4', '9', '1', '1', '1', '4', '0', '8', '9', '2', '6', '9', '7', '1', '6', '4', '6', '7', '9', '5', '1', '1', '6', '9', '6', '9', '8', '3', '1', '8', '9', '5', '9', '7', '0', '0', '0', '7', '7', '3', '7'])
noncomputable def fragment0251748Acc00800 : List (String × SourceJson) := (fragment0251748Field007Key00, fragment0251748Field007Value00) :: fragment0251748Acc00700
noncomputable def fragment0251748Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '5', '2', '6', '2', '3', '3', '0', '2', '5', '7', '0', '3', '0', '5', '9', '7', '3', '4', '8', '9', '6', '4', '3', '0', '0', '8', '8', '6', '1', '2', '8', '5', '3', '6', '7', '4', '1', '7', '0', '2', '4', '6', '5', '2', '9', '0', '5', '5', '8', '4', '0', '1', '4', '6', '3', '6', '2', '3', '1', '9', '3', '7', '2', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '1', '2', '0', '6', '8', '4', '2', '0', '7', '7', '8', '3', '8', '5', '7', '6', '4', '5', '2', '5', '7', '5', '5', '4', '1', '0', '2', '1', '4', '4', '2', '3', '4', '5', '2', '4', '0', '2', '4', '9', '9', '9', '3', '6', '4', '6', '6', '2', '5', '8', '5', '6', '5', '8', '9', '3', '5', '4', '9', '1', '1', '1', '4', '0', '8', '9', '2', '6', '9', '7', '1', '6', '4', '6', '7', '9', '5', '1', '1', '6', '9', '6', '9', '8', '3', '1', '8', '9', '5', '9', '7', '0', '0', '0', '7', '7', '3', '7', '"', ',']

theorem object_fragment0251748_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 194) (SourceJson.white (fragment0251748Field007Chars00 ++ tail)) fragment0251748Acc00700 =
      SourceJson.object (fuel + 193) (SourceJson.white tail) fragment0251748Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251748_object_field_007"
  err.flush

noncomputable def fragment0251748Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0251748Field008Value00 : SourceJson := .str (String.ofList ['2', '3', '0', '9', '4', '2', '4', '2', '4', '6', '5', '4', '1', '1', '2', '6', '0', '9', '0'])
noncomputable def fragment0251748Acc00900 : List (String × SourceJson) := (fragment0251748Field008Key00, fragment0251748Field008Value00) :: fragment0251748Acc00800
noncomputable def fragment0251748Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '0', '9', '4', '2', '4', '2', '4', '6', '5', '4', '1', '1', '2', '6', '0', '9', '0', '"', ',']

theorem object_fragment0251748_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 193) (SourceJson.white (fragment0251748Field008Chars00 ++ tail)) fragment0251748Acc00800 =
      SourceJson.object (fuel + 192) (SourceJson.white tail) fragment0251748Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251748_object_field_008"
  err.flush

noncomputable def fragment0251748Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0251748Field009Value00 : SourceJson := .str (String.ofList ['1', '6', '5', '0', '8', '2', '5', '9', '0', '8', '6', '4', '1', '3', '6', '3', '6', '7', '4', '4'])
noncomputable def fragment0251748Acc01000 : List (String × SourceJson) := (fragment0251748Field009Key00, fragment0251748Field009Value00) :: fragment0251748Acc00900
noncomputable def fragment0251748Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '5', '0', '8', '2', '5', '9', '0', '8', '6', '4', '1', '3', '6', '3', '6', '7', '4', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0251748_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 192) (SourceJson.white (fragment0251748Field009Chars00 ++ tail)) fragment0251748Acc00900 =
      .ok (.obj (fragment0251748Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251748_object_field_009"
  err.flush

noncomputable def fragment0251748Chars : List Char := '{' :: (fragment0251748Field000Chars00 ++ fragment0251748Field001Chars00 ++ fragment0251748Field002Chars00 ++ fragment0251748Field003Chars00 ++ fragment0251748Field004Chars00 ++ fragment0251748Field005Chars00 ++ fragment0251748Field006Chars00 ++ fragment0251748Field007Chars00 ++ fragment0251748Field008Chars00 ++ fragment0251748Field009Chars00)
noncomputable def fragment0251748Value : SourceJson := .obj (fragment0251748Acc01000.reverse)

theorem value_fragment0251748 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 202) (fragment0251748Chars ++ tail) =
      .ok (fragment0251748Value, tail) := by
  have hinput : fragment0251748Chars ++ tail = '{' :: (fragment0251748Field000Chars00 ++ (fragment0251748Field001Chars00 ++ (fragment0251748Field002Chars00 ++ (fragment0251748Field003Chars00 ++ (fragment0251748Field004Chars00 ++ (fragment0251748Field005Chars00 ++ (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0251748Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 202) (fragment0251748Chars ++ tail) =
        SourceJson.value (fuel + 202) ('{' :: (fragment0251748Field000Chars00 ++ (fragment0251748Field001Chars00 ++ (fragment0251748Field002Chars00 ++ (fragment0251748Field003Chars00 ++ (fragment0251748Field004Chars00 ++ (fragment0251748Field005Chars00 ++ (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 202)) hinput
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0251748Field000Chars00 ++ (fragment0251748Field001Chars00 ++ (fragment0251748Field002Chars00 ++ (fragment0251748Field003Chars00 ++ (fragment0251748Field004Chars00 ++ (fragment0251748Field005Chars00 ++ (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail)))))))))))) fragment0251748Acc00000 := by rfl
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0251748Field001Chars00 ++ (fragment0251748Field002Chars00 ++ (fragment0251748Field003Chars00 ++ (fragment0251748Field004Chars00 ++ (fragment0251748Field005Chars00 ++ (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail))))))))))) fragment0251748Acc00100 := object_fragment0251748_field_000 fuel (fragment0251748Field001Chars00 ++ (fragment0251748Field002Chars00 ++ (fragment0251748Field003Chars00 ++ (fragment0251748Field004Chars00 ++ (fragment0251748Field005Chars00 ++ (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0251748Field002Chars00 ++ (fragment0251748Field003Chars00 ++ (fragment0251748Field004Chars00 ++ (fragment0251748Field005Chars00 ++ (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail)))))))))) fragment0251748Acc00200 := object_fragment0251748_field_001 fuel (fragment0251748Field002Chars00 ++ (fragment0251748Field003Chars00 ++ (fragment0251748Field004Chars00 ++ (fragment0251748Field005Chars00 ++ (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0251748Field003Chars00 ++ (fragment0251748Field004Chars00 ++ (fragment0251748Field005Chars00 ++ (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail))))))))) fragment0251748Acc00300 := object_fragment0251748_field_002 fuel (fragment0251748Field003Chars00 ++ (fragment0251748Field004Chars00 ++ (fragment0251748Field005Chars00 ++ (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0251748Field004Chars00 ++ (fragment0251748Field005Chars00 ++ (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail)))))))) fragment0251748Acc00400 := object_fragment0251748_field_003 fuel (fragment0251748Field004Chars00 ++ (fragment0251748Field005Chars00 ++ (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0251748Field005Chars00 ++ (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail))))))) fragment0251748Acc00500 := object_fragment0251748_field_004 fuel (fragment0251748Field005Chars00 ++ (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail)))))) fragment0251748Acc00600 := object_fragment0251748_field_005 fuel (fragment0251748Field006Chars00 ++ (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 194) (SourceJson.white (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail))))) fragment0251748Acc00700 := object_fragment0251748_field_006 fuel (fragment0251748Field007Chars00 ++ (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 193) (SourceJson.white (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail)))) fragment0251748Acc00800 := object_fragment0251748_field_007 fuel (fragment0251748Field008Chars00 ++ (fragment0251748Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 192) (SourceJson.white (fragment0251748Field009Chars00 ++ (tail))) fragment0251748Acc00900 := object_fragment0251748_field_008 fuel (fragment0251748Field009Chars00 ++ (tail))
    _ = .ok (fragment0251748Value, tail) := object_fragment0251748_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_before_reader"
  err.flush

noncomputable def chunk0014LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0014SuffixChars00 : List Char := [',']
noncomputable def chunk0014Chars00 : List Char := chunk0014LeadChars00 ++ fragment0250165Chars ++ chunk0014SuffixChars00
noncomputable def chunk0014Push00 (acc : List SourceJson) : List SourceJson := fragment0250165Value :: acc

noncomputable def chunk0014AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0014_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 590)
      (SourceJson.white (chunk0014LeadChars00 ++ (fragment0250165Chars ++ rest))) acc =
      (SourceJson.value (fuel + 589) (fragment0250165Chars ++ rest)).bind
        (chunk0014AfterValue00 (fuel + 589) acc) := by rfl

theorem array_chunk0014 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 590) (SourceJson.white (chunk0014Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 589) (SourceJson.white tail) (chunk0014Push00 acc) := by
  have hinput : chunk0014Chars00 ++ tail = chunk0014LeadChars00 ++ (fragment0250165Chars ++ (chunk0014SuffixChars00 ++ tail)) := by
    simp only [chunk0014Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 590) (SourceJson.white (chunk0014Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 590)
          (SourceJson.white (chunk0014LeadChars00 ++ (fragment0250165Chars ++ (chunk0014SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 590) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 589) (fragment0250165Chars ++ (chunk0014SuffixChars00 ++ tail))).bind
        (chunk0014AfterValue00 (fuel + 589) acc) := array_chunk0014_head fuel (chunk0014SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0250165Value, chunk0014SuffixChars00 ++ tail)).bind
        (chunk0014AfterValue00 (fuel + 589) acc) :=
      congrArg (fun result => result.bind (chunk0014AfterValue00 (fuel + 589) acc))
        (value_fragment0250165 (fuel + 361) (chunk0014SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 589) (SourceJson.white tail) (chunk0014Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_before_reader"
  err.flush

noncomputable def chunk0015LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0015SuffixChars00 : List Char := [',']
noncomputable def chunk0015Chars00 : List Char := chunk0015LeadChars00 ++ fragment0251748Chars ++ chunk0015SuffixChars00
noncomputable def chunk0015Push00 (acc : List SourceJson) : List SourceJson := fragment0251748Value :: acc

noncomputable def chunk0015AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0015_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 589)
      (SourceJson.white (chunk0015LeadChars00 ++ (fragment0251748Chars ++ rest))) acc =
      (SourceJson.value (fuel + 588) (fragment0251748Chars ++ rest)).bind
        (chunk0015AfterValue00 (fuel + 588) acc) := by rfl

theorem array_chunk0015 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 589) (SourceJson.white (chunk0015Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 588) (SourceJson.white tail) (chunk0015Push00 acc) := by
  have hinput : chunk0015Chars00 ++ tail = chunk0015LeadChars00 ++ (fragment0251748Chars ++ (chunk0015SuffixChars00 ++ tail)) := by
    simp only [chunk0015Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 589) (SourceJson.white (chunk0015Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 589)
          (SourceJson.white (chunk0015LeadChars00 ++ (fragment0251748Chars ++ (chunk0015SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 589) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 588) (fragment0251748Chars ++ (chunk0015SuffixChars00 ++ tail))).bind
        (chunk0015AfterValue00 (fuel + 588) acc) := array_chunk0015_head fuel (chunk0015SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0251748Value, chunk0015SuffixChars00 ++ tail)).bind
        (chunk0015AfterValue00 (fuel + 588) acc) :=
      congrArg (fun result => result.bind (chunk0015AfterValue00 (fuel + 588) acc))
        (value_fragment0251748 (fuel + 386) (chunk0015SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 588) (SourceJson.white tail) (chunk0015Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0014Chars00 ++ chunk0015Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0015Push00 (chunk0014Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 590) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 588) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 590) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 590) (SourceJson.white (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 590) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 589) (SourceJson.white (chunk0015Chars00 ++ (tail))) (chunk0014Push00 (acc)) := array_chunk0014 fuel (chunk0015Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 588) (SourceJson.white tail) (blockPush acc) := array_chunk0015 fuel (tail) (chunk0014Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 250159).take 3132 = blockChars := by rfl

theorem block_original_split : sourceRest 250159 = blockChars ++ sourceRest 253291 := by
  calc
    sourceRest 250159 = (sourceRest 250159).take 3132 ++ (sourceRest 250159).drop 3132 :=
      (List.take_append_drop 3132 (sourceRest 250159)).symm
    _ = blockChars ++ (sourceRest 250159).drop 3132 :=
      congrArg (fun part => part ++ (sourceRest 250159).drop 3132) block_original_prefix
    _ = blockChars ++ sourceRest 253291 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 250159 3132)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 590) (SourceJson.white (sourceRest 250159)) acc =
      SourceJson.array (fuel + 588) (SourceJson.white (sourceRest 253291)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 590) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 253291) acc)

#print axioms object_fragment0250165_field_000
#print axioms object_fragment0250165_field_001
#print axioms object_fragment0250165_field_002
#print axioms object_fragment0250165_field_003
#print axioms object_fragment0250165_field_004
#print axioms object_fragment0250165_field_005
#print axioms object_fragment0250165_field_006
#print axioms object_fragment0250165_field_007
#print axioms object_fragment0250165_field_008
#print axioms object_fragment0250165_field_009
#print axioms value_fragment0250165
#print axioms object_fragment0251748_field_000
#print axioms object_fragment0251748_field_001
#print axioms object_fragment0251748_field_002
#print axioms object_fragment0251748_field_003
#print axioms object_fragment0251748_field_004
#print axioms object_fragment0251748_field_005
#print axioms object_fragment0251748_field_006
#print axioms object_fragment0251748_field_007
#print axioms object_fragment0251748_field_008
#print axioms object_fragment0251748_field_009
#print axioms value_fragment0251748
#print axioms array_chunk0014_head
#print axioms array_chunk0014
#print axioms array_chunk0015_head
#print axioms array_chunk0015
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock007

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
