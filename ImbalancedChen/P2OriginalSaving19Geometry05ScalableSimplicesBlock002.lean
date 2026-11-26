import ImbalancedChen.P2OriginalSaving19Geometry05ScalableInput

/-! Original simplices grouped chunk transitions, including exact compact-input binding.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesBlock002

noncomputable def fragment0131392Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0131392Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0131392Field000Value00 : SourceJson := .number (String.ofList ['1', '6'])
noncomputable def fragment0131392Acc00100 : List (String × SourceJson) := (fragment0131392Field000Key00, fragment0131392Field000Value00) :: fragment0131392Acc00000
noncomputable def fragment0131392Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '6', ',']

theorem object_fragment0131392_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 270) (SourceJson.white (fragment0131392Field000Chars00 ++ tail)) fragment0131392Acc00000 =
      SourceJson.object (fuel + 269) (SourceJson.white tail) fragment0131392Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0131392_object_field_000"
  err.flush

noncomputable def fragment0131392Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0131392Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0131392Acc00200 : List (String × SourceJson) := (fragment0131392Field001Key00, fragment0131392Field001Value00) :: fragment0131392Acc00100
noncomputable def fragment0131392Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0131392_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 269) (SourceJson.white (fragment0131392Field001Chars00 ++ tail)) fragment0131392Acc00100 =
      SourceJson.object (fuel + 268) (SourceJson.white tail) fragment0131392Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0131392_object_field_001"
  err.flush

noncomputable def fragment0131392Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0131392Field002Value00 : SourceJson := .str (String.ofList ['1', '5', '9', '9', '0', '7', '9', '5', '7', '2', '2', '0', '9', '8', '3', '8', '3', '7', '2', '2', '2', '4', '8', '2', '3', '2', '1', '1', '0', '6', '7', '4', '6', '3', '6', '2', '8', '4', '7', '1', '/', '1', '5', '7', '3', '6', '7', '1', '5', '3', '3', '4', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0131392Acc00300 : List (String × SourceJson) := (fragment0131392Field002Key00, fragment0131392Field002Value00) :: fragment0131392Acc00200
noncomputable def fragment0131392Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '5', '9', '9', '0', '7', '9', '5', '7', '2', '2', '0', '9', '8', '3', '8', '3', '7', '2', '2', '2', '4', '8', '2', '3', '2', '1', '1', '0', '6', '7', '4', '6', '3', '6', '2', '8', '4', '7', '1', '/', '1', '5', '7', '3', '6', '7', '1', '5', '3', '3', '4', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0131392_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 268) (SourceJson.white (fragment0131392Field002Chars00 ++ tail)) fragment0131392Acc00200 =
      SourceJson.object (fuel + 267) (SourceJson.white tail) fragment0131392Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0131392_object_field_002"
  err.flush

noncomputable def fragment0131392Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0131392Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0131392Acc00400 : List (String × SourceJson) := (fragment0131392Field003Key00, fragment0131392Field003Value00) :: fragment0131392Acc00300
noncomputable def fragment0131392Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0131392_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 267) (SourceJson.white (fragment0131392Field003Chars00 ++ tail)) fragment0131392Acc00300 =
      SourceJson.object (fuel + 266) (SourceJson.white tail) fragment0131392Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0131392_object_field_003"
  err.flush

noncomputable def fragment0131392Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0131392Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0131392Acc00500 : List (String × SourceJson) := (fragment0131392Field004Key00, fragment0131392Field004Value00) :: fragment0131392Acc00400
noncomputable def fragment0131392Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0131392_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 266) (SourceJson.white (fragment0131392Field004Chars00 ++ tail)) fragment0131392Acc00400 =
      SourceJson.object (fuel + 265) (SourceJson.white tail) fragment0131392Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0131392_object_field_004"
  err.flush

noncomputable def fragment0131392Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0131392Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '3', '7', '2', '0', '6', '6', '7', '6', '5', '4', '7', '1', '6', '9', '1', '/', '1', '4', '9', '9', '0', '7', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '1', '1', '7', '1', '7', '9', '6', '2', '9', '9', '8', '3', '/', '4', '6', '8', '4', '6', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '8', '4', '2', '4', '5', '0', '6', '4', '2', '7', '2', '9', '/', '4', '9', '9', '6', '9', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '8', '4', '7', '7', '8', '5', '1', '2', '9', '6', '5', '7', '/', '6', '2', '4', '6', '1', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '4', '7', '0', '1', '8', '2', '7', '3', '8', '5', '3', '/', '1', '0', '4', '1', '0', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '7', '8', '9', '2', '1', '4', '9', '5', '5', '1', '/', '1', '2', '4', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '7', '1', '0', '9', '6', '8', '7', '2', '8', '1', '1', '5', '3', '/', '2', '4', '9', '8', '4', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '4', '4', '0', '7', '8', '1', '9', '6', '9', '8', '7', '5', '1', '/', '7', '4', '9', '5', '3', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '7', '6', '4', '8', '1', '4', '2', '5', '9', '4', '4', '3', '1', '/', '7', '4', '9', '5', '3', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '9', '9', '1', '9', '3', '9', '9', '0', '5', '6', '7', '/', '1', '5', '6', '1', '5', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0131392Acc00600 : List (String × SourceJson) := (fragment0131392Field005Key00, fragment0131392Field005Value00) :: fragment0131392Acc00500
noncomputable def fragment0131392Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '2', '0', '6', '6', '7', '6', '5', '4', '7', '1', '6', '9', '1', '/', '1', '4', '9', '9', '0', '7', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '1', '1', '7', '1', '7', '9', '6', '2', '9', '9', '8', '3', '/', '4', '6', '8', '4', '6', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '8', '4', '2', '4', '5', '0', '6', '4', '2', '7', '2', '9', '/', '4', '9', '9', '6', '9', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '8', '4', '7', '7', '8', '5', '1', '2', '9', '6', '5', '7', '/', '6', '2', '4', '6', '1', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '4', '7', '0', '1', '8', '2', '7', '3', '8', '5', '3', '/', '1', '0', '4', '1', '0', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '3', '7', '8', '9', '2', '1', '4', '9', '5', '5', '1', '/', '1', '2', '4', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '1', '0', '9', '6', '8', '7', '2', '8', '1', '1', '5', '3', '/', '2', '4', '9', '8', '4', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '4', '4', '0', '7', '8', '1', '9', '6', '9', '8', '7', '5', '1', '/', '7', '4', '9', '5', '3', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '7', '6', '4', '8', '1', '4', '2', '5', '9', '4', '4', '3', '1', '/', '7', '4', '9', '5', '3', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '9', '9', '1', '9', '3', '9', '9', '0', '5', '6', '7', '/', '1', '5', '6', '1', '5', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0131392_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 265) (SourceJson.white (fragment0131392Field005Chars00 ++ tail)) fragment0131392Acc00500 =
      SourceJson.object (fuel + 264) (SourceJson.white tail) fragment0131392Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0131392_object_field_005"
  err.flush

noncomputable def fragment0131392Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0131392Field006Value00 : SourceJson := .str (String.ofList ['7', '3', '1', '5', '7', '4', '0', '8', '5', '1', '4', '2', '0', '8', '4', '8', '0', '6', '4', '6', '4', '8', '8', '5', '5', '3', '0', '5', '5', '5', '0', '5', '7', '2', '8', '3', '4', '2', '2', '7', '6', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '2', '2', '8', '1', '5', '8', '8', '2', '9', '7', '8', '9', '8', '3', '9', '1', '5', '5', '8', '4', '6', '2', '2', '5', '5', '8', '4', '9', '1', '6', '6', '6', '9', '8', '6', '8', '0', '4', '5', '3', '0', '4', '6', '8', '5', '4', '6', '7', '1', '1', '0', '4', '5', '5', '7', '9', '8', '1', '1', '3', '1', '4', '9'])
noncomputable def fragment0131392Acc00700 : List (String × SourceJson) := (fragment0131392Field006Key00, fragment0131392Field006Value00) :: fragment0131392Acc00600
noncomputable def fragment0131392Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '3', '1', '5', '7', '4', '0', '8', '5', '1', '4', '2', '0', '8', '4', '8', '0', '6', '4', '6', '4', '8', '8', '5', '5', '3', '0', '5', '5', '5', '0', '5', '7', '2', '8', '3', '4', '2', '2', '7', '6', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '2', '2', '8', '1', '5', '8', '8', '2', '9', '7', '8', '9', '8', '3', '9', '1', '5', '5', '8', '4', '6', '2', '2', '5', '5', '8', '4', '9', '1', '6', '6', '6', '9', '8', '6', '8', '0', '4', '5', '3', '0', '4', '6', '8', '5', '4', '6', '7', '1', '1', '0', '4', '5', '5', '7', '9', '8', '1', '1', '3', '1', '4', '9', '"', ',']

theorem object_fragment0131392_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment0131392Field006Chars00 ++ tail)) fragment0131392Acc00600 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment0131392Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0131392_object_field_006"
  err.flush

noncomputable def fragment0131392Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0131392Field007Value00 : SourceJson := .str (String.ofList ['6', '7', '5', '7', '6', '7', '7', '7', '4', '4', '7', '1', '6', '1', '3', '2', '6', '6', '0', '8', '1', '1', '7', '3', '9', '5', '3', '0', '6', '8', '5', '2', '6', '0', '3', '8', '6', '4', '6', '0', '1', '3', '8', '2', '2', '1', '2', '7', '3', '0', '9', '4', '4', '1', '2', '9', '4', '1', '7', '7', '6', '1', '3', '9', '1', '8', '0', '6', '4', '6', '8', '5', '0', '7', '9', '1', '2', '4', '1', '7', '3', '3', '4', '2', '2', '9', '7', '3', '7', '8', '4', '3', '3', '6', '4', '6', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '5', '2', '6', '6', '7', '8', '7', '1', '9', '8', '2', '1', '9', '0', '9', '9', '2', '4', '3', '9', '8', '4', '3', '1', '6', '8', '7', '3', '6', '6', '6', '1', '2', '5', '6', '4', '6', '2', '0', '0', '1', '7', '6', '5', '1', '9', '1', '8', '4', '1', '0', '2', '7', '9', '0', '6', '7', '0', '8', '1', '0', '1', '2', '0', '9', '6', '3', '1', '2', '8', '1', '0', '7', '7', '5', '3', '2', '0', '6', '6', '2', '1', '7', '2', '5', '4', '8', '0', '0', '3', '4', '9', '5', '0', '3', '8', '7', '6', '6', '4', '0', '4', '6', '3', '7', '8', '9', '8', '8', '2', '6', '8', '3', '9', '8', '0', '4', '0', '2', '3', '4', '5', '1', '1', '2', '7', '5', '9', '0', '3', '7', '7', '6', '9', '1'])
noncomputable def fragment0131392Acc00800 : List (String × SourceJson) := (fragment0131392Field007Key00, fragment0131392Field007Value00) :: fragment0131392Acc00700
noncomputable def fragment0131392Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '7', '5', '7', '6', '7', '7', '7', '4', '4', '7', '1', '6', '1', '3', '2', '6', '6', '0', '8', '1', '1', '7', '3', '9', '5', '3', '0', '6', '8', '5', '2', '6', '0', '3', '8', '6', '4', '6', '0', '1', '3', '8', '2', '2', '1', '2', '7', '3', '0', '9', '4', '4', '1', '2', '9', '4', '1', '7', '7', '6', '1', '3', '9', '1', '8', '0', '6', '4', '6', '8', '5', '0', '7', '9', '1', '2', '4', '1', '7', '3', '3', '4', '2', '2', '9', '7', '3', '7', '8', '4', '3', '3', '6', '4', '6', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '5', '2', '6', '6', '7', '8', '7', '1', '9', '8', '2', '1', '9', '0', '9', '9', '2', '4', '3', '9', '8', '4', '3', '1', '6', '8', '7', '3', '6', '6', '6', '1', '2', '5', '6', '4', '6', '2', '0', '0', '1', '7', '6', '5', '1', '9', '1', '8', '4', '1', '0', '2', '7', '9', '0', '6', '7', '0', '8', '1', '0', '1', '2', '0', '9', '6', '3', '1', '2', '8', '1', '0', '7', '7', '5', '3', '2', '0', '6', '6', '2', '1', '7', '2', '5', '4', '8', '0', '0', '3', '4', '9', '5', '0', '3', '8', '7', '6', '6', '4', '0', '4', '6', '3', '7', '8', '9', '8', '8', '2', '6', '8', '3', '9', '8', '0', '4', '0', '2', '3', '4', '5', '1', '1', '2', '7', '5', '9', '0', '3', '7', '7', '6', '9', '1', '"', ',']

theorem object_fragment0131392_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0131392Field007Chars00 ++ tail)) fragment0131392Acc00700 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0131392Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0131392_object_field_007"
  err.flush

noncomputable def fragment0131392Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0131392Field008Value00 : SourceJson := .str (String.ofList ['3', '0', '1', '4', '3', '9', '5', '2', '4', '3', '0', '3', '6', '1', '1', '4'])
noncomputable def fragment0131392Acc00900 : List (String × SourceJson) := (fragment0131392Field008Key00, fragment0131392Field008Value00) :: fragment0131392Acc00800
noncomputable def fragment0131392Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '0', '1', '4', '3', '9', '5', '2', '4', '3', '0', '3', '6', '1', '1', '4', '"', ',']

theorem object_fragment0131392_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0131392Field008Chars00 ++ tail)) fragment0131392Acc00800 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0131392Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0131392_object_field_008"
  err.flush

noncomputable def fragment0131392Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0131392Field009Value00 : SourceJson := .str (String.ofList ['1', '1', '8', '2', '7', '6', '2', '0', '7', '2', '8', '4', '8', '1', '0', '5', '4'])
noncomputable def fragment0131392Acc01000 : List (String × SourceJson) := (fragment0131392Field009Key00, fragment0131392Field009Value00) :: fragment0131392Acc00900
noncomputable def fragment0131392Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '8', '2', '7', '6', '2', '0', '7', '2', '8', '4', '8', '1', '0', '5', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0131392_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0131392Field009Chars00 ++ tail)) fragment0131392Acc00900 =
      .ok (.obj (fragment0131392Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0131392_object_field_009"
  err.flush

noncomputable def fragment0131392Chars : List Char := '{' :: (fragment0131392Field000Chars00 ++ fragment0131392Field001Chars00 ++ fragment0131392Field002Chars00 ++ fragment0131392Field003Chars00 ++ fragment0131392Field004Chars00 ++ fragment0131392Field005Chars00 ++ fragment0131392Field006Chars00 ++ fragment0131392Field007Chars00 ++ fragment0131392Field008Chars00 ++ fragment0131392Field009Chars00)
noncomputable def fragment0131392Value : SourceJson := .obj (fragment0131392Acc01000.reverse)

theorem value_fragment0131392 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 271) (fragment0131392Chars ++ tail) =
      .ok (fragment0131392Value, tail) := by
  have hinput : fragment0131392Chars ++ tail = '{' :: (fragment0131392Field000Chars00 ++ (fragment0131392Field001Chars00 ++ (fragment0131392Field002Chars00 ++ (fragment0131392Field003Chars00 ++ (fragment0131392Field004Chars00 ++ (fragment0131392Field005Chars00 ++ (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0131392Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 271) (fragment0131392Chars ++ tail) =
        SourceJson.value (fuel + 271) ('{' :: (fragment0131392Field000Chars00 ++ (fragment0131392Field001Chars00 ++ (fragment0131392Field002Chars00 ++ (fragment0131392Field003Chars00 ++ (fragment0131392Field004Chars00 ++ (fragment0131392Field005Chars00 ++ (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 271)) hinput
    _ = SourceJson.object (fuel + 270) (SourceJson.white (fragment0131392Field000Chars00 ++ (fragment0131392Field001Chars00 ++ (fragment0131392Field002Chars00 ++ (fragment0131392Field003Chars00 ++ (fragment0131392Field004Chars00 ++ (fragment0131392Field005Chars00 ++ (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail)))))))))))) fragment0131392Acc00000 := by rfl
    _ = SourceJson.object (fuel + 269) (SourceJson.white (fragment0131392Field001Chars00 ++ (fragment0131392Field002Chars00 ++ (fragment0131392Field003Chars00 ++ (fragment0131392Field004Chars00 ++ (fragment0131392Field005Chars00 ++ (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail))))))))))) fragment0131392Acc00100 := object_fragment0131392_field_000 fuel (fragment0131392Field001Chars00 ++ (fragment0131392Field002Chars00 ++ (fragment0131392Field003Chars00 ++ (fragment0131392Field004Chars00 ++ (fragment0131392Field005Chars00 ++ (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 268) (SourceJson.white (fragment0131392Field002Chars00 ++ (fragment0131392Field003Chars00 ++ (fragment0131392Field004Chars00 ++ (fragment0131392Field005Chars00 ++ (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail)))))))))) fragment0131392Acc00200 := object_fragment0131392_field_001 fuel (fragment0131392Field002Chars00 ++ (fragment0131392Field003Chars00 ++ (fragment0131392Field004Chars00 ++ (fragment0131392Field005Chars00 ++ (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 267) (SourceJson.white (fragment0131392Field003Chars00 ++ (fragment0131392Field004Chars00 ++ (fragment0131392Field005Chars00 ++ (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail))))))))) fragment0131392Acc00300 := object_fragment0131392_field_002 fuel (fragment0131392Field003Chars00 ++ (fragment0131392Field004Chars00 ++ (fragment0131392Field005Chars00 ++ (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 266) (SourceJson.white (fragment0131392Field004Chars00 ++ (fragment0131392Field005Chars00 ++ (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail)))))))) fragment0131392Acc00400 := object_fragment0131392_field_003 fuel (fragment0131392Field004Chars00 ++ (fragment0131392Field005Chars00 ++ (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 265) (SourceJson.white (fragment0131392Field005Chars00 ++ (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail))))))) fragment0131392Acc00500 := object_fragment0131392_field_004 fuel (fragment0131392Field005Chars00 ++ (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail)))))) fragment0131392Acc00600 := object_fragment0131392_field_005 fuel (fragment0131392Field006Chars00 ++ (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail))))) fragment0131392Acc00700 := object_fragment0131392_field_006 fuel (fragment0131392Field007Chars00 ++ (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail)))) fragment0131392Acc00800 := object_fragment0131392_field_007 fuel (fragment0131392Field008Chars00 ++ (fragment0131392Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0131392Field009Chars00 ++ (tail))) fragment0131392Acc00900 := object_fragment0131392_field_008 fuel (fragment0131392Field009Chars00 ++ (tail))
    _ = .ok (fragment0131392Value, tail) := object_fragment0131392_field_009 fuel (tail)

noncomputable def fragment0133064Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0133064Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0133064Field000Value00 : SourceJson := .number (String.ofList ['1', '7'])
noncomputable def fragment0133064Acc00100 : List (String × SourceJson) := (fragment0133064Field000Key00, fragment0133064Field000Value00) :: fragment0133064Acc00000
noncomputable def fragment0133064Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '7', ',']

theorem object_fragment0133064_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 266) (SourceJson.white (fragment0133064Field000Chars00 ++ tail)) fragment0133064Acc00000 =
      SourceJson.object (fuel + 265) (SourceJson.white tail) fragment0133064Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0133064_object_field_000"
  err.flush

noncomputable def fragment0133064Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0133064Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0133064Acc00200 : List (String × SourceJson) := (fragment0133064Field001Key00, fragment0133064Field001Value00) :: fragment0133064Acc00100
noncomputable def fragment0133064Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0133064_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 265) (SourceJson.white (fragment0133064Field001Chars00 ++ tail)) fragment0133064Acc00100 =
      SourceJson.object (fuel + 264) (SourceJson.white tail) fragment0133064Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0133064_object_field_001"
  err.flush

noncomputable def fragment0133064Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0133064Field002Value00 : SourceJson := .str (String.ofList ['6', '7', '1', '4', '8', '8', '5', '3', '7', '8', '2', '1', '6', '1', '5', '5', '9', '2', '3', '9', '3', '1', '4', '0', '4', '4', '3', '2', '7', '2', '9', '7', '6', '7', '6', '0', '8', '1', '5', '3', '3', '/', '4', '2', '4', '0', '0', '0', '5', '5', '6', '5', '5', '0', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0133064Acc00300 : List (String × SourceJson) := (fragment0133064Field002Key00, fragment0133064Field002Value00) :: fragment0133064Acc00200
noncomputable def fragment0133064Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '7', '1', '4', '8', '8', '5', '3', '7', '8', '2', '1', '6', '1', '5', '5', '9', '2', '3', '9', '3', '1', '4', '0', '4', '4', '3', '2', '7', '2', '9', '7', '6', '7', '6', '0', '8', '1', '5', '3', '3', '/', '4', '2', '4', '0', '0', '0', '5', '5', '6', '5', '5', '0', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0133064_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment0133064Field002Chars00 ++ tail)) fragment0133064Acc00200 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment0133064Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0133064_object_field_002"
  err.flush

noncomputable def fragment0133064Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0133064Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0133064Acc00400 : List (String × SourceJson) := (fragment0133064Field003Key00, fragment0133064Field003Value00) :: fragment0133064Acc00300
noncomputable def fragment0133064Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0133064_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0133064Field003Chars00 ++ tail)) fragment0133064Acc00300 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0133064Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0133064_object_field_003"
  err.flush

noncomputable def fragment0133064Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0133064Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0133064Acc00500 : List (String × SourceJson) := (fragment0133064Field004Key00, fragment0133064Field004Value00) :: fragment0133064Acc00400
noncomputable def fragment0133064Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0133064_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0133064Field004Chars00 ++ tail)) fragment0133064Acc00400 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0133064Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0133064_object_field_004"
  err.flush

noncomputable def fragment0133064Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0133064Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '1', '0', '4', '9', '0', '1', '7', '3', '9', '3', '9', '8', '6', '1', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '0', '7', '0', '0', '0', '7', '5', '4', '7', '6', '4', '1', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '8', '2', '1', '7', '5', '8', '5', '7', '4', '7', '4', '3', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '4', '2', '6', '6', '3', '5', '2', '2', '3', '3', '8', '1', '/', '1', '5', '0', '2', '6', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '8', '6', '1', '6', '7', '9', '5', '0', '1', '8', '5', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '3', '7', '8', '4', '6', '2', '0', '6', '9', '2', '1', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '8', '7', '2', '0', '1', '0', '2', '4', '6', '9', '9', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '2', '2', '8', '8', '8', '7', '0', '5', '6', '4', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '5', '3', '2', '9', '0', '8', '7', '3', '3', '6', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '8', '5', '7', '7', '8', '2', '4', '8', '3', '0', '2', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0133064Acc00600 : List (String × SourceJson) := (fragment0133064Field005Key00, fragment0133064Field005Value00) :: fragment0133064Acc00500
noncomputable def fragment0133064Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '4', '9', '0', '1', '7', '3', '9', '3', '9', '8', '6', '1', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '0', '7', '0', '0', '0', '7', '5', '4', '7', '6', '4', '1', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '8', '2', '1', '7', '5', '8', '5', '7', '4', '7', '4', '3', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '2', '6', '6', '3', '5', '2', '2', '3', '3', '8', '1', '/', '1', '5', '0', '2', '6', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '8', '6', '1', '6', '7', '9', '5', '0', '1', '8', '5', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '3', '7', '8', '4', '6', '2', '0', '6', '9', '2', '1', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '8', '7', '2', '0', '1', '0', '2', '4', '6', '9', '9', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '2', '2', '8', '8', '8', '7', '0', '5', '6', '4', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '5', '3', '2', '9', '0', '8', '7', '3', '3', '6', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '8', '5', '7', '7', '8', '2', '4', '8', '3', '0', '2', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0133064_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0133064Field005Chars00 ++ tail)) fragment0133064Acc00500 =
      SourceJson.object (fuel + 260) (SourceJson.white tail) fragment0133064Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0133064_object_field_005"
  err.flush

noncomputable def fragment0133064Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0133064Field006Value00 : SourceJson := .str (String.ofList ['1', '4', '0', '9', '5', '9', '3', '0', '3', '6', '1', '2', '1', '7', '7', '7', '5', '0', '9', '8', '9', '1', '4', '7', '1', '7', '3', '4', '6', '1', '7', '4', '6', '9', '7', '6', '3', '3', '5', '4', '8', '0', '9', '9', '5', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '/', '2', '5', '2', '5', '7', '9', '2', '8', '0', '4', '4', '0', '2', '7', '4', '8', '8', '5', '3', '4', '6', '8', '1', '7', '8', '4', '2', '4', '9', '9', '4', '0', '2', '5', '9', '1', '5', '5', '7', '3', '6', '6', '4', '5', '3', '2', '9', '6', '6', '9', '8', '4', '7', '6', '0', '3', '8', '0', '9', '4', '2', '4', '0', '4', '2', '1', '0', '8', '1'])
noncomputable def fragment0133064Acc00700 : List (String × SourceJson) := (fragment0133064Field006Key00, fragment0133064Field006Value00) :: fragment0133064Acc00600
noncomputable def fragment0133064Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '0', '9', '5', '9', '3', '0', '3', '6', '1', '2', '1', '7', '7', '7', '5', '0', '9', '8', '9', '1', '4', '7', '1', '7', '3', '4', '6', '1', '7', '4', '6', '9', '7', '6', '3', '3', '5', '4', '8', '0', '9', '9', '5', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '/', '2', '5', '2', '5', '7', '9', '2', '8', '0', '4', '4', '0', '2', '7', '4', '8', '8', '5', '3', '4', '6', '8', '1', '7', '8', '4', '2', '4', '9', '9', '4', '0', '2', '5', '9', '1', '5', '5', '7', '3', '6', '6', '4', '5', '3', '2', '9', '6', '6', '9', '8', '4', '7', '6', '0', '3', '8', '0', '9', '4', '2', '4', '0', '4', '2', '1', '0', '8', '1', '"', ',']

theorem object_fragment0133064_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0133064Field006Chars00 ++ tail)) fragment0133064Acc00600 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0133064Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0133064_object_field_006"
  err.flush

noncomputable def fragment0133064Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0133064Field007Value00 : SourceJson := .str (String.ofList ['6', '7', '8', '6', '4', '2', '4', '0', '6', '0', '7', '6', '5', '2', '9', '2', '0', '3', '3', '1', '8', '0', '5', '6', '9', '4', '7', '1', '6', '2', '4', '5', '3', '3', '1', '8', '2', '9', '3', '7', '9', '4', '4', '6', '9', '0', '0', '8', '2', '0', '9', '5', '0', '6', '1', '8', '3', '4', '2', '9', '2', '2', '2', '9', '0', '8', '0', '0', '8', '6', '2', '1', '8', '6', '7', '1', '8', '9', '8', '5', '2', '9', '5', '3', '1', '8', '7', '5', '5', '0', '9', '1', '7', '4', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '0', '2', '1', '3', '9', '0', '6', '0', '1', '5', '9', '9', '2', '6', '2', '3', '8', '3', '4', '8', '7', '8', '0', '4', '0', '2', '2', '5', '9', '3', '6', '2', '5', '2', '8', '8', '6', '1', '8', '8', '6', '2', '5', '8', '8', '0', '0', '5', '8', '8', '7', '1', '2', '1', '4', '2', '7', '7', '0', '3', '1', '4', '1', '0', '2', '6', '4', '3', '6', '7', '1', '6', '3', '1', '4', '9', '3', '3', '6', '9', '3', '7', '9', '8', '9', '5', '3', '4', '4', '3', '5', '3', '1', '1', '8', '2', '0', '6', '4', '4', '7', '8', '0', '6', '9', '9', '2', '9', '5', '8', '4', '8', '4', '8', '7', '8', '5', '1', '5', '8', '2', '2', '2', '0', '8', '9', '8', '7', '8', '9', '7', '3'])
noncomputable def fragment0133064Acc00800 : List (String × SourceJson) := (fragment0133064Field007Key00, fragment0133064Field007Value00) :: fragment0133064Acc00700
noncomputable def fragment0133064Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '7', '8', '6', '4', '2', '4', '0', '6', '0', '7', '6', '5', '2', '9', '2', '0', '3', '3', '1', '8', '0', '5', '6', '9', '4', '7', '1', '6', '2', '4', '5', '3', '3', '1', '8', '2', '9', '3', '7', '9', '4', '4', '6', '9', '0', '0', '8', '2', '0', '9', '5', '0', '6', '1', '8', '3', '4', '2', '9', '2', '2', '2', '9', '0', '8', '0', '0', '8', '6', '2', '1', '8', '6', '7', '1', '8', '9', '8', '5', '2', '9', '5', '3', '1', '8', '7', '5', '5', '0', '9', '1', '7', '4', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '0', '2', '1', '3', '9', '0', '6', '0', '1', '5', '9', '9', '2', '6', '2', '3', '8', '3', '4', '8', '7', '8', '0', '4', '0', '2', '2', '5', '9', '3', '6', '2', '5', '2', '8', '8', '6', '1', '8', '8', '6', '2', '5', '8', '8', '0', '0', '5', '8', '8', '7', '1', '2', '1', '4', '2', '7', '7', '0', '3', '1', '4', '1', '0', '2', '6', '4', '3', '6', '7', '1', '6', '3', '1', '4', '9', '3', '3', '6', '9', '3', '7', '9', '8', '9', '5', '3', '4', '4', '3', '5', '3', '1', '1', '8', '2', '0', '6', '4', '4', '7', '8', '0', '6', '9', '9', '2', '9', '5', '8', '4', '8', '4', '8', '7', '8', '5', '1', '5', '8', '2', '2', '2', '0', '8', '9', '8', '7', '8', '9', '7', '3', '"', ',']

theorem object_fragment0133064_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0133064Field007Chars00 ++ tail)) fragment0133064Acc00700 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0133064Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0133064_object_field_007"
  err.flush

noncomputable def fragment0133064Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0133064Field008Value00 : SourceJson := .str (String.ofList ['4', '4', '2', '1', '5', '6', '0', '8', '6', '3', '9', '8', '5', '4', '0', '8'])
noncomputable def fragment0133064Acc00900 : List (String × SourceJson) := (fragment0133064Field008Key00, fragment0133064Field008Value00) :: fragment0133064Acc00800
noncomputable def fragment0133064Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '4', '2', '1', '5', '6', '0', '8', '6', '3', '9', '8', '5', '4', '0', '8', '"', ',']

theorem object_fragment0133064_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0133064Field008Chars00 ++ tail)) fragment0133064Acc00800 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0133064Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0133064_object_field_008"
  err.flush

noncomputable def fragment0133064Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0133064Field009Value00 : SourceJson := .str (String.ofList ['1', '7', '3', '3', '2', '4', '2', '4', '4', '3', '1', '9', '7', '5', '8', '8', '8'])
noncomputable def fragment0133064Acc01000 : List (String × SourceJson) := (fragment0133064Field009Key00, fragment0133064Field009Value00) :: fragment0133064Acc00900
noncomputable def fragment0133064Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '3', '3', '2', '4', '2', '4', '4', '3', '1', '9', '7', '5', '8', '8', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0133064_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0133064Field009Chars00 ++ tail)) fragment0133064Acc00900 =
      .ok (.obj (fragment0133064Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0133064_object_field_009"
  err.flush

noncomputable def fragment0133064Chars : List Char := '{' :: (fragment0133064Field000Chars00 ++ fragment0133064Field001Chars00 ++ fragment0133064Field002Chars00 ++ fragment0133064Field003Chars00 ++ fragment0133064Field004Chars00 ++ fragment0133064Field005Chars00 ++ fragment0133064Field006Chars00 ++ fragment0133064Field007Chars00 ++ fragment0133064Field008Chars00 ++ fragment0133064Field009Chars00)
noncomputable def fragment0133064Value : SourceJson := .obj (fragment0133064Acc01000.reverse)

theorem value_fragment0133064 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 267) (fragment0133064Chars ++ tail) =
      .ok (fragment0133064Value, tail) := by
  have hinput : fragment0133064Chars ++ tail = '{' :: (fragment0133064Field000Chars00 ++ (fragment0133064Field001Chars00 ++ (fragment0133064Field002Chars00 ++ (fragment0133064Field003Chars00 ++ (fragment0133064Field004Chars00 ++ (fragment0133064Field005Chars00 ++ (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0133064Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 267) (fragment0133064Chars ++ tail) =
        SourceJson.value (fuel + 267) ('{' :: (fragment0133064Field000Chars00 ++ (fragment0133064Field001Chars00 ++ (fragment0133064Field002Chars00 ++ (fragment0133064Field003Chars00 ++ (fragment0133064Field004Chars00 ++ (fragment0133064Field005Chars00 ++ (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 267)) hinput
    _ = SourceJson.object (fuel + 266) (SourceJson.white (fragment0133064Field000Chars00 ++ (fragment0133064Field001Chars00 ++ (fragment0133064Field002Chars00 ++ (fragment0133064Field003Chars00 ++ (fragment0133064Field004Chars00 ++ (fragment0133064Field005Chars00 ++ (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail)))))))))))) fragment0133064Acc00000 := by rfl
    _ = SourceJson.object (fuel + 265) (SourceJson.white (fragment0133064Field001Chars00 ++ (fragment0133064Field002Chars00 ++ (fragment0133064Field003Chars00 ++ (fragment0133064Field004Chars00 ++ (fragment0133064Field005Chars00 ++ (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail))))))))))) fragment0133064Acc00100 := object_fragment0133064_field_000 fuel (fragment0133064Field001Chars00 ++ (fragment0133064Field002Chars00 ++ (fragment0133064Field003Chars00 ++ (fragment0133064Field004Chars00 ++ (fragment0133064Field005Chars00 ++ (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment0133064Field002Chars00 ++ (fragment0133064Field003Chars00 ++ (fragment0133064Field004Chars00 ++ (fragment0133064Field005Chars00 ++ (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail)))))))))) fragment0133064Acc00200 := object_fragment0133064_field_001 fuel (fragment0133064Field002Chars00 ++ (fragment0133064Field003Chars00 ++ (fragment0133064Field004Chars00 ++ (fragment0133064Field005Chars00 ++ (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0133064Field003Chars00 ++ (fragment0133064Field004Chars00 ++ (fragment0133064Field005Chars00 ++ (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail))))))))) fragment0133064Acc00300 := object_fragment0133064_field_002 fuel (fragment0133064Field003Chars00 ++ (fragment0133064Field004Chars00 ++ (fragment0133064Field005Chars00 ++ (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0133064Field004Chars00 ++ (fragment0133064Field005Chars00 ++ (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail)))))))) fragment0133064Acc00400 := object_fragment0133064_field_003 fuel (fragment0133064Field004Chars00 ++ (fragment0133064Field005Chars00 ++ (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0133064Field005Chars00 ++ (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail))))))) fragment0133064Acc00500 := object_fragment0133064_field_004 fuel (fragment0133064Field005Chars00 ++ (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail)))))) fragment0133064Acc00600 := object_fragment0133064_field_005 fuel (fragment0133064Field006Chars00 ++ (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail))))) fragment0133064Acc00700 := object_fragment0133064_field_006 fuel (fragment0133064Field007Chars00 ++ (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail)))) fragment0133064Acc00800 := object_fragment0133064_field_007 fuel (fragment0133064Field008Chars00 ++ (fragment0133064Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0133064Field009Chars00 ++ (tail))) fragment0133064Acc00900 := object_fragment0133064_field_008 fuel (fragment0133064Field009Chars00 ++ (tail))
    _ = .ok (fragment0133064Value, tail) := object_fragment0133064_field_009 fuel (tail)

noncomputable def fragment0134746Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0134746Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0134746Field000Value00 : SourceJson := .number (String.ofList ['1', '8'])
noncomputable def fragment0134746Acc00100 : List (String × SourceJson) := (fragment0134746Field000Key00, fragment0134746Field000Value00) :: fragment0134746Acc00000
noncomputable def fragment0134746Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '8', ',']

theorem object_fragment0134746_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 265) (SourceJson.white (fragment0134746Field000Chars00 ++ tail)) fragment0134746Acc00000 =
      SourceJson.object (fuel + 264) (SourceJson.white tail) fragment0134746Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134746_object_field_000"
  err.flush

noncomputable def fragment0134746Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0134746Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0134746Acc00200 : List (String × SourceJson) := (fragment0134746Field001Key00, fragment0134746Field001Value00) :: fragment0134746Acc00100
noncomputable def fragment0134746Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0134746_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment0134746Field001Chars00 ++ tail)) fragment0134746Acc00100 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment0134746Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134746_object_field_001"
  err.flush

noncomputable def fragment0134746Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0134746Field002Value00 : SourceJson := .str (String.ofList ['5', '7', '5', '0', '5', '2', '7', '6', '4', '9', '8', '0', '2', '6', '6', '5', '7', '0', '8', '4', '5', '5', '7', '2', '8', '8', '5', '0', '6', '0', '2', '8', '3', '9', '/', '5', '9', '1', '5', '1', '8', '6', '3', '3', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0134746Acc00300 : List (String × SourceJson) := (fragment0134746Field002Key00, fragment0134746Field002Value00) :: fragment0134746Acc00200
noncomputable def fragment0134746Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '7', '5', '0', '5', '2', '7', '6', '4', '9', '8', '0', '2', '6', '6', '5', '7', '0', '8', '4', '5', '5', '7', '2', '8', '8', '5', '0', '6', '0', '2', '8', '3', '9', '/', '5', '9', '1', '5', '1', '8', '6', '3', '3', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0134746_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0134746Field002Chars00 ++ tail)) fragment0134746Acc00200 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0134746Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134746_object_field_002"
  err.flush

noncomputable def fragment0134746Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0134746Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0134746Acc00400 : List (String × SourceJson) := (fragment0134746Field003Key00, fragment0134746Field003Value00) :: fragment0134746Acc00300
noncomputable def fragment0134746Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0134746_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0134746Field003Chars00 ++ tail)) fragment0134746Acc00300 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0134746Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134746_object_field_003"
  err.flush

noncomputable def fragment0134746Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0134746Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0134746Acc00500 : List (String × SourceJson) := (fragment0134746Field004Key00, fragment0134746Field004Value00) :: fragment0134746Acc00400
noncomputable def fragment0134746Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0134746_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0134746Field004Chars00 ++ tail)) fragment0134746Acc00400 =
      SourceJson.object (fuel + 260) (SourceJson.white tail) fragment0134746Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134746_object_field_004"
  err.flush

noncomputable def fragment0134746Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0134746Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '5', '0', '0', '1', '8', '2', '4', '8', '3', '7', '0', '6', '3', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '2', '9', '1', '7', '4', '1', '6', '4', '0', '9', '5', '3', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '9', '6', '9', '3', '4', '2', '3', '6', '1', '4', '8', '3', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '1', '0', '4', '3', '9', '1', '8', '2', '5', '3', '3', '1', '/', '4', '0', '0', '6', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '6', '7', '8', '4', '7', '2', '1', '0', '7', '4', '1', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '6', '9', '0', '2', '6', '2', '4', '2', '0', '1', '8', '1', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '2', '1', '2', '6', '5', '5', '8', '7', '6', '1', '9', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '5', '8', '3', '4', '5', '1', '8', '6', '9', '7', '1', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '8', '4', '7', '9', '2', '4', '0', '7', '2', '9', '3', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '8', '4', '7', '8', '0', '3', '8', '6', '3', '8', '9', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0134746Acc00600 : List (String × SourceJson) := (fragment0134746Field005Key00, fragment0134746Field005Value00) :: fragment0134746Acc00500
noncomputable def fragment0134746Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '0', '0', '1', '8', '2', '4', '8', '3', '7', '0', '6', '3', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '2', '9', '1', '7', '4', '1', '6', '4', '0', '9', '5', '3', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '9', '6', '9', '3', '4', '2', '3', '6', '1', '4', '8', '3', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '1', '0', '4', '3', '9', '1', '8', '2', '5', '3', '3', '1', '/', '4', '0', '0', '6', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '6', '7', '8', '4', '7', '2', '1', '0', '7', '4', '1', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '9', '0', '2', '6', '2', '4', '2', '0', '1', '8', '1', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '2', '1', '2', '6', '5', '5', '8', '7', '6', '1', '9', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '5', '8', '3', '4', '5', '1', '8', '6', '9', '7', '1', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '8', '4', '7', '9', '2', '4', '0', '7', '2', '9', '3', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '8', '4', '7', '8', '0', '3', '8', '6', '3', '8', '9', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0134746_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0134746Field005Chars00 ++ tail)) fragment0134746Acc00500 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0134746Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134746_object_field_005"
  err.flush

noncomputable def fragment0134746Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0134746Field006Value00 : SourceJson := .str (String.ofList ['3', '0', '7', '8', '7', '6', '9', '9', '9', '0', '6', '7', '0', '7', '1', '9', '7', '3', '6', '6', '0', '3', '9', '4', '0', '0', '5', '5', '4', '7', '3', '6', '0', '5', '5', '9', '1', '6', '9', '5', '3', '6', '0', '0', '0', '0', '0', '/', '7', '3', '9', '2', '3', '2', '4', '8', '1', '0', '4', '0', '0', '1', '3', '5', '9', '5', '7', '0', '9', '0', '0', '9', '1', '5', '2', '4', '9', '2', '9', '8', '8', '1', '8', '7', '4', '1', '4', '6', '4', '7', '4', '7', '8', '3', '7', '7', '4', '8', '9', '2', '7', '9', '4', '7', '0', '7', '5', '6', '2', '0', '0', '7'])
noncomputable def fragment0134746Acc00700 : List (String × SourceJson) := (fragment0134746Field006Key00, fragment0134746Field006Value00) :: fragment0134746Acc00600
noncomputable def fragment0134746Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '7', '8', '7', '6', '9', '9', '9', '0', '6', '7', '0', '7', '1', '9', '7', '3', '6', '6', '0', '3', '9', '4', '0', '0', '5', '5', '4', '7', '3', '6', '0', '5', '5', '9', '1', '6', '9', '5', '3', '6', '0', '0', '0', '0', '0', '/', '7', '3', '9', '2', '3', '2', '4', '8', '1', '0', '4', '0', '0', '1', '3', '5', '9', '5', '7', '0', '9', '0', '0', '9', '1', '5', '2', '4', '9', '2', '9', '8', '8', '1', '8', '7', '4', '1', '4', '6', '4', '7', '4', '7', '8', '3', '7', '7', '4', '8', '9', '2', '7', '9', '4', '7', '0', '7', '5', '6', '2', '0', '0', '7', '"', ',']

theorem object_fragment0134746_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0134746Field006Chars00 ++ tail)) fragment0134746Acc00600 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0134746Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134746_object_field_006"
  err.flush

noncomputable def fragment0134746Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0134746Field007Value00 : SourceJson := .str (String.ofList ['1', '3', '6', '7', '8', '0', '1', '4', '4', '5', '6', '6', '7', '7', '5', '3', '6', '4', '1', '0', '5', '7', '4', '8', '2', '8', '0', '2', '9', '6', '6', '2', '3', '4', '5', '4', '9', '8', '2', '9', '6', '1', '8', '2', '2', '8', '7', '9', '1', '1', '3', '0', '7', '0', '7', '7', '1', '7', '9', '2', '8', '7', '3', '2', '3', '7', '5', '8', '9', '9', '2', '0', '4', '9', '6', '7', '5', '0', '3', '7', '9', '1', '8', '6', '9', '6', '5', '0', '9', '6', '4', '3', '1', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '5', '9', '7', '3', '5', '5', '2', '4', '0', '6', '0', '0', '1', '6', '8', '8', '4', '2', '5', '7', '2', '8', '6', '1', '2', '1', '8', '9', '5', '7', '5', '5', '8', '4', '8', '2', '0', '9', '4', '8', '1', '8', '1', '6', '6', '7', '0', '8', '2', '7', '4', '8', '6', '7', '9', '0', '7', '8', '8', '1', '1', '6', '8', '8', '7', '7', '3', '8', '3', '3', '6', '1', '2', '7', '2', '4', '7', '1', '7', '6', '6', '4', '4', '4', '3', '9', '7', '5', '2', '0', '1', '3', '9', '4', '6', '4', '1', '5', '0', '6', '7', '6', '8', '6', '9', '3', '0', '9', '1', '9', '6', '7', '7', '7', '1', '4', '3', '4', '7', '0', '9', '9', '8', '1', '5', '6', '8', '1', '1', '7', '0', '5', '9', '1'])
noncomputable def fragment0134746Acc00800 : List (String × SourceJson) := (fragment0134746Field007Key00, fragment0134746Field007Value00) :: fragment0134746Acc00700
noncomputable def fragment0134746Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '6', '7', '8', '0', '1', '4', '4', '5', '6', '6', '7', '7', '5', '3', '6', '4', '1', '0', '5', '7', '4', '8', '2', '8', '0', '2', '9', '6', '6', '2', '3', '4', '5', '4', '9', '8', '2', '9', '6', '1', '8', '2', '2', '8', '7', '9', '1', '1', '3', '0', '7', '0', '7', '7', '1', '7', '9', '2', '8', '7', '3', '2', '3', '7', '5', '8', '9', '9', '2', '0', '4', '9', '6', '7', '5', '0', '3', '7', '9', '1', '8', '6', '9', '6', '5', '0', '9', '6', '4', '3', '1', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '5', '9', '7', '3', '5', '5', '2', '4', '0', '6', '0', '0', '1', '6', '8', '8', '4', '2', '5', '7', '2', '8', '6', '1', '2', '1', '8', '9', '5', '7', '5', '5', '8', '4', '8', '2', '0', '9', '4', '8', '1', '8', '1', '6', '6', '7', '0', '8', '2', '7', '4', '8', '6', '7', '9', '0', '7', '8', '8', '1', '1', '6', '8', '8', '7', '7', '3', '8', '3', '3', '6', '1', '2', '7', '2', '4', '7', '1', '7', '6', '6', '4', '4', '4', '3', '9', '7', '5', '2', '0', '1', '3', '9', '4', '6', '4', '1', '5', '0', '6', '7', '6', '8', '6', '9', '3', '0', '9', '1', '9', '6', '7', '7', '7', '1', '4', '3', '4', '7', '0', '9', '9', '8', '1', '5', '6', '8', '1', '1', '7', '0', '5', '9', '1', '"', ',']

theorem object_fragment0134746_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0134746Field007Chars00 ++ tail)) fragment0134746Acc00700 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0134746Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134746_object_field_007"
  err.flush

noncomputable def fragment0134746Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0134746Field008Value00 : SourceJson := .str (String.ofList ['3', '2', '9', '9', '7', '1', '0', '1', '1', '0', '4', '3'])
noncomputable def fragment0134746Acc00900 : List (String × SourceJson) := (fragment0134746Field008Key00, fragment0134746Field008Value00) :: fragment0134746Acc00800
noncomputable def fragment0134746Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '9', '9', '7', '1', '0', '1', '1', '0', '4', '3', '"', ',']

theorem object_fragment0134746_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0134746Field008Chars00 ++ tail)) fragment0134746Acc00800 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0134746Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134746_object_field_008"
  err.flush

noncomputable def fragment0134746Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0134746Field009Value00 : SourceJson := .str (String.ofList ['1', '1', '2', '9', '1', '4', '8', '5', '2', '5', '8', '9', '9'])
noncomputable def fragment0134746Acc01000 : List (String × SourceJson) := (fragment0134746Field009Key00, fragment0134746Field009Value00) :: fragment0134746Acc00900
noncomputable def fragment0134746Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '2', '9', '1', '4', '8', '5', '2', '5', '8', '9', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0134746_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0134746Field009Chars00 ++ tail)) fragment0134746Acc00900 =
      .ok (.obj (fragment0134746Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134746_object_field_009"
  err.flush

noncomputable def fragment0134746Chars : List Char := '{' :: (fragment0134746Field000Chars00 ++ fragment0134746Field001Chars00 ++ fragment0134746Field002Chars00 ++ fragment0134746Field003Chars00 ++ fragment0134746Field004Chars00 ++ fragment0134746Field005Chars00 ++ fragment0134746Field006Chars00 ++ fragment0134746Field007Chars00 ++ fragment0134746Field008Chars00 ++ fragment0134746Field009Chars00)
noncomputable def fragment0134746Value : SourceJson := .obj (fragment0134746Acc01000.reverse)

theorem value_fragment0134746 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 266) (fragment0134746Chars ++ tail) =
      .ok (fragment0134746Value, tail) := by
  have hinput : fragment0134746Chars ++ tail = '{' :: (fragment0134746Field000Chars00 ++ (fragment0134746Field001Chars00 ++ (fragment0134746Field002Chars00 ++ (fragment0134746Field003Chars00 ++ (fragment0134746Field004Chars00 ++ (fragment0134746Field005Chars00 ++ (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0134746Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 266) (fragment0134746Chars ++ tail) =
        SourceJson.value (fuel + 266) ('{' :: (fragment0134746Field000Chars00 ++ (fragment0134746Field001Chars00 ++ (fragment0134746Field002Chars00 ++ (fragment0134746Field003Chars00 ++ (fragment0134746Field004Chars00 ++ (fragment0134746Field005Chars00 ++ (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 266)) hinput
    _ = SourceJson.object (fuel + 265) (SourceJson.white (fragment0134746Field000Chars00 ++ (fragment0134746Field001Chars00 ++ (fragment0134746Field002Chars00 ++ (fragment0134746Field003Chars00 ++ (fragment0134746Field004Chars00 ++ (fragment0134746Field005Chars00 ++ (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail)))))))))))) fragment0134746Acc00000 := by rfl
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment0134746Field001Chars00 ++ (fragment0134746Field002Chars00 ++ (fragment0134746Field003Chars00 ++ (fragment0134746Field004Chars00 ++ (fragment0134746Field005Chars00 ++ (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail))))))))))) fragment0134746Acc00100 := object_fragment0134746_field_000 fuel (fragment0134746Field001Chars00 ++ (fragment0134746Field002Chars00 ++ (fragment0134746Field003Chars00 ++ (fragment0134746Field004Chars00 ++ (fragment0134746Field005Chars00 ++ (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0134746Field002Chars00 ++ (fragment0134746Field003Chars00 ++ (fragment0134746Field004Chars00 ++ (fragment0134746Field005Chars00 ++ (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail)))))))))) fragment0134746Acc00200 := object_fragment0134746_field_001 fuel (fragment0134746Field002Chars00 ++ (fragment0134746Field003Chars00 ++ (fragment0134746Field004Chars00 ++ (fragment0134746Field005Chars00 ++ (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0134746Field003Chars00 ++ (fragment0134746Field004Chars00 ++ (fragment0134746Field005Chars00 ++ (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail))))))))) fragment0134746Acc00300 := object_fragment0134746_field_002 fuel (fragment0134746Field003Chars00 ++ (fragment0134746Field004Chars00 ++ (fragment0134746Field005Chars00 ++ (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0134746Field004Chars00 ++ (fragment0134746Field005Chars00 ++ (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail)))))))) fragment0134746Acc00400 := object_fragment0134746_field_003 fuel (fragment0134746Field004Chars00 ++ (fragment0134746Field005Chars00 ++ (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0134746Field005Chars00 ++ (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail))))))) fragment0134746Acc00500 := object_fragment0134746_field_004 fuel (fragment0134746Field005Chars00 ++ (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail)))))) fragment0134746Acc00600 := object_fragment0134746_field_005 fuel (fragment0134746Field006Chars00 ++ (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail))))) fragment0134746Acc00700 := object_fragment0134746_field_006 fuel (fragment0134746Field007Chars00 ++ (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail)))) fragment0134746Acc00800 := object_fragment0134746_field_007 fuel (fragment0134746Field008Chars00 ++ (fragment0134746Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0134746Field009Chars00 ++ (tail))) fragment0134746Acc00900 := object_fragment0134746_field_008 fuel (fragment0134746Field009Chars00 ++ (tail))
    _ = .ok (fragment0134746Value, tail) := object_fragment0134746_field_009 fuel (tail)

noncomputable def fragment0136392Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0136392Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0136392Field000Value00 : SourceJson := .number (String.ofList ['1', '9'])
noncomputable def fragment0136392Acc00100 : List (String × SourceJson) := (fragment0136392Field000Key00, fragment0136392Field000Value00) :: fragment0136392Acc00000
noncomputable def fragment0136392Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '9', ',']

theorem object_fragment0136392_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0136392Field000Chars00 ++ tail)) fragment0136392Acc00000 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0136392Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136392_object_field_000"
  err.flush

noncomputable def fragment0136392Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0136392Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0136392Acc00200 : List (String × SourceJson) := (fragment0136392Field001Key00, fragment0136392Field001Value00) :: fragment0136392Acc00100
noncomputable def fragment0136392Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0136392_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0136392Field001Chars00 ++ tail)) fragment0136392Acc00100 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0136392Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136392_object_field_001"
  err.flush

noncomputable def fragment0136392Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0136392Field002Value00 : SourceJson := .str (String.ofList ['5', '7', '5', '0', '6', '6', '7', '9', '0', '6', '1', '4', '7', '0', '0', '1', '3', '0', '9', '0', '3', '5', '2', '0', '1', '6', '1', '3', '8', '8', '9', '5', '5', '1', '/', '5', '9', '1', '5', '1', '8', '6', '3', '3', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0136392Acc00300 : List (String × SourceJson) := (fragment0136392Field002Key00, fragment0136392Field002Value00) :: fragment0136392Acc00200
noncomputable def fragment0136392Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '7', '5', '0', '6', '6', '7', '9', '0', '6', '1', '4', '7', '0', '0', '1', '3', '0', '9', '0', '3', '5', '2', '0', '1', '6', '1', '3', '8', '8', '9', '5', '5', '1', '/', '5', '9', '1', '5', '1', '8', '6', '3', '3', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0136392_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0136392Field002Chars00 ++ tail)) fragment0136392Acc00200 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0136392Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136392_object_field_002"
  err.flush

noncomputable def fragment0136392Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0136392Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0136392Acc00400 : List (String × SourceJson) := (fragment0136392Field003Key00, fragment0136392Field003Value00) :: fragment0136392Acc00300
noncomputable def fragment0136392Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0136392_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0136392Field003Chars00 ++ tail)) fragment0136392Acc00300 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0136392Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136392_object_field_003"
  err.flush

noncomputable def fragment0136392Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0136392Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0136392Acc00500 : List (String × SourceJson) := (fragment0136392Field004Key00, fragment0136392Field004Value00) :: fragment0136392Acc00400
noncomputable def fragment0136392Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0136392_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0136392Field004Chars00 ++ tail)) fragment0136392Acc00400 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0136392Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136392_object_field_004"
  err.flush

noncomputable def fragment0136392Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0136392Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '9', '4', '8', '5', '6', '7', '6', '4', '8', '8', '8', '1', '/', '7', '5', '1', '3', '0', '6', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '9', '3', '9', '2', '2', '8', '9', '9', '7', '4', '6', '9', '/', '3', '0', '0', '5', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '5', '0', '4', '2', '2', '8', '3', '9', '2', '5', '4', '1', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '0', '5', '8', '8', '0', '1', '6', '7', '8', '9', '9', '9', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '2', '4', '1', '4', '4', '9', '9', '9', '4', '7', '1', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '2', '5', '5', '7', '3', '9', '9', '8', '2', '9', '1', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '1', '0', '8', '4', '1', '2', '3', '1', '9', '9', '1', '/', '1', '5', '0', '2', '6', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '9', '6', '5', '0', '3', '9', '9', '7', '9', '5', '1', '/', '1', '0', '0', '1', '7', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '7', '3', '9', '2', '2', '7', '1', '0', '1', '0', '1', '/', '1', '0', '0', '1', '7', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '7', '9', '6', '5', '3', '3', '2', '3', '2', '7', '/', '3', '3', '3', '9', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0136392Acc00600 : List (String × SourceJson) := (fragment0136392Field005Key00, fragment0136392Field005Value00) :: fragment0136392Acc00500
noncomputable def fragment0136392Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '4', '8', '5', '6', '7', '6', '4', '8', '8', '8', '1', '/', '7', '5', '1', '3', '0', '6', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '9', '3', '9', '2', '2', '8', '9', '9', '7', '4', '6', '9', '/', '3', '0', '0', '5', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '0', '4', '2', '2', '8', '3', '9', '2', '5', '4', '1', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '0', '5', '8', '8', '0', '1', '6', '7', '8', '9', '9', '9', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '2', '4', '1', '4', '4', '9', '9', '9', '4', '7', '1', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '2', '5', '5', '7', '3', '9', '9', '8', '2', '9', '1', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '1', '0', '8', '4', '1', '2', '3', '1', '9', '9', '1', '/', '1', '5', '0', '2', '6', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '9', '6', '5', '0', '3', '9', '9', '7', '9', '5', '1', '/', '1', '0', '0', '1', '7', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '7', '3', '9', '2', '2', '7', '1', '0', '1', '0', '1', '/', '1', '0', '0', '1', '7', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '7', '9', '6', '5', '3', '3', '2', '3', '2', '7', '/', '3', '3', '3', '9', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0136392_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0136392Field005Chars00 ++ tail)) fragment0136392Acc00500 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0136392Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136392_object_field_005"
  err.flush

noncomputable def fragment0136392Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0136392Field006Value00 : SourceJson := .str (String.ofList ['3', '0', '7', '8', '8', '4', '5', '0', '8', '2', '3', '9', '2', '7', '7', '3', '5', '2', '8', '3', '8', '4', '7', '3', '5', '9', '4', '1', '8', '2', '8', '9', '6', '3', '6', '2', '0', '6', '1', '8', '2', '4', '0', '0', '0', '0', '0', '/', '7', '3', '9', '2', '4', '4', '3', '8', '3', '4', '7', '3', '6', '6', '6', '7', '6', '3', '5', '9', '1', '9', '7', '5', '4', '5', '2', '6', '9', '9', '0', '8', '1', '7', '6', '5', '8', '3', '6', '1', '1', '3', '3', '3', '8', '2', '3', '2', '6', '2', '5', '9', '8', '3', '4', '1', '7', '2', '4', '0', '6', '0', '4', '7'])
noncomputable def fragment0136392Acc00700 : List (String × SourceJson) := (fragment0136392Field006Key00, fragment0136392Field006Value00) :: fragment0136392Acc00600
noncomputable def fragment0136392Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '7', '8', '8', '4', '5', '0', '8', '2', '3', '9', '2', '7', '7', '3', '5', '2', '8', '3', '8', '4', '7', '3', '5', '9', '4', '1', '8', '2', '8', '9', '6', '3', '6', '2', '0', '6', '1', '8', '2', '4', '0', '0', '0', '0', '0', '/', '7', '3', '9', '2', '4', '4', '3', '8', '3', '4', '7', '3', '6', '6', '6', '7', '6', '3', '5', '9', '1', '9', '7', '5', '4', '5', '2', '6', '9', '9', '0', '8', '1', '7', '6', '5', '8', '3', '6', '1', '1', '3', '3', '3', '8', '2', '3', '2', '6', '2', '5', '9', '8', '3', '4', '1', '7', '2', '4', '0', '6', '0', '4', '7', '"', ',']

theorem object_fragment0136392_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0136392Field006Chars00 ++ tail)) fragment0136392Acc00600 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0136392Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136392_object_field_006"
  err.flush

noncomputable def fragment0136392Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0136392Field007Value00 : SourceJson := .str (String.ofList ['2', '3', '3', '2', '7', '6', '0', '8', '3', '5', '0', '0', '5', '9', '5', '0', '0', '3', '8', '5', '4', '5', '4', '0', '9', '3', '6', '0', '1', '7', '7', '3', '7', '6', '3', '6', '3', '3', '9', '7', '2', '1', '7', '2', '7', '7', '6', '9', '0', '2', '3', '7', '5', '0', '8', '4', '3', '2', '0', '6', '3', '5', '7', '2', '8', '3', '9', '6', '0', '1', '5', '8', '3', '5', '5', '7', '3', '9', '7', '7', '8', '3', '9', '0', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '4', '4', '2', '5', '2', '7', '5', '1', '5', '9', '1', '0', '6', '2', '9', '1', '5', '2', '5', '3', '2', '1', '7', '0', '5', '6', '5', '5', '1', '1', '2', '1', '3', '2', '3', '7', '4', '7', '5', '6', '1', '1', '2', '5', '2', '5', '4', '5', '1', '6', '0', '4', '7', '5', '9', '6', '1', '6', '3', '4', '7', '2', '2', '5', '0', '3', '8', '1', '5', '1', '7', '8', '0', '0', '8', '8', '6', '7', '2', '8', '3', '2', '5', '5', '6', '1', '4', '3', '0', '0', '5', '2', '6', '5', '7', '9', '6', '9', '6', '9', '5', '5', '4', '8', '4', '4', '4', '3', '1', '7', '3', '0', '0', '2', '2', '6', '3', '0', '1', '5', '0', '6', '9', '0', '7'])
noncomputable def fragment0136392Acc00800 : List (String × SourceJson) := (fragment0136392Field007Key00, fragment0136392Field007Value00) :: fragment0136392Acc00700
noncomputable def fragment0136392Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '3', '3', '2', '7', '6', '0', '8', '3', '5', '0', '0', '5', '9', '5', '0', '0', '3', '8', '5', '4', '5', '4', '0', '9', '3', '6', '0', '1', '7', '7', '3', '7', '6', '3', '6', '3', '3', '9', '7', '2', '1', '7', '2', '7', '7', '6', '9', '0', '2', '3', '7', '5', '0', '8', '4', '3', '2', '0', '6', '3', '5', '7', '2', '8', '3', '9', '6', '0', '1', '5', '8', '3', '5', '5', '7', '3', '9', '7', '7', '8', '3', '9', '0', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '4', '4', '2', '5', '2', '7', '5', '1', '5', '9', '1', '0', '6', '2', '9', '1', '5', '2', '5', '3', '2', '1', '7', '0', '5', '6', '5', '5', '1', '1', '2', '1', '3', '2', '3', '7', '4', '7', '5', '6', '1', '1', '2', '5', '2', '5', '4', '5', '1', '6', '0', '4', '7', '5', '9', '6', '1', '6', '3', '4', '7', '2', '2', '5', '0', '3', '8', '1', '5', '1', '7', '8', '0', '0', '8', '8', '6', '7', '2', '8', '3', '2', '5', '5', '6', '1', '4', '3', '0', '0', '5', '2', '6', '5', '7', '9', '6', '9', '6', '9', '5', '5', '4', '8', '4', '4', '4', '3', '1', '7', '3', '0', '0', '2', '2', '6', '3', '0', '1', '5', '0', '6', '9', '0', '7', '"', ',']

theorem object_fragment0136392_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0136392Field007Chars00 ++ tail)) fragment0136392Acc00700 =
      SourceJson.object (fuel + 240) (SourceJson.white tail) fragment0136392Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136392_object_field_007"
  err.flush

noncomputable def fragment0136392Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0136392Field008Value00 : SourceJson := .str (String.ofList ['3', '2', '9', '9', '7', '3', '7', '4', '6', '1', '6', '2'])
noncomputable def fragment0136392Acc00900 : List (String × SourceJson) := (fragment0136392Field008Key00, fragment0136392Field008Value00) :: fragment0136392Acc00800
noncomputable def fragment0136392Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '9', '9', '7', '3', '7', '4', '6', '1', '6', '2', '"', ',']

theorem object_fragment0136392_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 240) (SourceJson.white (fragment0136392Field008Chars00 ++ tail)) fragment0136392Acc00800 =
      SourceJson.object (fuel + 239) (SourceJson.white tail) fragment0136392Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136392_object_field_008"
  err.flush

noncomputable def fragment0136392Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0136392Field009Value00 : SourceJson := .str (String.ofList ['1', '1', '2', '4', '0', '3', '8', '5', '9', '0', '5', '6', '2'])
noncomputable def fragment0136392Acc01000 : List (String × SourceJson) := (fragment0136392Field009Key00, fragment0136392Field009Value00) :: fragment0136392Acc00900
noncomputable def fragment0136392Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '2', '4', '0', '3', '8', '5', '9', '0', '5', '6', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0136392_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0136392Field009Chars00 ++ tail)) fragment0136392Acc00900 =
      .ok (.obj (fragment0136392Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136392_object_field_009"
  err.flush

noncomputable def fragment0136392Chars : List Char := '{' :: (fragment0136392Field000Chars00 ++ fragment0136392Field001Chars00 ++ fragment0136392Field002Chars00 ++ fragment0136392Field003Chars00 ++ fragment0136392Field004Chars00 ++ fragment0136392Field005Chars00 ++ fragment0136392Field006Chars00 ++ fragment0136392Field007Chars00 ++ fragment0136392Field008Chars00 ++ fragment0136392Field009Chars00)
noncomputable def fragment0136392Value : SourceJson := .obj (fragment0136392Acc01000.reverse)

theorem value_fragment0136392 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 249) (fragment0136392Chars ++ tail) =
      .ok (fragment0136392Value, tail) := by
  have hinput : fragment0136392Chars ++ tail = '{' :: (fragment0136392Field000Chars00 ++ (fragment0136392Field001Chars00 ++ (fragment0136392Field002Chars00 ++ (fragment0136392Field003Chars00 ++ (fragment0136392Field004Chars00 ++ (fragment0136392Field005Chars00 ++ (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0136392Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 249) (fragment0136392Chars ++ tail) =
        SourceJson.value (fuel + 249) ('{' :: (fragment0136392Field000Chars00 ++ (fragment0136392Field001Chars00 ++ (fragment0136392Field002Chars00 ++ (fragment0136392Field003Chars00 ++ (fragment0136392Field004Chars00 ++ (fragment0136392Field005Chars00 ++ (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 249)) hinput
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0136392Field000Chars00 ++ (fragment0136392Field001Chars00 ++ (fragment0136392Field002Chars00 ++ (fragment0136392Field003Chars00 ++ (fragment0136392Field004Chars00 ++ (fragment0136392Field005Chars00 ++ (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail)))))))))))) fragment0136392Acc00000 := by rfl
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0136392Field001Chars00 ++ (fragment0136392Field002Chars00 ++ (fragment0136392Field003Chars00 ++ (fragment0136392Field004Chars00 ++ (fragment0136392Field005Chars00 ++ (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail))))))))))) fragment0136392Acc00100 := object_fragment0136392_field_000 fuel (fragment0136392Field001Chars00 ++ (fragment0136392Field002Chars00 ++ (fragment0136392Field003Chars00 ++ (fragment0136392Field004Chars00 ++ (fragment0136392Field005Chars00 ++ (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0136392Field002Chars00 ++ (fragment0136392Field003Chars00 ++ (fragment0136392Field004Chars00 ++ (fragment0136392Field005Chars00 ++ (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail)))))))))) fragment0136392Acc00200 := object_fragment0136392_field_001 fuel (fragment0136392Field002Chars00 ++ (fragment0136392Field003Chars00 ++ (fragment0136392Field004Chars00 ++ (fragment0136392Field005Chars00 ++ (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0136392Field003Chars00 ++ (fragment0136392Field004Chars00 ++ (fragment0136392Field005Chars00 ++ (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail))))))))) fragment0136392Acc00300 := object_fragment0136392_field_002 fuel (fragment0136392Field003Chars00 ++ (fragment0136392Field004Chars00 ++ (fragment0136392Field005Chars00 ++ (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0136392Field004Chars00 ++ (fragment0136392Field005Chars00 ++ (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail)))))))) fragment0136392Acc00400 := object_fragment0136392_field_003 fuel (fragment0136392Field004Chars00 ++ (fragment0136392Field005Chars00 ++ (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0136392Field005Chars00 ++ (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail))))))) fragment0136392Acc00500 := object_fragment0136392_field_004 fuel (fragment0136392Field005Chars00 ++ (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail)))))) fragment0136392Acc00600 := object_fragment0136392_field_005 fuel (fragment0136392Field006Chars00 ++ (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail))))) fragment0136392Acc00700 := object_fragment0136392_field_006 fuel (fragment0136392Field007Chars00 ++ (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 240) (SourceJson.white (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail)))) fragment0136392Acc00800 := object_fragment0136392_field_007 fuel (fragment0136392Field008Chars00 ++ (fragment0136392Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0136392Field009Chars00 ++ (tail))) fragment0136392Acc00900 := object_fragment0136392_field_008 fuel (fragment0136392Field009Chars00 ++ (tail))
    _ = .ok (fragment0136392Value, tail) := object_fragment0136392_field_009 fuel (tail)

noncomputable def fragment0138011Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0138011Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0138011Field000Value00 : SourceJson := .number (String.ofList ['2', '0'])
noncomputable def fragment0138011Acc00100 : List (String × SourceJson) := (fragment0138011Field000Key00, fragment0138011Field000Value00) :: fragment0138011Acc00000
noncomputable def fragment0138011Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '0', ',']

theorem object_fragment0138011_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 405) (SourceJson.white (fragment0138011Field000Chars00 ++ tail)) fragment0138011Acc00000 =
      SourceJson.object (fuel + 404) (SourceJson.white tail) fragment0138011Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138011_object_field_000"
  err.flush

noncomputable def fragment0138011Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0138011Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0138011Acc00200 : List (String × SourceJson) := (fragment0138011Field001Key00, fragment0138011Field001Value00) :: fragment0138011Acc00100
noncomputable def fragment0138011Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0138011_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 404) (SourceJson.white (fragment0138011Field001Chars00 ++ tail)) fragment0138011Acc00100 =
      SourceJson.object (fuel + 403) (SourceJson.white tail) fragment0138011Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138011_object_field_001"
  err.flush

noncomputable def fragment0138011Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0138011Field002Value00 : SourceJson := .str (String.ofList ['6', '2', '9', '0', '1', '7', '6', '4', '6', '3', '7', '9', '3', '1', '1', '9', '3', '7', '7', '7', '7', '8', '1', '4', '5', '2', '1', '0', '9', '7', '9', '8', '7', '4', '9', '3', '4', '6', '1', '/', '2', '5', '2', '3', '8', '1', '2', '8', '3', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0138011Acc00300 : List (String × SourceJson) := (fragment0138011Field002Key00, fragment0138011Field002Value00) :: fragment0138011Acc00200
noncomputable def fragment0138011Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '2', '9', '0', '1', '7', '6', '4', '6', '3', '7', '9', '3', '1', '1', '9', '3', '7', '7', '7', '7', '8', '1', '4', '5', '2', '1', '0', '9', '7', '9', '8', '7', '4', '9', '3', '4', '6', '1', '/', '2', '5', '2', '3', '8', '1', '2', '8', '3', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0138011_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 403) (SourceJson.white (fragment0138011Field002Chars00 ++ tail)) fragment0138011Acc00200 =
      SourceJson.object (fuel + 402) (SourceJson.white tail) fragment0138011Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138011_object_field_002"
  err.flush

noncomputable def fragment0138011Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0138011Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '2', '4', '1', '6', '9', '/', '1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0138011Acc00400 : List (String × SourceJson) := (fragment0138011Field003Key00, fragment0138011Field003Value00) :: fragment0138011Acc00300
noncomputable def fragment0138011Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '8', '2', '4', '1', '6', '9', '/', '1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0138011_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 402) (SourceJson.white (fragment0138011Field003Chars00 ++ tail)) fragment0138011Acc00300 =
      SourceJson.object (fuel + 401) (SourceJson.white tail) fragment0138011Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138011_object_field_003"
  err.flush

noncomputable def fragment0138011Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0138011Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0138011Acc00500 : List (String × SourceJson) := (fragment0138011Field004Key00, fragment0138011Field004Value00) :: fragment0138011Acc00400
noncomputable def fragment0138011Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0138011_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 401) (SourceJson.white (fragment0138011Field004Chars00 ++ tail)) fragment0138011Acc00400 =
      SourceJson.object (fuel + 400) (SourceJson.white tail) fragment0138011Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138011_object_field_004"
  err.flush

noncomputable def fragment0138011Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0138011Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '7', '6', '1', '0', '5', '4', '0', '9', '2', '1', '9', '7', '3', '8', '2', '9', '4', '6', '3', '1', '1', '/', '5', '2', '0', '4', '6', '5', '1', '8', '5', '7', '1', '5', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '9', '9', '9', '6', '8', '9', '2', '7', '8', '3', '5', '4', '1', '1', '9', '0', '5', '0', '3', '/', '1', '6', '2', '6', '4', '5', '3', '7', '0', '5', '3', '5', '9', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '8', '8', '3', '6', '1', '8', '5', '1', '4', '7', '9', '4', '7', '1', '2', '1', '2', '1', '/', '3', '4', '6', '9', '7', '6', '7', '9', '0', '4', '7', '6', '7', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '0', '5', '3', '0', '5', '2', '5', '2', '6', '3', '3', '6', '7', '6', '1', '2', '7', '5', '1', '/', '6', '5', '0', '5', '8', '1', '4', '8', '2', '1', '4', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '1', '8', '9', '8', '8', '8', '9', '2', '9', '8', '5', '0', '7', '0', '9', '9', '3', '7', '/', '5', '4', '2', '1', '5', '1', '2', '3', '5', '1', '1', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '5', '9', '1', '6', '9', '1', '3', '1', '1', '0', '6', '3', '5', '9', '2', '5', '4', '3', '/', '4', '3', '3', '7', '2', '0', '9', '8', '8', '0', '9', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '7', '9', '5', '4', '1', '2', '4', '9', '5', '8', '3', '5', '1', '0', '4', '3', '5', '1', '/', '2', '8', '9', '1', '4', '7', '3', '2', '5', '3', '9', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '4', '4', '7', '9', '4', '6', '0', '6', '5', '0', '6', '6', '5', '4', '0', '9', '4', '1', '1', '/', '2', '6', '0', '2', '3', '2', '5', '9', '2', '8', '5', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '4', '7', '9', '3', '4', '0', '9', '3', '9', '2', '0', '7', '3', '5', '5', '1', '2', '1', '1', '/', '2', '6', '0', '2', '3', '2', '5', '9', '2', '8', '5', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '1', '2', '7', '9', '8', '8', '1', '8', '4', '4', '1', '4', '9', '7', '6', '1', '4', '1', '/', '1', '6', '2', '6', '4', '5', '3', '7', '0', '5', '3', '5', '9', '7', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0138011Acc00600 : List (String × SourceJson) := (fragment0138011Field005Key00, fragment0138011Field005Value00) :: fragment0138011Acc00500
noncomputable def fragment0138011Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '6', '1', '0', '5', '4', '0', '9', '2', '1', '9', '7', '3', '8', '2', '9', '4', '6', '3', '1', '1', '/', '5', '2', '0', '4', '6', '5', '1', '8', '5', '7', '1', '5', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '9', '9', '6', '8', '9', '2', '7', '8', '3', '5', '4', '1', '1', '9', '0', '5', '0', '3', '/', '1', '6', '2', '6', '4', '5', '3', '7', '0', '5', '3', '5', '9', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '8', '8', '3', '6', '1', '8', '5', '1', '4', '7', '9', '4', '7', '1', '2', '1', '2', '1', '/', '3', '4', '6', '9', '7', '6', '7', '9', '0', '4', '7', '6', '7', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '0', '5', '3', '0', '5', '2', '5', '2', '6', '3', '3', '6', '7', '6', '1', '2', '7', '5', '1', '/', '6', '5', '0', '5', '8', '1', '4', '8', '2', '1', '4', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '1', '8', '9', '8', '8', '8', '9', '2', '9', '8', '5', '0', '7', '0', '9', '9', '3', '7', '/', '5', '4', '2', '1', '5', '1', '2', '3', '5', '1', '1', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '5', '9', '1', '6', '9', '1', '3', '1', '1', '0', '6', '3', '5', '9', '2', '5', '4', '3', '/', '4', '3', '3', '7', '2', '0', '9', '8', '8', '0', '9', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '7', '9', '5', '4', '1', '2', '4', '9', '5', '8', '3', '5', '1', '0', '4', '3', '5', '1', '/', '2', '8', '9', '1', '4', '7', '3', '2', '5', '3', '9', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '5', '4', '4', '7', '9', '4', '6', '0', '6', '5', '0', '6', '6', '5', '4', '0', '9', '4', '1', '1', '/', '2', '6', '0', '2', '3', '2', '5', '9', '2', '8', '5', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '4', '7', '9', '3', '4', '0', '9', '3', '9', '2', '0', '7', '3', '5', '5', '1', '2', '1', '1', '/', '2', '6', '0', '2', '3', '2', '5', '9', '2', '8', '5', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '1', '2', '7', '9', '8', '8', '1', '8', '4', '4', '1', '4', '9', '7', '6', '1', '4', '1', '/', '1', '6', '2', '6', '4', '5', '3', '7', '0', '5', '3', '5', '9', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0138011_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0138011Field005Chars00 ++ tail)) fragment0138011Acc00500 =
      SourceJson.object (fuel + 399) (SourceJson.white tail) fragment0138011Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138011_object_field_005"
  err.flush

noncomputable def fragment0138011Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0138011Field006Value00 : SourceJson := .str (String.ofList ['3', '7', '9', '8', '5', '6', '7', '6', '2', '4', '1', '0', '9', '0', '6', '0', '9', '1', '1', '7', '8', '6', '5', '4', '7', '7', '8', '8', '9', '2', '2', '0', '0', '4', '5', '0', '8', '9', '9', '1', '9', '0', '5', '3', '4', '4', '0', '0', '0', '0', '0', '/', '1', '7', '2', '4', '8', '8', '6', '8', '9', '7', '8', '1', '6', '8', '0', '3', '2', '1', '0', '4', '2', '2', '5', '8', '0', '3', '1', '4', '8', '7', '0', '5', '0', '8', '0', '6', '0', '3', '8', '9', '3', '6', '0', '2', '7', '6', '0', '5', '5', '9', '8', '0', '9', '7', '4', '5', '2', '3', '1', '7', '2', '7', '8', '9', '9'])
noncomputable def fragment0138011Acc00700 : List (String × SourceJson) := (fragment0138011Field006Key00, fragment0138011Field006Value00) :: fragment0138011Acc00600
noncomputable def fragment0138011Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '7', '9', '8', '5', '6', '7', '6', '2', '4', '1', '0', '9', '0', '6', '0', '9', '1', '1', '7', '8', '6', '5', '4', '7', '7', '8', '8', '9', '2', '2', '0', '0', '4', '5', '0', '8', '9', '9', '1', '9', '0', '5', '3', '4', '4', '0', '0', '0', '0', '0', '/', '1', '7', '2', '4', '8', '8', '6', '8', '9', '7', '8', '1', '6', '8', '0', '3', '2', '1', '0', '4', '2', '2', '5', '8', '0', '3', '1', '4', '8', '7', '0', '5', '0', '8', '0', '6', '0', '3', '8', '9', '3', '6', '0', '2', '7', '6', '0', '5', '5', '9', '8', '0', '9', '7', '4', '5', '2', '3', '1', '7', '2', '7', '8', '9', '9', '"', ',']

theorem object_fragment0138011_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 399) (SourceJson.white (fragment0138011Field006Chars00 ++ tail)) fragment0138011Acc00600 =
      SourceJson.object (fuel + 398) (SourceJson.white tail) fragment0138011Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138011_object_field_006"
  err.flush

noncomputable def fragment0138011Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0138011Field007Value00 : SourceJson := .str (String.ofList ['7', '8', '8', '5', '1', '4', '1', '7', '8', '4', '5', '2', '9', '4', '0', '3', '5', '6', '5', '4', '2', '6', '4', '0', '4', '2', '0', '1', '8', '3', '6', '7', '4', '9', '0', '3', '6', '4', '4', '3', '7', '9', '7', '3', '8', '9', '8', '3', '7', '9', '8', '6', '6', '7', '1', '4', '5', '0', '9', '6', '1', '0', '4', '7', '1', '8', '0', '3', '4', '7', '4', '7', '5', '8', '3', '8', '0', '4', '5', '6', '5', '1', '8', '4', '0', '4', '6', '1', '7', '0', '4', '4', '5', '4', '0', '1', '7', '7', '1', '7', '5', '8', '7', '4', '8', '3', '5', '5', '0', '6', '6', '5', '8', '2', '2', '1', '5', '8', '5', '4', '3', '6', '0', '3', '9', '5', '8', '4', '2', '2', '1', '7', '0', '3', '8', '7', '5', '6', '6', '1', '1', '9', '5', '7', '0', '1', '5', '8', '5', '1', '9', '1', '8', '8', '7', '1', '5', '4', '2', '3', '6', '6', '3', '0', '6', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '4', '1', '7', '9', '7', '8', '7', '3', '1', '8', '9', '4', '3', '2', '5', '0', '6', '1', '9', '5', '1', '6', '0', '0', '0', '0', '5', '0', '6', '4', '3', '8', '6', '0', '0', '4', '5', '0', '7', '1', '1', '8', '5', '6', '3', '1', '8', '7', '3', '8', '1', '9', '3', '8', '0', '4', '0', '9', '4', '2', '9', '9', '5', '1', '4', '6', '9', '7', '2', '0', '5', '5', '5', '5', '4', '0', '6', '0', '9', '6', '3', '6', '5', '5', '0', '3', '0', '9', '0', '7', '7', '4', '4', '6', '5', '2', '7', '7', '3', '3', '6', '4', '1', '7', '4', '7', '1', '4', '2', '0', '7', '4', '1', '7', '5', '7', '5', '2', '1', '7', '4', '0', '3', '5', '0', '1', '7', '5', '3', '4', '3', '7', '2', '3', '6', '5', '1', '6', '6', '5', '1', '2', '9', '7', '0', '1', '4', '3', '9', '7', '7', '7', '3', '9', '0', '2', '4', '5', '6', '2', '0', '0', '6', '6', '2', '2', '0', '6', '3', '8', '6', '6', '4', '5', '4', '9', '9', '3', '5', '9', '3', '1', '8', '2', '6', '8', '8', '6', '9', '4', '3', '1', '9', '6', '1', '9', '0', '1', '1', '2', '4', '3'])
noncomputable def fragment0138011Acc00800 : List (String × SourceJson) := (fragment0138011Field007Key00, fragment0138011Field007Value00) :: fragment0138011Acc00700
noncomputable def fragment0138011Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '8', '8', '5', '1', '4', '1', '7', '8', '4', '5', '2', '9', '4', '0', '3', '5', '6', '5', '4', '2', '6', '4', '0', '4', '2', '0', '1', '8', '3', '6', '7', '4', '9', '0', '3', '6', '4', '4', '3', '7', '9', '7', '3', '8', '9', '8', '3', '7', '9', '8', '6', '6', '7', '1', '4', '5', '0', '9', '6', '1', '0', '4', '7', '1', '8', '0', '3', '4', '7', '4', '7', '5', '8', '3', '8', '0', '4', '5', '6', '5', '1', '8', '4', '0', '4', '6', '1', '7', '0', '4', '4', '5', '4', '0', '1', '7', '7', '1', '7', '5', '8', '7', '4', '8', '3', '5', '5', '0', '6', '6', '5', '8', '2', '2', '1', '5', '8', '5', '4', '3', '6', '0', '3', '9', '5', '8', '4', '2', '2', '1', '7', '0', '3', '8', '7', '5', '6', '6', '1', '1', '9', '5', '7', '0', '1', '5', '8', '5', '1', '9', '1', '8', '8', '7', '1', '5', '4', '2', '3', '6', '6', '3', '0', '6', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '4', '1', '7', '9', '7', '8', '7', '3', '1', '8', '9', '4', '3', '2', '5', '0', '6', '1', '9', '5', '1', '6', '0', '0', '0', '0', '5', '0', '6', '4', '3', '8', '6', '0', '0', '4', '5', '0', '7', '1', '1', '8', '5', '6', '3', '1', '8', '7', '3', '8', '1', '9', '3', '8', '0', '4', '0', '9', '4', '2', '9', '9', '5', '1', '4', '6', '9', '7', '2', '0', '5', '5', '5', '5', '4', '0', '6', '0', '9', '6', '3', '6', '5', '5', '0', '3', '0', '9', '0', '7', '7', '4', '4', '6', '5', '2', '7', '7', '3', '3', '6', '4', '1', '7', '4', '7', '1', '4', '2', '0', '7', '4', '1', '7', '5', '7', '5', '2', '1', '7', '4', '0', '3', '5', '0', '1', '7', '5', '3', '4', '3', '7', '2', '3', '6', '5', '1', '6', '6', '5', '1', '2', '9', '7', '0', '1', '4', '3', '9', '7', '7', '7', '3', '9', '0', '2', '4', '5', '6', '2', '0', '0', '6', '6', '2', '2', '0', '6', '3', '8', '6', '6', '4', '5', '4', '9', '9', '3', '5', '9', '3', '1', '8', '2', '6', '8', '8', '6', '9', '4', '3', '1', '9', '6', '1', '9', '0', '1', '1', '2', '4', '3', '"', ',']

theorem object_fragment0138011_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 398) (SourceJson.white (fragment0138011Field007Chars00 ++ tail)) fragment0138011Acc00700 =
      SourceJson.object (fuel + 397) (SourceJson.white tail) fragment0138011Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138011_object_field_007"
  err.flush

noncomputable def fragment0138011Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0138011Field008Value00 : SourceJson := .str (String.ofList ['1', '7', '4', '4', '7', '7', '2', '5', '6', '1', '1', '7', '6', '3', '5', '2'])
noncomputable def fragment0138011Acc00900 : List (String × SourceJson) := (fragment0138011Field008Key00, fragment0138011Field008Value00) :: fragment0138011Acc00800
noncomputable def fragment0138011Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '4', '4', '7', '7', '2', '5', '6', '1', '1', '7', '6', '3', '5', '2', '"', ',']

theorem object_fragment0138011_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 397) (SourceJson.white (fragment0138011Field008Chars00 ++ tail)) fragment0138011Acc00800 =
      SourceJson.object (fuel + 396) (SourceJson.white tail) fragment0138011Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138011_object_field_008"
  err.flush

noncomputable def fragment0138011Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0138011Field009Value00 : SourceJson := .str (String.ofList ['5', '9', '9', '6', '6', '0', '7', '5', '0', '7', '3', '6', '7', '3', '7', '8'])
noncomputable def fragment0138011Acc01000 : List (String × SourceJson) := (fragment0138011Field009Key00, fragment0138011Field009Value00) :: fragment0138011Acc00900
noncomputable def fragment0138011Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '9', '6', '6', '0', '7', '5', '0', '7', '3', '6', '7', '3', '7', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0138011_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 396) (SourceJson.white (fragment0138011Field009Chars00 ++ tail)) fragment0138011Acc00900 =
      .ok (.obj (fragment0138011Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138011_object_field_009"
  err.flush

noncomputable def fragment0138011Chars : List Char := '{' :: (fragment0138011Field000Chars00 ++ fragment0138011Field001Chars00 ++ fragment0138011Field002Chars00 ++ fragment0138011Field003Chars00 ++ fragment0138011Field004Chars00 ++ fragment0138011Field005Chars00 ++ fragment0138011Field006Chars00 ++ fragment0138011Field007Chars00 ++ fragment0138011Field008Chars00 ++ fragment0138011Field009Chars00)
noncomputable def fragment0138011Value : SourceJson := .obj (fragment0138011Acc01000.reverse)

theorem value_fragment0138011 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 406) (fragment0138011Chars ++ tail) =
      .ok (fragment0138011Value, tail) := by
  have hinput : fragment0138011Chars ++ tail = '{' :: (fragment0138011Field000Chars00 ++ (fragment0138011Field001Chars00 ++ (fragment0138011Field002Chars00 ++ (fragment0138011Field003Chars00 ++ (fragment0138011Field004Chars00 ++ (fragment0138011Field005Chars00 ++ (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0138011Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 406) (fragment0138011Chars ++ tail) =
        SourceJson.value (fuel + 406) ('{' :: (fragment0138011Field000Chars00 ++ (fragment0138011Field001Chars00 ++ (fragment0138011Field002Chars00 ++ (fragment0138011Field003Chars00 ++ (fragment0138011Field004Chars00 ++ (fragment0138011Field005Chars00 ++ (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 406)) hinput
    _ = SourceJson.object (fuel + 405) (SourceJson.white (fragment0138011Field000Chars00 ++ (fragment0138011Field001Chars00 ++ (fragment0138011Field002Chars00 ++ (fragment0138011Field003Chars00 ++ (fragment0138011Field004Chars00 ++ (fragment0138011Field005Chars00 ++ (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail)))))))))))) fragment0138011Acc00000 := by rfl
    _ = SourceJson.object (fuel + 404) (SourceJson.white (fragment0138011Field001Chars00 ++ (fragment0138011Field002Chars00 ++ (fragment0138011Field003Chars00 ++ (fragment0138011Field004Chars00 ++ (fragment0138011Field005Chars00 ++ (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail))))))))))) fragment0138011Acc00100 := object_fragment0138011_field_000 fuel (fragment0138011Field001Chars00 ++ (fragment0138011Field002Chars00 ++ (fragment0138011Field003Chars00 ++ (fragment0138011Field004Chars00 ++ (fragment0138011Field005Chars00 ++ (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 403) (SourceJson.white (fragment0138011Field002Chars00 ++ (fragment0138011Field003Chars00 ++ (fragment0138011Field004Chars00 ++ (fragment0138011Field005Chars00 ++ (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail)))))))))) fragment0138011Acc00200 := object_fragment0138011_field_001 fuel (fragment0138011Field002Chars00 ++ (fragment0138011Field003Chars00 ++ (fragment0138011Field004Chars00 ++ (fragment0138011Field005Chars00 ++ (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 402) (SourceJson.white (fragment0138011Field003Chars00 ++ (fragment0138011Field004Chars00 ++ (fragment0138011Field005Chars00 ++ (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail))))))))) fragment0138011Acc00300 := object_fragment0138011_field_002 fuel (fragment0138011Field003Chars00 ++ (fragment0138011Field004Chars00 ++ (fragment0138011Field005Chars00 ++ (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 401) (SourceJson.white (fragment0138011Field004Chars00 ++ (fragment0138011Field005Chars00 ++ (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail)))))))) fragment0138011Acc00400 := object_fragment0138011_field_003 fuel (fragment0138011Field004Chars00 ++ (fragment0138011Field005Chars00 ++ (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0138011Field005Chars00 ++ (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail))))))) fragment0138011Acc00500 := object_fragment0138011_field_004 fuel (fragment0138011Field005Chars00 ++ (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 399) (SourceJson.white (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail)))))) fragment0138011Acc00600 := object_fragment0138011_field_005 fuel (fragment0138011Field006Chars00 ++ (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 398) (SourceJson.white (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail))))) fragment0138011Acc00700 := object_fragment0138011_field_006 fuel (fragment0138011Field007Chars00 ++ (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 397) (SourceJson.white (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail)))) fragment0138011Acc00800 := object_fragment0138011_field_007 fuel (fragment0138011Field008Chars00 ++ (fragment0138011Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 396) (SourceJson.white (fragment0138011Field009Chars00 ++ (tail))) fragment0138011Acc00900 := object_fragment0138011_field_008 fuel (fragment0138011Field009Chars00 ++ (tail))
    _ = .ok (fragment0138011Value, tail) := object_fragment0138011_field_009 fuel (tail)

noncomputable def fragment0139954Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0139954Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0139954Field000Value00 : SourceJson := .number (String.ofList ['2', '1'])
noncomputable def fragment0139954Acc00100 : List (String × SourceJson) := (fragment0139954Field000Key00, fragment0139954Field000Value00) :: fragment0139954Acc00000
noncomputable def fragment0139954Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '1', ',']

theorem object_fragment0139954_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 270) (SourceJson.white (fragment0139954Field000Chars00 ++ tail)) fragment0139954Acc00000 =
      SourceJson.object (fuel + 269) (SourceJson.white tail) fragment0139954Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0139954_object_field_000"
  err.flush

noncomputable def fragment0139954Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0139954Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0139954Acc00200 : List (String × SourceJson) := (fragment0139954Field001Key00, fragment0139954Field001Value00) :: fragment0139954Acc00100
noncomputable def fragment0139954Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0139954_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 269) (SourceJson.white (fragment0139954Field001Chars00 ++ tail)) fragment0139954Acc00100 =
      SourceJson.object (fuel + 268) (SourceJson.white tail) fragment0139954Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0139954_object_field_001"
  err.flush

noncomputable def fragment0139954Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0139954Field002Value00 : SourceJson := .str (String.ofList ['4', '4', '9', '2', '0', '6', '5', '8', '1', '7', '9', '6', '8', '7', '4', '7', '7', '4', '1', '6', '7', '3', '0', '6', '9', '6', '9', '4', '4', '6', '9', '5', '1', '5', '9', '7', '4', '1', '/', '7', '0', '2', '5', '3', '1', '9', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0139954Acc00300 : List (String × SourceJson) := (fragment0139954Field002Key00, fragment0139954Field002Value00) :: fragment0139954Acc00200
noncomputable def fragment0139954Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '4', '9', '2', '0', '6', '5', '8', '1', '7', '9', '6', '8', '7', '4', '7', '7', '4', '1', '6', '7', '3', '0', '6', '9', '6', '9', '4', '4', '6', '9', '5', '1', '5', '9', '7', '4', '1', '/', '7', '0', '2', '5', '3', '1', '9', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0139954_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 268) (SourceJson.white (fragment0139954Field002Chars00 ++ tail)) fragment0139954Acc00200 =
      SourceJson.object (fuel + 267) (SourceJson.white tail) fragment0139954Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0139954_object_field_002"
  err.flush

noncomputable def fragment0139954Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0139954Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0139954Acc00400 : List (String × SourceJson) := (fragment0139954Field003Key00, fragment0139954Field003Value00) :: fragment0139954Acc00300
noncomputable def fragment0139954Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0139954_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 267) (SourceJson.white (fragment0139954Field003Chars00 ++ tail)) fragment0139954Acc00300 =
      SourceJson.object (fuel + 266) (SourceJson.white tail) fragment0139954Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0139954_object_field_003"
  err.flush

noncomputable def fragment0139954Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0139954Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0139954Acc00500 : List (String × SourceJson) := (fragment0139954Field004Key00, fragment0139954Field004Value00) :: fragment0139954Acc00400
noncomputable def fragment0139954Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0139954_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 266) (SourceJson.white (fragment0139954Field004Chars00 ++ tail)) fragment0139954Acc00400 =
      SourceJson.object (fuel + 265) (SourceJson.white tail) fragment0139954Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0139954_object_field_004"
  err.flush

noncomputable def fragment0139954Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0139954Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '3', '7', '0', '3', '9', '0', '5', '4', '7', '0', '4', '7', '5', '3', '1', '/', '1', '4', '9', '9', '0', '7', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '6', '6', '1', '9', '9', '4', '5', '1', '0', '5', '7', '/', '1', '1', '7', '1', '1', '5', '4', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '0', '3', '4', '4', '3', '1', '6', '7', '8', '5', '0', '1', '7', '/', '4', '9', '9', '6', '9', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '4', '9', '5', '1', '9', '5', '8', '5', '6', '8', '9', '1', '/', '1', '8', '7', '3', '8', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '5', '7', '5', '4', '5', '8', '2', '4', '0', '2', '8', '7', '/', '1', '5', '6', '1', '5', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '1', '2', '4', '2', '5', '6', '1', '3', '9', '7', '9', '/', '1', '2', '4', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '5', '8', '0', '0', '4', '1', '5', '7', '3', '4', '9', '1', '/', '8', '3', '2', '8', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '7', '2', '9', '9', '1', '3', '2', '0', '1', '6', '7', '1', '1', '/', '7', '4', '9', '5', '3', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '5', '3', '8', '9', '5', '5', '2', '1', '9', '9', '1', '1', '/', '7', '4', '9', '5', '3', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '7', '0', '0', '3', '0', '3', '4', '0', '7', '7', '9', '/', '1', '1', '7', '1', '1', '5', '4', '2', '5', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0139954Acc00600 : List (String × SourceJson) := (fragment0139954Field005Key00, fragment0139954Field005Value00) :: fragment0139954Acc00500
noncomputable def fragment0139954Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '0', '3', '9', '0', '5', '4', '7', '0', '4', '7', '5', '3', '1', '/', '1', '4', '9', '9', '0', '7', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '6', '6', '1', '9', '9', '4', '5', '1', '0', '5', '7', '/', '1', '1', '7', '1', '1', '5', '4', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '3', '4', '4', '3', '1', '6', '7', '8', '5', '0', '1', '7', '/', '4', '9', '9', '6', '9', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '4', '9', '5', '1', '9', '5', '8', '5', '6', '8', '9', '1', '/', '1', '8', '7', '3', '8', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '7', '5', '4', '5', '8', '2', '4', '0', '2', '8', '7', '/', '1', '5', '6', '1', '5', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '1', '2', '4', '2', '5', '6', '1', '3', '9', '7', '9', '/', '1', '2', '4', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '5', '8', '0', '0', '4', '1', '5', '7', '3', '4', '9', '1', '/', '8', '3', '2', '8', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '7', '2', '9', '9', '1', '3', '2', '0', '1', '6', '7', '1', '1', '/', '7', '4', '9', '5', '3', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '5', '3', '8', '9', '5', '5', '2', '1', '9', '9', '1', '1', '/', '7', '4', '9', '5', '3', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '7', '0', '0', '3', '0', '3', '4', '0', '7', '7', '9', '/', '1', '1', '7', '1', '1', '5', '4', '2', '5', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0139954_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 265) (SourceJson.white (fragment0139954Field005Chars00 ++ tail)) fragment0139954Acc00500 =
      SourceJson.object (fuel + 264) (SourceJson.white tail) fragment0139954Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0139954_object_field_005"
  err.flush

noncomputable def fragment0139954Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0139954Field006Value00 : SourceJson := .str (String.ofList ['7', '8', '8', '2', '6', '0', '0', '5', '5', '7', '7', '6', '2', '5', '7', '5', '3', '2', '0', '2', '9', '3', '9', '5', '5', '6', '3', '3', '8', '5', '2', '4', '3', '1', '1', '1', '3', '9', '8', '3', '3', '6', '0', '0', '0', '0', '0', '/', '2', '8', '2', '2', '9', '8', '8', '4', '3', '8', '2', '6', '5', '9', '9', '8', '8', '1', '6', '9', '5', '3', '2', '0', '3', '2', '9', '3', '7', '2', '7', '8', '0', '9', '6', '5', '5', '0', '0', '7', '4', '4', '6', '1', '0', '9', '9', '8', '9', '4', '3', '7', '0', '2', '5', '8', '6', '7', '1', '4', '9'])
noncomputable def fragment0139954Acc00700 : List (String × SourceJson) := (fragment0139954Field006Key00, fragment0139954Field006Value00) :: fragment0139954Acc00600
noncomputable def fragment0139954Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '8', '8', '2', '6', '0', '0', '5', '5', '7', '7', '6', '2', '5', '7', '5', '3', '2', '0', '2', '9', '3', '9', '5', '5', '6', '3', '3', '8', '5', '2', '4', '3', '1', '1', '1', '3', '9', '8', '3', '3', '6', '0', '0', '0', '0', '0', '/', '2', '8', '2', '2', '9', '8', '8', '4', '3', '8', '2', '6', '5', '9', '9', '8', '8', '1', '6', '9', '5', '3', '2', '0', '3', '2', '9', '3', '7', '2', '7', '8', '0', '9', '6', '5', '5', '0', '0', '7', '4', '4', '6', '1', '0', '9', '9', '8', '9', '4', '3', '7', '0', '2', '5', '8', '6', '7', '1', '4', '9', '"', ',']

theorem object_fragment0139954_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment0139954Field006Chars00 ++ tail)) fragment0139954Acc00600 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment0139954Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0139954_object_field_006"
  err.flush

noncomputable def fragment0139954Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0139954Field007Value00 : SourceJson := .str (String.ofList ['3', '8', '7', '7', '7', '8', '6', '5', '5', '4', '6', '1', '5', '3', '5', '0', '8', '2', '8', '3', '5', '7', '1', '7', '8', '6', '2', '1', '0', '3', '7', '1', '3', '9', '9', '2', '7', '0', '5', '6', '1', '8', '8', '3', '3', '4', '2', '8', '5', '3', '4', '9', '1', '6', '6', '9', '1', '1', '7', '6', '5', '8', '0', '7', '6', '6', '1', '5', '9', '8', '1', '5', '9', '5', '2', '4', '2', '8', '8', '3', '9', '2', '2', '3', '2', '7', '8', '5', '3', '0', '8', '8', '6', '2', '3', '9', '8', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '9', '0', '0', '0', '0', '7', '6', '7', '6', '6', '8', '7', '6', '7', '8', '6', '5', '8', '1', '1', '7', '8', '6', '0', '8', '0', '2', '6', '4', '3', '5', '1', '1', '3', '8', '6', '5', '1', '4', '1', '3', '9', '4', '6', '0', '5', '4', '9', '7', '0', '5', '4', '9', '8', '4', '1', '3', '1', '4', '2', '0', '9', '3', '6', '1', '8', '9', '4', '2', '7', '1', '4', '2', '3', '3', '4', '5', '7', '3', '9', '9', '8', '8', '5', '9', '5', '4', '0', '7', '9', '5', '1', '8', '4', '4', '5', '9', '7', '6', '3', '8', '9', '1', '3', '5', '7', '9', '1', '4', '2', '5', '7', '8', '7', '8', '5', '3', '1', '8', '3', '4', '2', '0', '7', '3', '4', '8', '3', '9', '1', '3', '4', '2', '6', '1'])
noncomputable def fragment0139954Acc00800 : List (String × SourceJson) := (fragment0139954Field007Key00, fragment0139954Field007Value00) :: fragment0139954Acc00700
noncomputable def fragment0139954Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '8', '7', '7', '7', '8', '6', '5', '5', '4', '6', '1', '5', '3', '5', '0', '8', '2', '8', '3', '5', '7', '1', '7', '8', '6', '2', '1', '0', '3', '7', '1', '3', '9', '9', '2', '7', '0', '5', '6', '1', '8', '8', '3', '3', '4', '2', '8', '5', '3', '4', '9', '1', '6', '6', '9', '1', '1', '7', '6', '5', '8', '0', '7', '6', '6', '1', '5', '9', '8', '1', '5', '9', '5', '2', '4', '2', '8', '8', '3', '9', '2', '2', '3', '2', '7', '8', '5', '3', '0', '8', '8', '6', '2', '3', '9', '8', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '9', '0', '0', '0', '0', '7', '6', '7', '6', '6', '8', '7', '6', '7', '8', '6', '5', '8', '1', '1', '7', '8', '6', '0', '8', '0', '2', '6', '4', '3', '5', '1', '1', '3', '8', '6', '5', '1', '4', '1', '3', '9', '4', '6', '0', '5', '4', '9', '7', '0', '5', '4', '9', '8', '4', '1', '3', '1', '4', '2', '0', '9', '3', '6', '1', '8', '9', '4', '2', '7', '1', '4', '2', '3', '3', '4', '5', '7', '3', '9', '9', '8', '8', '5', '9', '5', '4', '0', '7', '9', '5', '1', '8', '4', '4', '5', '9', '7', '6', '3', '8', '9', '1', '3', '5', '7', '9', '1', '4', '2', '5', '7', '8', '7', '8', '5', '3', '1', '8', '3', '4', '2', '0', '7', '3', '4', '8', '3', '9', '1', '3', '4', '2', '6', '1', '"', ',']

theorem object_fragment0139954_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0139954Field007Chars00 ++ tail)) fragment0139954Acc00700 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0139954Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0139954_object_field_007"
  err.flush

noncomputable def fragment0139954Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0139954Field008Value00 : SourceJson := .str (String.ofList ['2', '2', '1', '2', '2', '7', '9', '5', '4', '5', '8', '8', '8', '0', '9', '2'])
noncomputable def fragment0139954Acc00900 : List (String × SourceJson) := (fragment0139954Field008Key00, fragment0139954Field008Value00) :: fragment0139954Acc00800
noncomputable def fragment0139954Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '1', '2', '2', '7', '9', '5', '4', '5', '8', '8', '8', '0', '9', '2', '"', ',']

theorem object_fragment0139954_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0139954Field008Chars00 ++ tail)) fragment0139954Acc00800 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0139954Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0139954_object_field_008"
  err.flush

noncomputable def fragment0139954Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0139954Field009Value00 : SourceJson := .str (String.ofList ['7', '8', '7', '7', '6', '7', '4', '3', '2', '3', '0', '8', '3', '0', '7', '8'])
noncomputable def fragment0139954Acc01000 : List (String × SourceJson) := (fragment0139954Field009Key00, fragment0139954Field009Value00) :: fragment0139954Acc00900
noncomputable def fragment0139954Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '8', '7', '7', '6', '7', '4', '3', '2', '3', '0', '8', '3', '0', '7', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0139954_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0139954Field009Chars00 ++ tail)) fragment0139954Acc00900 =
      .ok (.obj (fragment0139954Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0139954_object_field_009"
  err.flush

noncomputable def fragment0139954Chars : List Char := '{' :: (fragment0139954Field000Chars00 ++ fragment0139954Field001Chars00 ++ fragment0139954Field002Chars00 ++ fragment0139954Field003Chars00 ++ fragment0139954Field004Chars00 ++ fragment0139954Field005Chars00 ++ fragment0139954Field006Chars00 ++ fragment0139954Field007Chars00 ++ fragment0139954Field008Chars00 ++ fragment0139954Field009Chars00)
noncomputable def fragment0139954Value : SourceJson := .obj (fragment0139954Acc01000.reverse)

theorem value_fragment0139954 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 271) (fragment0139954Chars ++ tail) =
      .ok (fragment0139954Value, tail) := by
  have hinput : fragment0139954Chars ++ tail = '{' :: (fragment0139954Field000Chars00 ++ (fragment0139954Field001Chars00 ++ (fragment0139954Field002Chars00 ++ (fragment0139954Field003Chars00 ++ (fragment0139954Field004Chars00 ++ (fragment0139954Field005Chars00 ++ (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0139954Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 271) (fragment0139954Chars ++ tail) =
        SourceJson.value (fuel + 271) ('{' :: (fragment0139954Field000Chars00 ++ (fragment0139954Field001Chars00 ++ (fragment0139954Field002Chars00 ++ (fragment0139954Field003Chars00 ++ (fragment0139954Field004Chars00 ++ (fragment0139954Field005Chars00 ++ (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 271)) hinput
    _ = SourceJson.object (fuel + 270) (SourceJson.white (fragment0139954Field000Chars00 ++ (fragment0139954Field001Chars00 ++ (fragment0139954Field002Chars00 ++ (fragment0139954Field003Chars00 ++ (fragment0139954Field004Chars00 ++ (fragment0139954Field005Chars00 ++ (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail)))))))))))) fragment0139954Acc00000 := by rfl
    _ = SourceJson.object (fuel + 269) (SourceJson.white (fragment0139954Field001Chars00 ++ (fragment0139954Field002Chars00 ++ (fragment0139954Field003Chars00 ++ (fragment0139954Field004Chars00 ++ (fragment0139954Field005Chars00 ++ (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail))))))))))) fragment0139954Acc00100 := object_fragment0139954_field_000 fuel (fragment0139954Field001Chars00 ++ (fragment0139954Field002Chars00 ++ (fragment0139954Field003Chars00 ++ (fragment0139954Field004Chars00 ++ (fragment0139954Field005Chars00 ++ (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 268) (SourceJson.white (fragment0139954Field002Chars00 ++ (fragment0139954Field003Chars00 ++ (fragment0139954Field004Chars00 ++ (fragment0139954Field005Chars00 ++ (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail)))))))))) fragment0139954Acc00200 := object_fragment0139954_field_001 fuel (fragment0139954Field002Chars00 ++ (fragment0139954Field003Chars00 ++ (fragment0139954Field004Chars00 ++ (fragment0139954Field005Chars00 ++ (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 267) (SourceJson.white (fragment0139954Field003Chars00 ++ (fragment0139954Field004Chars00 ++ (fragment0139954Field005Chars00 ++ (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail))))))))) fragment0139954Acc00300 := object_fragment0139954_field_002 fuel (fragment0139954Field003Chars00 ++ (fragment0139954Field004Chars00 ++ (fragment0139954Field005Chars00 ++ (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 266) (SourceJson.white (fragment0139954Field004Chars00 ++ (fragment0139954Field005Chars00 ++ (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail)))))))) fragment0139954Acc00400 := object_fragment0139954_field_003 fuel (fragment0139954Field004Chars00 ++ (fragment0139954Field005Chars00 ++ (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 265) (SourceJson.white (fragment0139954Field005Chars00 ++ (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail))))))) fragment0139954Acc00500 := object_fragment0139954_field_004 fuel (fragment0139954Field005Chars00 ++ (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail)))))) fragment0139954Acc00600 := object_fragment0139954_field_005 fuel (fragment0139954Field006Chars00 ++ (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail))))) fragment0139954Acc00700 := object_fragment0139954_field_006 fuel (fragment0139954Field007Chars00 ++ (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail)))) fragment0139954Acc00800 := object_fragment0139954_field_007 fuel (fragment0139954Field008Chars00 ++ (fragment0139954Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0139954Field009Chars00 ++ (tail))) fragment0139954Acc00900 := object_fragment0139954_field_008 fuel (fragment0139954Field009Chars00 ++ (tail))
    _ = .ok (fragment0139954Value, tail) := object_fragment0139954_field_009 fuel (tail)

noncomputable def fragment0141618Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0141618Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0141618Field000Value00 : SourceJson := .number (String.ofList ['2', '2'])
noncomputable def fragment0141618Acc00100 : List (String × SourceJson) := (fragment0141618Field000Key00, fragment0141618Field000Value00) :: fragment0141618Acc00000
noncomputable def fragment0141618Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '2', ',']

theorem object_fragment0141618_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 278) (SourceJson.white (fragment0141618Field000Chars00 ++ tail)) fragment0141618Acc00000 =
      SourceJson.object (fuel + 277) (SourceJson.white tail) fragment0141618Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0141618_object_field_000"
  err.flush

noncomputable def fragment0141618Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0141618Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0141618Acc00200 : List (String × SourceJson) := (fragment0141618Field001Key00, fragment0141618Field001Value00) :: fragment0141618Acc00100
noncomputable def fragment0141618Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0141618_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 277) (SourceJson.white (fragment0141618Field001Chars00 ++ tail)) fragment0141618Acc00100 =
      SourceJson.object (fuel + 276) (SourceJson.white tail) fragment0141618Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0141618_object_field_001"
  err.flush

noncomputable def fragment0141618Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0141618Field002Value00 : SourceJson := .str (String.ofList ['1', '1', '7', '7', '9', '8', '1', '7', '0', '4', '1', '5', '5', '2', '7', '2', '9', '3', '3', '3', '2', '7', '8', '4', '0', '7', '2', '2', '3', '4', '9', '4', '3', '/', '1', '7', '6', '6', '3', '4', '0', '3', '6', '4', '1', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0141618Acc00300 : List (String × SourceJson) := (fragment0141618Field002Key00, fragment0141618Field002Value00) :: fragment0141618Acc00200
noncomputable def fragment0141618Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '1', '7', '7', '9', '8', '1', '7', '0', '4', '1', '5', '5', '2', '7', '2', '9', '3', '3', '3', '2', '7', '8', '4', '0', '7', '2', '2', '3', '4', '9', '4', '3', '/', '1', '7', '6', '6', '3', '4', '0', '3', '6', '4', '1', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0141618_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 276) (SourceJson.white (fragment0141618Field002Chars00 ++ tail)) fragment0141618Acc00200 =
      SourceJson.object (fuel + 275) (SourceJson.white tail) fragment0141618Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0141618_object_field_002"
  err.flush

noncomputable def fragment0141618Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0141618Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0141618Acc00400 : List (String × SourceJson) := (fragment0141618Field003Key00, fragment0141618Field003Value00) :: fragment0141618Acc00300
noncomputable def fragment0141618Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0141618_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 275) (SourceJson.white (fragment0141618Field003Chars00 ++ tail)) fragment0141618Acc00300 =
      SourceJson.object (fuel + 274) (SourceJson.white tail) fragment0141618Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0141618_object_field_003"
  err.flush

noncomputable def fragment0141618Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0141618Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0141618Acc00500 : List (String × SourceJson) := (fragment0141618Field004Key00, fragment0141618Field004Value00) :: fragment0141618Acc00400
noncomputable def fragment0141618Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0141618_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 274) (SourceJson.white (fragment0141618Field004Chars00 ++ tail)) fragment0141618Acc00400 =
      SourceJson.object (fuel + 273) (SourceJson.white tail) fragment0141618Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0141618_object_field_004"
  err.flush

noncomputable def fragment0141618Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0141618Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '8', '0', '2', '0', '7', '6', '6', '8', '7', '1', '9', '3', '4', '1', '/', '6', '4', '6', '1', '2', '3', '5', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '6', '6', '4', '8', '5', '4', '8', '7', '2', '2', '3', '1', '7', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '6', '2', '4', '3', '9', '4', '2', '2', '7', '9', '9', '1', '/', '6', '4', '6', '1', '2', '3', '5', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '7', '1', '2', '7', '0', '0', '1', '1', '8', '3', '0', '9', '1', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '4', '2', '9', '9', '0', '5', '0', '3', '2', '7', '7', '7', '9', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '3', '1', '6', '2', '4', '2', '6', '3', '0', '5', '5', '7', '/', '3', '2', '3', '0', '6', '1', '7', '9', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '3', '6', '9', '2', '3', '5', '7', '2', '3', '3', '9', '9', '1', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '3', '8', '0', '4', '9', '6', '9', '6', '1', '7', '6', '1', '/', '1', '4', '3', '5', '8', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '2', '6', '1', '8', '5', '7', '8', '4', '6', '0', '6', '5', '3', '/', '4', '3', '0', '7', '4', '9', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '2', '6', '1', '7', '7', '1', '6', '9', '6', '2', '5', '3', '3', '/', '4', '3', '0', '7', '4', '9', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0141618Acc00600 : List (String × SourceJson) := (fragment0141618Field005Key00, fragment0141618Field005Value00) :: fragment0141618Acc00500
noncomputable def fragment0141618Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '0', '2', '0', '7', '6', '6', '8', '7', '1', '9', '3', '4', '1', '/', '6', '4', '6', '1', '2', '3', '5', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '6', '6', '4', '8', '5', '4', '8', '7', '2', '2', '3', '1', '7', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '6', '2', '4', '3', '9', '4', '2', '2', '7', '9', '9', '1', '/', '6', '4', '6', '1', '2', '3', '5', '9', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '7', '1', '2', '7', '0', '0', '1', '1', '8', '3', '0', '9', '1', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '4', '2', '9', '9', '0', '5', '0', '3', '2', '7', '7', '7', '9', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '3', '1', '6', '2', '4', '2', '6', '3', '0', '5', '5', '7', '/', '3', '2', '3', '0', '6', '1', '7', '9', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '3', '6', '9', '2', '3', '5', '7', '2', '3', '3', '9', '9', '1', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '3', '8', '0', '4', '9', '6', '9', '6', '1', '7', '6', '1', '/', '1', '4', '3', '5', '8', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '6', '1', '8', '5', '7', '8', '4', '6', '0', '6', '5', '3', '/', '4', '3', '0', '7', '4', '9', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '6', '1', '7', '7', '1', '6', '9', '6', '2', '5', '3', '3', '/', '4', '3', '0', '7', '4', '9', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0141618_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 273) (SourceJson.white (fragment0141618Field005Chars00 ++ tail)) fragment0141618Acc00500 =
      SourceJson.object (fuel + 272) (SourceJson.white tail) fragment0141618Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0141618_object_field_005"
  err.flush

noncomputable def fragment0141618Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0141618Field006Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '9', '4', '0', '2', '5', '4', '6', '8', '4', '5', '2', '0', '2', '7', '8', '9', '9', '3', '7', '8', '2', '1', '4', '9', '1', '6', '8', '1', '9', '7', '8', '7', '0', '8', '8', '8', '8', '6', '1', '1', '6', '1', '9', '2', '0', '0', '0', '0', '0', '0', '/', '3', '1', '0', '8', '5', '7', '4', '1', '9', '9', '4', '1', '3', '3', '1', '4', '8', '5', '4', '6', '1', '2', '3', '3', '4', '1', '9', '8', '5', '9', '9', '9', '9', '7', '6', '0', '5', '4', '8', '0', '1', '9', '6', '5', '9', '4', '9', '7', '0', '3', '9', '2', '3', '8', '8', '6', '8', '7', '4', '1', '2', '0', '9', '6', '2', '4', '0', '8', '5', '9'])
noncomputable def fragment0141618Acc00700 : List (String × SourceJson) := (fragment0141618Field006Key00, fragment0141618Field006Value00) :: fragment0141618Acc00600
noncomputable def fragment0141618Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '8', '9', '4', '0', '2', '5', '4', '6', '8', '4', '5', '2', '0', '2', '7', '8', '9', '9', '3', '7', '8', '2', '1', '4', '9', '1', '6', '8', '1', '9', '7', '8', '7', '0', '8', '8', '8', '8', '6', '1', '1', '6', '1', '9', '2', '0', '0', '0', '0', '0', '0', '/', '3', '1', '0', '8', '5', '7', '4', '1', '9', '9', '4', '1', '3', '3', '1', '4', '8', '5', '4', '6', '1', '2', '3', '3', '4', '1', '9', '8', '5', '9', '9', '9', '9', '7', '6', '0', '5', '4', '8', '0', '1', '9', '6', '5', '9', '4', '9', '7', '0', '3', '9', '2', '3', '8', '8', '6', '8', '7', '4', '1', '2', '0', '9', '6', '2', '4', '0', '8', '5', '9', '"', ',']

theorem object_fragment0141618_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 272) (SourceJson.white (fragment0141618Field006Chars00 ++ tail)) fragment0141618Acc00600 =
      SourceJson.object (fuel + 271) (SourceJson.white tail) fragment0141618Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0141618_object_field_006"
  err.flush

noncomputable def fragment0141618Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0141618Field007Value00 : SourceJson := .str (String.ofList ['5', '9', '1', '9', '4', '7', '8', '5', '6', '4', '6', '0', '5', '9', '5', '8', '2', '7', '3', '3', '5', '6', '3', '4', '1', '8', '3', '6', '4', '2', '6', '2', '2', '3', '2', '2', '4', '1', '3', '5', '3', '4', '0', '8', '2', '7', '6', '2', '7', '2', '9', '7', '5', '5', '4', '1', '5', '8', '0', '5', '0', '3', '2', '5', '9', '7', '0', '7', '4', '2', '8', '5', '3', '1', '6', '0', '1', '7', '1', '7', '4', '0', '7', '1', '2', '7', '4', '7', '3', '3', '5', '3', '9', '2', '7', '0', '9', '2', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '7', '2', '3', '9', '7', '0', '8', '4', '3', '9', '0', '3', '9', '5', '6', '6', '1', '7', '0', '0', '5', '7', '1', '7', '4', '2', '7', '6', '0', '3', '1', '9', '3', '1', '9', '5', '8', '2', '7', '1', '5', '0', '9', '1', '5', '0', '1', '4', '8', '6', '7', '7', '7', '3', '4', '6', '4', '5', '2', '2', '2', '4', '0', '5', '7', '0', '7', '5', '6', '4', '0', '9', '9', '6', '6', '9', '6', '8', '1', '6', '6', '8', '2', '0', '8', '8', '8', '5', '9', '5', '5', '8', '6', '0', '0', '2', '2', '4', '3', '7', '3', '8', '5', '2', '1', '6', '2', '3', '5', '7', '4', '6', '9', '5', '9', '3', '0', '4', '2', '4', '4', '3', '9', '3', '9', '8', '9', '3', '8', '3', '9', '8', '9', '1', '0', '3', '0', '8', '5', '4', '9'])
noncomputable def fragment0141618Acc00800 : List (String × SourceJson) := (fragment0141618Field007Key00, fragment0141618Field007Value00) :: fragment0141618Acc00700
noncomputable def fragment0141618Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '9', '1', '9', '4', '7', '8', '5', '6', '4', '6', '0', '5', '9', '5', '8', '2', '7', '3', '3', '5', '6', '3', '4', '1', '8', '3', '6', '4', '2', '6', '2', '2', '3', '2', '2', '4', '1', '3', '5', '3', '4', '0', '8', '2', '7', '6', '2', '7', '2', '9', '7', '5', '5', '4', '1', '5', '8', '0', '5', '0', '3', '2', '5', '9', '7', '0', '7', '4', '2', '8', '5', '3', '1', '6', '0', '1', '7', '1', '7', '4', '0', '7', '1', '2', '7', '4', '7', '3', '3', '5', '3', '9', '2', '7', '0', '9', '2', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '7', '2', '3', '9', '7', '0', '8', '4', '3', '9', '0', '3', '9', '5', '6', '6', '1', '7', '0', '0', '5', '7', '1', '7', '4', '2', '7', '6', '0', '3', '1', '9', '3', '1', '9', '5', '8', '2', '7', '1', '5', '0', '9', '1', '5', '0', '1', '4', '8', '6', '7', '7', '7', '3', '4', '6', '4', '5', '2', '2', '2', '4', '0', '5', '7', '0', '7', '5', '6', '4', '0', '9', '9', '6', '6', '9', '6', '8', '1', '6', '6', '8', '2', '0', '8', '8', '8', '5', '9', '5', '5', '8', '6', '0', '0', '2', '2', '4', '3', '7', '3', '8', '5', '2', '1', '6', '2', '3', '5', '7', '4', '6', '9', '5', '9', '3', '0', '4', '2', '4', '4', '3', '9', '3', '9', '8', '9', '3', '8', '3', '9', '8', '9', '1', '0', '3', '0', '8', '5', '4', '9', '"', ',']

theorem object_fragment0141618_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 271) (SourceJson.white (fragment0141618Field007Chars00 ++ tail)) fragment0141618Acc00700 =
      SourceJson.object (fuel + 270) (SourceJson.white tail) fragment0141618Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0141618_object_field_007"
  err.flush

noncomputable def fragment0141618Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0141618Field008Value00 : SourceJson := .str (String.ofList ['2', '7', '7', '6', '5', '5', '7', '8', '8', '4', '3', '5'])
noncomputable def fragment0141618Acc00900 : List (String × SourceJson) := (fragment0141618Field008Key00, fragment0141618Field008Value00) :: fragment0141618Acc00800
noncomputable def fragment0141618Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '7', '6', '5', '5', '7', '8', '8', '4', '3', '5', '"', ',']

theorem object_fragment0141618_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 270) (SourceJson.white (fragment0141618Field008Chars00 ++ tail)) fragment0141618Acc00800 =
      SourceJson.object (fuel + 269) (SourceJson.white tail) fragment0141618Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0141618_object_field_008"
  err.flush

noncomputable def fragment0141618Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0141618Field009Value00 : SourceJson := .str (String.ofList ['8', '1', '9', '3', '4', '2', '7', '6', '4', '8', '4', '9'])
noncomputable def fragment0141618Acc01000 : List (String × SourceJson) := (fragment0141618Field009Key00, fragment0141618Field009Value00) :: fragment0141618Acc00900
noncomputable def fragment0141618Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '1', '9', '3', '4', '2', '7', '6', '4', '8', '4', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0141618_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 269) (SourceJson.white (fragment0141618Field009Chars00 ++ tail)) fragment0141618Acc00900 =
      .ok (.obj (fragment0141618Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0141618_object_field_009"
  err.flush

noncomputable def fragment0141618Chars : List Char := '{' :: (fragment0141618Field000Chars00 ++ fragment0141618Field001Chars00 ++ fragment0141618Field002Chars00 ++ fragment0141618Field003Chars00 ++ fragment0141618Field004Chars00 ++ fragment0141618Field005Chars00 ++ fragment0141618Field006Chars00 ++ fragment0141618Field007Chars00 ++ fragment0141618Field008Chars00 ++ fragment0141618Field009Chars00)
noncomputable def fragment0141618Value : SourceJson := .obj (fragment0141618Acc01000.reverse)

theorem value_fragment0141618 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 279) (fragment0141618Chars ++ tail) =
      .ok (fragment0141618Value, tail) := by
  have hinput : fragment0141618Chars ++ tail = '{' :: (fragment0141618Field000Chars00 ++ (fragment0141618Field001Chars00 ++ (fragment0141618Field002Chars00 ++ (fragment0141618Field003Chars00 ++ (fragment0141618Field004Chars00 ++ (fragment0141618Field005Chars00 ++ (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0141618Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 279) (fragment0141618Chars ++ tail) =
        SourceJson.value (fuel + 279) ('{' :: (fragment0141618Field000Chars00 ++ (fragment0141618Field001Chars00 ++ (fragment0141618Field002Chars00 ++ (fragment0141618Field003Chars00 ++ (fragment0141618Field004Chars00 ++ (fragment0141618Field005Chars00 ++ (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 279)) hinput
    _ = SourceJson.object (fuel + 278) (SourceJson.white (fragment0141618Field000Chars00 ++ (fragment0141618Field001Chars00 ++ (fragment0141618Field002Chars00 ++ (fragment0141618Field003Chars00 ++ (fragment0141618Field004Chars00 ++ (fragment0141618Field005Chars00 ++ (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail)))))))))))) fragment0141618Acc00000 := by rfl
    _ = SourceJson.object (fuel + 277) (SourceJson.white (fragment0141618Field001Chars00 ++ (fragment0141618Field002Chars00 ++ (fragment0141618Field003Chars00 ++ (fragment0141618Field004Chars00 ++ (fragment0141618Field005Chars00 ++ (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail))))))))))) fragment0141618Acc00100 := object_fragment0141618_field_000 fuel (fragment0141618Field001Chars00 ++ (fragment0141618Field002Chars00 ++ (fragment0141618Field003Chars00 ++ (fragment0141618Field004Chars00 ++ (fragment0141618Field005Chars00 ++ (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 276) (SourceJson.white (fragment0141618Field002Chars00 ++ (fragment0141618Field003Chars00 ++ (fragment0141618Field004Chars00 ++ (fragment0141618Field005Chars00 ++ (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail)))))))))) fragment0141618Acc00200 := object_fragment0141618_field_001 fuel (fragment0141618Field002Chars00 ++ (fragment0141618Field003Chars00 ++ (fragment0141618Field004Chars00 ++ (fragment0141618Field005Chars00 ++ (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 275) (SourceJson.white (fragment0141618Field003Chars00 ++ (fragment0141618Field004Chars00 ++ (fragment0141618Field005Chars00 ++ (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail))))))))) fragment0141618Acc00300 := object_fragment0141618_field_002 fuel (fragment0141618Field003Chars00 ++ (fragment0141618Field004Chars00 ++ (fragment0141618Field005Chars00 ++ (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 274) (SourceJson.white (fragment0141618Field004Chars00 ++ (fragment0141618Field005Chars00 ++ (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail)))))))) fragment0141618Acc00400 := object_fragment0141618_field_003 fuel (fragment0141618Field004Chars00 ++ (fragment0141618Field005Chars00 ++ (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 273) (SourceJson.white (fragment0141618Field005Chars00 ++ (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail))))))) fragment0141618Acc00500 := object_fragment0141618_field_004 fuel (fragment0141618Field005Chars00 ++ (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 272) (SourceJson.white (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail)))))) fragment0141618Acc00600 := object_fragment0141618_field_005 fuel (fragment0141618Field006Chars00 ++ (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 271) (SourceJson.white (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail))))) fragment0141618Acc00700 := object_fragment0141618_field_006 fuel (fragment0141618Field007Chars00 ++ (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 270) (SourceJson.white (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail)))) fragment0141618Acc00800 := object_fragment0141618_field_007 fuel (fragment0141618Field008Chars00 ++ (fragment0141618Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 269) (SourceJson.white (fragment0141618Field009Chars00 ++ (tail))) fragment0141618Acc00900 := object_fragment0141618_field_008 fuel (fragment0141618Field009Chars00 ++ (tail))
    _ = .ok (fragment0141618Value, tail) := object_fragment0141618_field_009 fuel (tail)

noncomputable def fragment0143305Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0143305Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0143305Field000Value00 : SourceJson := .number (String.ofList ['2', '3'])
noncomputable def fragment0143305Acc00100 : List (String × SourceJson) := (fragment0143305Field000Key00, fragment0143305Field000Value00) :: fragment0143305Acc00000
noncomputable def fragment0143305Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '3', ',']

theorem object_fragment0143305_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 442) (SourceJson.white (fragment0143305Field000Chars00 ++ tail)) fragment0143305Acc00000 =
      SourceJson.object (fuel + 441) (SourceJson.white tail) fragment0143305Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0143305_object_field_000"
  err.flush

noncomputable def fragment0143305Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0143305Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0143305Acc00200 : List (String × SourceJson) := (fragment0143305Field001Key00, fragment0143305Field001Value00) :: fragment0143305Acc00100
noncomputable def fragment0143305Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0143305_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 441) (SourceJson.white (fragment0143305Field001Chars00 ++ tail)) fragment0143305Acc00100 =
      SourceJson.object (fuel + 440) (SourceJson.white tail) fragment0143305Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0143305_object_field_001"
  err.flush

noncomputable def fragment0143305Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0143305Field002Value00 : SourceJson := .str (String.ofList ['1', '2', '8', '8', '4', '9', '6', '0', '3', '4', '0', '5', '8', '2', '3', '8', '7', '6', '7', '4', '9', '1', '8', '1', '8', '0', '8', '0', '8', '6', '9', '4', '7', '4', '5', '5', '7', '3', '/', '7', '5', '3', '6', '3', '8', '5', '5', '5', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0143305Acc00300 : List (String × SourceJson) := (fragment0143305Field002Key00, fragment0143305Field002Value00) :: fragment0143305Acc00200
noncomputable def fragment0143305Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '2', '8', '8', '4', '9', '6', '0', '3', '4', '0', '5', '8', '2', '3', '8', '7', '6', '7', '4', '9', '1', '8', '1', '8', '0', '8', '0', '8', '6', '9', '4', '7', '4', '5', '5', '7', '3', '/', '7', '5', '3', '6', '3', '8', '5', '5', '5', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0143305_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 440) (SourceJson.white (fragment0143305Field002Chars00 ++ tail)) fragment0143305Acc00200 =
      SourceJson.object (fuel + 439) (SourceJson.white tail) fragment0143305Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0143305_object_field_002"
  err.flush

noncomputable def fragment0143305Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0143305Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '2', '4', '1', '6', '9', '/', '1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0143305Acc00400 : List (String × SourceJson) := (fragment0143305Field003Key00, fragment0143305Field003Value00) :: fragment0143305Acc00300
noncomputable def fragment0143305Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '8', '2', '4', '1', '6', '9', '/', '1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0143305_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 439) (SourceJson.white (fragment0143305Field003Chars00 ++ tail)) fragment0143305Acc00300 =
      SourceJson.object (fuel + 438) (SourceJson.white tail) fragment0143305Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0143305_object_field_003"
  err.flush

noncomputable def fragment0143305Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0143305Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0143305Acc00500 : List (String × SourceJson) := (fragment0143305Field004Key00, fragment0143305Field004Value00) :: fragment0143305Acc00400
noncomputable def fragment0143305Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0143305_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 438) (SourceJson.white (fragment0143305Field004Chars00 ++ tail)) fragment0143305Acc00400 =
      SourceJson.object (fuel + 437) (SourceJson.white tail) fragment0143305Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0143305_object_field_004"
  err.flush

noncomputable def fragment0143305Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0143305Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '0', '0', '8', '9', '3', '8', '3', '5', '8', '3', '9', '9', '5', '0', '5', '7', '9', '6', '5', '1', '1', '7', '3', '/', '2', '2', '3', '8', '0', '0', '0', '2', '9', '8', '5', '7', '4', '9', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '3', '2', '0', '5', '2', '9', '2', '9', '3', '2', '0', '1', '9', '7', '3', '8', '8', '6', '4', '9', '1', '/', '2', '7', '9', '7', '5', '0', '0', '3', '7', '3', '2', '1', '8', '6', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '5', '6', '2', '7', '9', '1', '2', '3', '5', '3', '1', '8', '9', '3', '4', '1', '6', '7', '5', '1', '/', '4', '4', '7', '6', '0', '0', '0', '5', '9', '7', '1', '4', '9', '8', '9', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '7', '7', '1', '0', '7', '0', '2', '0', '5', '4', '0', '3', '2', '1', '6', '3', '6', '4', '2', '1', '1', '/', '5', '5', '9', '5', '0', '0', '0', '7', '4', '6', '4', '3', '7', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '5', '2', '2', '8', '3', '6', '1', '6', '8', '0', '6', '5', '6', '1', '2', '0', '5', '3', '4', '8', '9', '/', '5', '5', '9', '5', '0', '0', '0', '7', '4', '6', '4', '3', '7', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '9', '3', '0', '3', '9', '3', '8', '4', '4', '0', '1', '8', '7', '9', '6', '5', '2', '8', '7', '1', '/', '1', '1', '1', '9', '0', '0', '0', '1', '4', '9', '2', '8', '7', '4', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '5', '0', '2', '5', '3', '9', '9', '0', '9', '6', '4', '1', '0', '5', '9', '9', '5', '3', '6', '1', '7', '/', '1', '1', '1', '9', '0', '0', '0', '1', '4', '9', '2', '8', '7', '4', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '1', '4', '3', '0', '6', '1', '2', '0', '0', '3', '8', '1', '2', '1', '4', '2', '1', '2', '0', '7', '1', '/', '3', '7', '3', '0', '0', '0', '0', '4', '9', '7', '6', '2', '4', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '0', '9', '1', '5', '3', '4', '3', '8', '8', '0', '8', '7', '9', '8', '5', '6', '5', '7', '1', '1', '/', '3', '7', '3', '0', '0', '0', '0', '4', '9', '7', '6', '2', '4', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '7', '8', '1', '2', '2', '8', '4', '8', '6', '2', '1', '2', '2', '4', '0', '8', '9', '8', '5', '9', '/', '9', '3', '2', '5', '0', '0', '1', '2', '4', '4', '0', '6', '2', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0143305Acc00600 : List (String × SourceJson) := (fragment0143305Field005Key00, fragment0143305Field005Value00) :: fragment0143305Acc00500
noncomputable def fragment0143305Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '0', '8', '9', '3', '8', '3', '5', '8', '3', '9', '9', '5', '0', '5', '7', '9', '6', '5', '1', '1', '7', '3', '/', '2', '2', '3', '8', '0', '0', '0', '2', '9', '8', '5', '7', '4', '9', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '3', '2', '0', '5', '2', '9', '2', '9', '3', '2', '0', '1', '9', '7', '3', '8', '8', '6', '4', '9', '1', '/', '2', '7', '9', '7', '5', '0', '0', '3', '7', '3', '2', '1', '8', '6', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '5', '6', '2', '7', '9', '1', '2', '3', '5', '3', '1', '8', '9', '3', '4', '1', '6', '7', '5', '1', '/', '4', '4', '7', '6', '0', '0', '0', '5', '9', '7', '1', '4', '9', '8', '9', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '7', '7', '1', '0', '7', '0', '2', '0', '5', '4', '0', '3', '2', '1', '6', '3', '6', '4', '2', '1', '1', '/', '5', '5', '9', '5', '0', '0', '0', '7', '4', '6', '4', '3', '7', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '5', '2', '2', '8', '3', '6', '1', '6', '8', '0', '6', '5', '6', '1', '2', '0', '5', '3', '4', '8', '9', '/', '5', '5', '9', '5', '0', '0', '0', '7', '4', '6', '4', '3', '7', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '9', '3', '0', '3', '9', '3', '8', '4', '4', '0', '1', '8', '7', '9', '6', '5', '2', '8', '7', '1', '/', '1', '1', '1', '9', '0', '0', '0', '1', '4', '9', '2', '8', '7', '4', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '5', '0', '2', '5', '3', '9', '9', '0', '9', '6', '4', '1', '0', '5', '9', '9', '5', '3', '6', '1', '7', '/', '1', '1', '1', '9', '0', '0', '0', '1', '4', '9', '2', '8', '7', '4', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '4', '3', '0', '6', '1', '2', '0', '0', '3', '8', '1', '2', '1', '4', '2', '1', '2', '0', '7', '1', '/', '3', '7', '3', '0', '0', '0', '0', '4', '9', '7', '6', '2', '4', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '0', '9', '1', '5', '3', '4', '3', '8', '8', '0', '8', '7', '9', '8', '5', '6', '5', '7', '1', '1', '/', '3', '7', '3', '0', '0', '0', '0', '4', '9', '7', '6', '2', '4', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '8', '1', '2', '2', '8', '4', '8', '6', '2', '1', '2', '2', '4', '0', '8', '9', '8', '5', '9', '/', '9', '3', '2', '5', '0', '0', '1', '2', '4', '4', '0', '6', '2', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0143305_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 437) (SourceJson.white (fragment0143305Field005Chars00 ++ tail)) fragment0143305Acc00500 =
      SourceJson.object (fuel + 436) (SourceJson.white tail) fragment0143305Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0143305_object_field_005"
  err.flush

noncomputable def fragment0143305Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0143305Field006Value00 : SourceJson := .str (String.ofList ['4', '0', '2', '9', '0', '4', '8', '6', '0', '0', '1', '6', '4', '4', '3', '3', '9', '7', '0', '5', '8', '6', '1', '2', '9', '7', '4', '2', '8', '6', '9', '1', '3', '6', '3', '2', '2', '1', '2', '7', '4', '4', '9', '5', '3', '6', '9', '5', '7', '8', '0', '0', '0', '0', '0', '0', '/', '2', '2', '5', '0', '4', '8', '6', '0', '1', '6', '5', '2', '7', '6', '1', '5', '4', '9', '5', '2', '3', '3', '7', '5', '9', '7', '6', '7', '0', '2', '9', '2', '3', '2', '1', '2', '9', '5', '6', '6', '1', '7', '8', '1', '6', '8', '0', '5', '0', '9', '0', '6', '2', '3', '2', '9', '8', '0', '0', '3', '3', '1', '1', '9', '4', '9', '0', '7', '2', '9'])
noncomputable def fragment0143305Acc00700 : List (String × SourceJson) := (fragment0143305Field006Key00, fragment0143305Field006Value00) :: fragment0143305Acc00600
noncomputable def fragment0143305Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '0', '2', '9', '0', '4', '8', '6', '0', '0', '1', '6', '4', '4', '3', '3', '9', '7', '0', '5', '8', '6', '1', '2', '9', '7', '4', '2', '8', '6', '9', '1', '3', '6', '3', '2', '2', '1', '2', '7', '4', '4', '9', '5', '3', '6', '9', '5', '7', '8', '0', '0', '0', '0', '0', '0', '/', '2', '2', '5', '0', '4', '8', '6', '0', '1', '6', '5', '2', '7', '6', '1', '5', '4', '9', '5', '2', '3', '3', '7', '5', '9', '7', '6', '7', '0', '2', '9', '2', '3', '2', '1', '2', '9', '5', '6', '6', '1', '7', '8', '1', '6', '8', '0', '5', '0', '9', '0', '6', '2', '3', '2', '9', '8', '0', '0', '3', '3', '1', '1', '9', '4', '9', '0', '7', '2', '9', '"', ',']

theorem object_fragment0143305_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 436) (SourceJson.white (fragment0143305Field006Chars00 ++ tail)) fragment0143305Acc00600 =
      SourceJson.object (fuel + 435) (SourceJson.white tail) fragment0143305Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0143305_object_field_006"
  err.flush

noncomputable def fragment0143305Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0143305Field007Value00 : SourceJson := .str (String.ofList ['4', '8', '9', '6', '9', '7', '7', '8', '6', '9', '3', '7', '9', '8', '7', '2', '0', '1', '4', '8', '6', '4', '6', '1', '6', '4', '5', '9', '0', '8', '9', '1', '7', '2', '1', '3', '4', '9', '6', '9', '5', '4', '5', '3', '6', '1', '2', '3', '2', '6', '0', '3', '0', '5', '8', '4', '2', '7', '5', '9', '5', '1', '0', '0', '7', '4', '0', '8', '8', '7', '1', '1', '0', '6', '8', '1', '9', '3', '1', '1', '2', '2', '0', '5', '0', '0', '5', '3', '3', '7', '2', '4', '0', '4', '4', '4', '7', '3', '5', '0', '0', '0', '8', '3', '8', '4', '7', '0', '0', '7', '5', '8', '3', '3', '1', '2', '9', '1', '6', '7', '1', '2', '6', '2', '8', '0', '4', '0', '9', '5', '6', '7', '9', '8', '2', '1', '3', '4', '9', '8', '1', '4', '6', '5', '1', '3', '8', '9', '9', '1', '3', '8', '5', '5', '4', '0', '7', '5', '1', '6', '4', '9', '8', '1', '3', '8', '0', '5', '2', '8', '1', '5', '4', '4', '6', '1', '5', '5', '6', '9', '1', '2', '9', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '9', '1', '6', '6', '3', '1', '8', '4', '5', '4', '4', '3', '9', '0', '2', '7', '7', '3', '0', '1', '9', '8', '6', '4', '0', '1', '3', '9', '1', '9', '0', '5', '5', '2', '9', '7', '3', '6', '9', '8', '9', '7', '7', '1', '3', '5', '0', '7', '8', '9', '2', '3', '6', '7', '7', '1', '4', '8', '9', '9', '7', '1', '9', '9', '3', '3', '8', '2', '1', '1', '7', '1', '0', '4', '8', '6', '0', '7', '9', '0', '4', '0', '5', '2', '5', '0', '9', '6', '7', '4', '2', '2', '2', '6', '2', '3', '0', '5', '3', '5', '0', '8', '0', '6', '3', '7', '7', '4', '9', '2', '4', '5', '2', '9', '4', '6', '6', '0', '7', '1', '2', '5', '9', '3', '8', '3', '2', '8', '4', '4', '1', '8', '0', '5', '9', '3', '4', '3', '8', '0', '3', '5', '8', '8', '1', '2', '1', '7', '7', '5', '9', '7', '9', '9', '6', '4', '4', '1', '1', '6', '8', '4', '6', '9', '9', '9', '8', '0', '2', '1', '3', '0', '5', '0', '8', '0', '4', '7', '7', '7', '1', '1', '0', '3', '9', '2', '0', '6', '8', '8', '8', '8', '1', '4', '8', '5', '6', '5', '9', '8', '2', '7', '2', '2', '7', '9', '7', '9', '5', '6', '7', '2', '4', '1', '8', '3', '6', '2', '7', '8', '1'])
noncomputable def fragment0143305Acc00800 : List (String × SourceJson) := (fragment0143305Field007Key00, fragment0143305Field007Value00) :: fragment0143305Acc00700
noncomputable def fragment0143305Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '8', '9', '6', '9', '7', '7', '8', '6', '9', '3', '7', '9', '8', '7', '2', '0', '1', '4', '8', '6', '4', '6', '1', '6', '4', '5', '9', '0', '8', '9', '1', '7', '2', '1', '3', '4', '9', '6', '9', '5', '4', '5', '3', '6', '1', '2', '3', '2', '6', '0', '3', '0', '5', '8', '4', '2', '7', '5', '9', '5', '1', '0', '0', '7', '4', '0', '8', '8', '7', '1', '1', '0', '6', '8', '1', '9', '3', '1', '1', '2', '2', '0', '5', '0', '0', '5', '3', '3', '7', '2', '4', '0', '4', '4', '4', '7', '3', '5', '0', '0', '0', '8', '3', '8', '4', '7', '0', '0', '7', '5', '8', '3', '3', '1', '2', '9', '1', '6', '7', '1', '2', '6', '2', '8', '0', '4', '0', '9', '5', '6', '7', '9', '8', '2', '1', '3', '4', '9', '8', '1', '4', '6', '5', '1', '3', '8', '9', '9', '1', '3', '8', '5', '5', '4', '0', '7', '5', '1', '6', '4', '9', '8', '1', '3', '8', '0', '5', '2', '8', '1', '5', '4', '4', '6', '1', '5', '5', '6', '9', '1', '2', '9', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '9', '1', '6', '6', '3', '1', '8', '4', '5', '4', '4', '3', '9', '0', '2', '7', '7', '3', '0', '1', '9', '8', '6', '4', '0', '1', '3', '9', '1', '9', '0', '5', '5', '2', '9', '7', '3', '6', '9', '8', '9', '7', '7', '1', '3', '5', '0', '7', '8', '9', '2', '3', '6', '7', '7', '1', '4', '8', '9', '9', '7', '1', '9', '9', '3', '3', '8', '2', '1', '1', '7', '1', '0', '4', '8', '6', '0', '7', '9', '0', '4', '0', '5', '2', '5', '0', '9', '6', '7', '4', '2', '2', '2', '6', '2', '3', '0', '5', '3', '5', '0', '8', '0', '6', '3', '7', '7', '4', '9', '2', '4', '5', '2', '9', '4', '6', '6', '0', '7', '1', '2', '5', '9', '3', '8', '3', '2', '8', '4', '4', '1', '8', '0', '5', '9', '3', '4', '3', '8', '0', '3', '5', '8', '8', '1', '2', '1', '7', '7', '5', '9', '7', '9', '9', '6', '4', '4', '1', '1', '6', '8', '4', '6', '9', '9', '9', '8', '0', '2', '1', '3', '0', '5', '0', '8', '0', '4', '7', '7', '7', '1', '1', '0', '3', '9', '2', '0', '6', '8', '8', '8', '8', '1', '4', '8', '5', '6', '5', '9', '8', '2', '7', '2', '2', '7', '9', '7', '9', '5', '6', '7', '2', '4', '1', '8', '3', '6', '2', '7', '8', '1', '"', ',']

theorem object_fragment0143305_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 435) (SourceJson.white (fragment0143305Field007Chars00 ++ tail)) fragment0143305Acc00700 =
      SourceJson.object (fuel + 434) (SourceJson.white tail) fragment0143305Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0143305_object_field_007"
  err.flush

noncomputable def fragment0143305Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0143305Field008Value00 : SourceJson := .str (String.ofList ['1', '4', '1', '8', '4', '2', '3', '0', '2', '0', '3', '0', '4', '8', '6', '7'])
noncomputable def fragment0143305Acc00900 : List (String × SourceJson) := (fragment0143305Field008Key00, fragment0143305Field008Value00) :: fragment0143305Acc00800
noncomputable def fragment0143305Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '1', '8', '4', '2', '3', '0', '2', '0', '3', '0', '4', '8', '6', '7', '"', ',']

theorem object_fragment0143305_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 434) (SourceJson.white (fragment0143305Field008Chars00 ++ tail)) fragment0143305Acc00800 =
      SourceJson.object (fuel + 433) (SourceJson.white tail) fragment0143305Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0143305_object_field_008"
  err.flush

noncomputable def fragment0143305Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0143305Field009Value00 : SourceJson := .str (String.ofList ['4', '3', '5', '1', '1', '7', '8', '3', '9', '5', '4', '8', '6', '0', '5', '2'])
noncomputable def fragment0143305Acc01000 : List (String × SourceJson) := (fragment0143305Field009Key00, fragment0143305Field009Value00) :: fragment0143305Acc00900
noncomputable def fragment0143305Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '3', '5', '1', '1', '7', '8', '3', '9', '5', '4', '8', '6', '0', '5', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0143305_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 433) (SourceJson.white (fragment0143305Field009Chars00 ++ tail)) fragment0143305Acc00900 =
      .ok (.obj (fragment0143305Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0143305_object_field_009"
  err.flush

noncomputable def fragment0143305Chars : List Char := '{' :: (fragment0143305Field000Chars00 ++ fragment0143305Field001Chars00 ++ fragment0143305Field002Chars00 ++ fragment0143305Field003Chars00 ++ fragment0143305Field004Chars00 ++ fragment0143305Field005Chars00 ++ fragment0143305Field006Chars00 ++ fragment0143305Field007Chars00 ++ fragment0143305Field008Chars00 ++ fragment0143305Field009Chars00)
noncomputable def fragment0143305Value : SourceJson := .obj (fragment0143305Acc01000.reverse)

theorem value_fragment0143305 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 443) (fragment0143305Chars ++ tail) =
      .ok (fragment0143305Value, tail) := by
  have hinput : fragment0143305Chars ++ tail = '{' :: (fragment0143305Field000Chars00 ++ (fragment0143305Field001Chars00 ++ (fragment0143305Field002Chars00 ++ (fragment0143305Field003Chars00 ++ (fragment0143305Field004Chars00 ++ (fragment0143305Field005Chars00 ++ (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0143305Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 443) (fragment0143305Chars ++ tail) =
        SourceJson.value (fuel + 443) ('{' :: (fragment0143305Field000Chars00 ++ (fragment0143305Field001Chars00 ++ (fragment0143305Field002Chars00 ++ (fragment0143305Field003Chars00 ++ (fragment0143305Field004Chars00 ++ (fragment0143305Field005Chars00 ++ (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 443)) hinput
    _ = SourceJson.object (fuel + 442) (SourceJson.white (fragment0143305Field000Chars00 ++ (fragment0143305Field001Chars00 ++ (fragment0143305Field002Chars00 ++ (fragment0143305Field003Chars00 ++ (fragment0143305Field004Chars00 ++ (fragment0143305Field005Chars00 ++ (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail)))))))))))) fragment0143305Acc00000 := by rfl
    _ = SourceJson.object (fuel + 441) (SourceJson.white (fragment0143305Field001Chars00 ++ (fragment0143305Field002Chars00 ++ (fragment0143305Field003Chars00 ++ (fragment0143305Field004Chars00 ++ (fragment0143305Field005Chars00 ++ (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail))))))))))) fragment0143305Acc00100 := object_fragment0143305_field_000 fuel (fragment0143305Field001Chars00 ++ (fragment0143305Field002Chars00 ++ (fragment0143305Field003Chars00 ++ (fragment0143305Field004Chars00 ++ (fragment0143305Field005Chars00 ++ (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 440) (SourceJson.white (fragment0143305Field002Chars00 ++ (fragment0143305Field003Chars00 ++ (fragment0143305Field004Chars00 ++ (fragment0143305Field005Chars00 ++ (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail)))))))))) fragment0143305Acc00200 := object_fragment0143305_field_001 fuel (fragment0143305Field002Chars00 ++ (fragment0143305Field003Chars00 ++ (fragment0143305Field004Chars00 ++ (fragment0143305Field005Chars00 ++ (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 439) (SourceJson.white (fragment0143305Field003Chars00 ++ (fragment0143305Field004Chars00 ++ (fragment0143305Field005Chars00 ++ (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail))))))))) fragment0143305Acc00300 := object_fragment0143305_field_002 fuel (fragment0143305Field003Chars00 ++ (fragment0143305Field004Chars00 ++ (fragment0143305Field005Chars00 ++ (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 438) (SourceJson.white (fragment0143305Field004Chars00 ++ (fragment0143305Field005Chars00 ++ (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail)))))))) fragment0143305Acc00400 := object_fragment0143305_field_003 fuel (fragment0143305Field004Chars00 ++ (fragment0143305Field005Chars00 ++ (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 437) (SourceJson.white (fragment0143305Field005Chars00 ++ (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail))))))) fragment0143305Acc00500 := object_fragment0143305_field_004 fuel (fragment0143305Field005Chars00 ++ (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 436) (SourceJson.white (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail)))))) fragment0143305Acc00600 := object_fragment0143305_field_005 fuel (fragment0143305Field006Chars00 ++ (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 435) (SourceJson.white (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail))))) fragment0143305Acc00700 := object_fragment0143305_field_006 fuel (fragment0143305Field007Chars00 ++ (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 434) (SourceJson.white (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail)))) fragment0143305Acc00800 := object_fragment0143305_field_007 fuel (fragment0143305Field008Chars00 ++ (fragment0143305Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 433) (SourceJson.white (fragment0143305Field009Chars00 ++ (tail))) fragment0143305Acc00900 := object_fragment0143305_field_008 fuel (fragment0143305Field009Chars00 ++ (tail))
    _ = .ok (fragment0143305Value, tail) := object_fragment0143305_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_before_reader"
  err.flush

noncomputable def chunk0016LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0016SuffixChars00 : List Char := [',']
noncomputable def chunk0016Chars00 : List Char := chunk0016LeadChars00 ++ fragment0131392Chars ++ chunk0016SuffixChars00
noncomputable def chunk0016Push00 (acc : List SourceJson) : List SourceJson := fragment0131392Value :: acc

noncomputable def chunk0016AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0016_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 457)
      (SourceJson.white (chunk0016LeadChars00 ++ (fragment0131392Chars ++ rest))) acc =
      (SourceJson.value (fuel + 456) (fragment0131392Chars ++ rest)).bind
        (chunk0016AfterValue00 (fuel + 456) acc) := by rfl

theorem array_chunk0016 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 457) (SourceJson.white (chunk0016Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 456) (SourceJson.white tail) (chunk0016Push00 acc) := by
  have hinput : chunk0016Chars00 ++ tail = chunk0016LeadChars00 ++ (fragment0131392Chars ++ (chunk0016SuffixChars00 ++ tail)) := by
    simp only [chunk0016Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 457) (SourceJson.white (chunk0016Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 457)
          (SourceJson.white (chunk0016LeadChars00 ++ (fragment0131392Chars ++ (chunk0016SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 457) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 456) (fragment0131392Chars ++ (chunk0016SuffixChars00 ++ tail))).bind
        (chunk0016AfterValue00 (fuel + 456) acc) := array_chunk0016_head fuel (chunk0016SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0131392Value, chunk0016SuffixChars00 ++ tail)).bind
        (chunk0016AfterValue00 (fuel + 456) acc) :=
      congrArg (fun result => result.bind (chunk0016AfterValue00 (fuel + 456) acc))
        (value_fragment0131392 (fuel + 185) (chunk0016SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 456) (SourceJson.white tail) (chunk0016Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0017_before_reader"
  err.flush

noncomputable def chunk0017LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0017SuffixChars00 : List Char := [',']
noncomputable def chunk0017Chars00 : List Char := chunk0017LeadChars00 ++ fragment0133064Chars ++ chunk0017SuffixChars00
noncomputable def chunk0017Push00 (acc : List SourceJson) : List SourceJson := fragment0133064Value :: acc

noncomputable def chunk0017AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0017_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 456)
      (SourceJson.white (chunk0017LeadChars00 ++ (fragment0133064Chars ++ rest))) acc =
      (SourceJson.value (fuel + 455) (fragment0133064Chars ++ rest)).bind
        (chunk0017AfterValue00 (fuel + 455) acc) := by rfl

theorem array_chunk0017 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 456) (SourceJson.white (chunk0017Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 455) (SourceJson.white tail) (chunk0017Push00 acc) := by
  have hinput : chunk0017Chars00 ++ tail = chunk0017LeadChars00 ++ (fragment0133064Chars ++ (chunk0017SuffixChars00 ++ tail)) := by
    simp only [chunk0017Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 456) (SourceJson.white (chunk0017Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 456)
          (SourceJson.white (chunk0017LeadChars00 ++ (fragment0133064Chars ++ (chunk0017SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 456) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 455) (fragment0133064Chars ++ (chunk0017SuffixChars00 ++ tail))).bind
        (chunk0017AfterValue00 (fuel + 455) acc) := array_chunk0017_head fuel (chunk0017SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0133064Value, chunk0017SuffixChars00 ++ tail)).bind
        (chunk0017AfterValue00 (fuel + 455) acc) :=
      congrArg (fun result => result.bind (chunk0017AfterValue00 (fuel + 455) acc))
        (value_fragment0133064 (fuel + 188) (chunk0017SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 455) (SourceJson.white tail) (chunk0017Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0017_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_before_reader"
  err.flush

noncomputable def chunk0018LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0018SuffixChars00 : List Char := [',']
noncomputable def chunk0018Chars00 : List Char := chunk0018LeadChars00 ++ fragment0134746Chars ++ chunk0018SuffixChars00
noncomputable def chunk0018Push00 (acc : List SourceJson) : List SourceJson := fragment0134746Value :: acc

noncomputable def chunk0018AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0018_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 455)
      (SourceJson.white (chunk0018LeadChars00 ++ (fragment0134746Chars ++ rest))) acc =
      (SourceJson.value (fuel + 454) (fragment0134746Chars ++ rest)).bind
        (chunk0018AfterValue00 (fuel + 454) acc) := by rfl

theorem array_chunk0018 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 455) (SourceJson.white (chunk0018Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 454) (SourceJson.white tail) (chunk0018Push00 acc) := by
  have hinput : chunk0018Chars00 ++ tail = chunk0018LeadChars00 ++ (fragment0134746Chars ++ (chunk0018SuffixChars00 ++ tail)) := by
    simp only [chunk0018Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 455) (SourceJson.white (chunk0018Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 455)
          (SourceJson.white (chunk0018LeadChars00 ++ (fragment0134746Chars ++ (chunk0018SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 455) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 454) (fragment0134746Chars ++ (chunk0018SuffixChars00 ++ tail))).bind
        (chunk0018AfterValue00 (fuel + 454) acc) := array_chunk0018_head fuel (chunk0018SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0134746Value, chunk0018SuffixChars00 ++ tail)).bind
        (chunk0018AfterValue00 (fuel + 454) acc) :=
      congrArg (fun result => result.bind (chunk0018AfterValue00 (fuel + 454) acc))
        (value_fragment0134746 (fuel + 188) (chunk0018SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 454) (SourceJson.white tail) (chunk0018Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_before_reader"
  err.flush

noncomputable def chunk0019LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0019SuffixChars00 : List Char := [',']
noncomputable def chunk0019Chars00 : List Char := chunk0019LeadChars00 ++ fragment0136392Chars ++ chunk0019SuffixChars00
noncomputable def chunk0019Push00 (acc : List SourceJson) : List SourceJson := fragment0136392Value :: acc

noncomputable def chunk0019AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0019_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 454)
      (SourceJson.white (chunk0019LeadChars00 ++ (fragment0136392Chars ++ rest))) acc =
      (SourceJson.value (fuel + 453) (fragment0136392Chars ++ rest)).bind
        (chunk0019AfterValue00 (fuel + 453) acc) := by rfl

theorem array_chunk0019 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 454) (SourceJson.white (chunk0019Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 453) (SourceJson.white tail) (chunk0019Push00 acc) := by
  have hinput : chunk0019Chars00 ++ tail = chunk0019LeadChars00 ++ (fragment0136392Chars ++ (chunk0019SuffixChars00 ++ tail)) := by
    simp only [chunk0019Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 454) (SourceJson.white (chunk0019Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 454)
          (SourceJson.white (chunk0019LeadChars00 ++ (fragment0136392Chars ++ (chunk0019SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 454) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 453) (fragment0136392Chars ++ (chunk0019SuffixChars00 ++ tail))).bind
        (chunk0019AfterValue00 (fuel + 453) acc) := array_chunk0019_head fuel (chunk0019SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0136392Value, chunk0019SuffixChars00 ++ tail)).bind
        (chunk0019AfterValue00 (fuel + 453) acc) :=
      congrArg (fun result => result.bind (chunk0019AfterValue00 (fuel + 453) acc))
        (value_fragment0136392 (fuel + 204) (chunk0019SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 453) (SourceJson.white tail) (chunk0019Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0020_before_reader"
  err.flush

noncomputable def chunk0020LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0020SuffixChars00 : List Char := [',']
noncomputable def chunk0020Chars00 : List Char := chunk0020LeadChars00 ++ fragment0138011Chars ++ chunk0020SuffixChars00
noncomputable def chunk0020Push00 (acc : List SourceJson) : List SourceJson := fragment0138011Value :: acc

noncomputable def chunk0020AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0020_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 453)
      (SourceJson.white (chunk0020LeadChars00 ++ (fragment0138011Chars ++ rest))) acc =
      (SourceJson.value (fuel + 452) (fragment0138011Chars ++ rest)).bind
        (chunk0020AfterValue00 (fuel + 452) acc) := by rfl

theorem array_chunk0020 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 453) (SourceJson.white (chunk0020Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 452) (SourceJson.white tail) (chunk0020Push00 acc) := by
  have hinput : chunk0020Chars00 ++ tail = chunk0020LeadChars00 ++ (fragment0138011Chars ++ (chunk0020SuffixChars00 ++ tail)) := by
    simp only [chunk0020Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 453) (SourceJson.white (chunk0020Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 453)
          (SourceJson.white (chunk0020LeadChars00 ++ (fragment0138011Chars ++ (chunk0020SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 453) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 452) (fragment0138011Chars ++ (chunk0020SuffixChars00 ++ tail))).bind
        (chunk0020AfterValue00 (fuel + 452) acc) := array_chunk0020_head fuel (chunk0020SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0138011Value, chunk0020SuffixChars00 ++ tail)).bind
        (chunk0020AfterValue00 (fuel + 452) acc) :=
      congrArg (fun result => result.bind (chunk0020AfterValue00 (fuel + 452) acc))
        (value_fragment0138011 (fuel + 46) (chunk0020SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 452) (SourceJson.white tail) (chunk0020Push00 acc) := by rfl

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
noncomputable def chunk0021Chars00 : List Char := chunk0021LeadChars00 ++ fragment0139954Chars ++ chunk0021SuffixChars00
noncomputable def chunk0021Push00 (acc : List SourceJson) : List SourceJson := fragment0139954Value :: acc

noncomputable def chunk0021AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0021_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 452)
      (SourceJson.white (chunk0021LeadChars00 ++ (fragment0139954Chars ++ rest))) acc =
      (SourceJson.value (fuel + 451) (fragment0139954Chars ++ rest)).bind
        (chunk0021AfterValue00 (fuel + 451) acc) := by rfl

theorem array_chunk0021 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 452) (SourceJson.white (chunk0021Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 451) (SourceJson.white tail) (chunk0021Push00 acc) := by
  have hinput : chunk0021Chars00 ++ tail = chunk0021LeadChars00 ++ (fragment0139954Chars ++ (chunk0021SuffixChars00 ++ tail)) := by
    simp only [chunk0021Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 452) (SourceJson.white (chunk0021Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 452)
          (SourceJson.white (chunk0021LeadChars00 ++ (fragment0139954Chars ++ (chunk0021SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 452) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 451) (fragment0139954Chars ++ (chunk0021SuffixChars00 ++ tail))).bind
        (chunk0021AfterValue00 (fuel + 451) acc) := array_chunk0021_head fuel (chunk0021SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0139954Value, chunk0021SuffixChars00 ++ tail)).bind
        (chunk0021AfterValue00 (fuel + 451) acc) :=
      congrArg (fun result => result.bind (chunk0021AfterValue00 (fuel + 451) acc))
        (value_fragment0139954 (fuel + 180) (chunk0021SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 451) (SourceJson.white tail) (chunk0021Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0021_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0022_before_reader"
  err.flush

noncomputable def chunk0022LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0022SuffixChars00 : List Char := [',']
noncomputable def chunk0022Chars00 : List Char := chunk0022LeadChars00 ++ fragment0141618Chars ++ chunk0022SuffixChars00
noncomputable def chunk0022Push00 (acc : List SourceJson) : List SourceJson := fragment0141618Value :: acc

noncomputable def chunk0022AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0022_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 451)
      (SourceJson.white (chunk0022LeadChars00 ++ (fragment0141618Chars ++ rest))) acc =
      (SourceJson.value (fuel + 450) (fragment0141618Chars ++ rest)).bind
        (chunk0022AfterValue00 (fuel + 450) acc) := by rfl

theorem array_chunk0022 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 451) (SourceJson.white (chunk0022Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 450) (SourceJson.white tail) (chunk0022Push00 acc) := by
  have hinput : chunk0022Chars00 ++ tail = chunk0022LeadChars00 ++ (fragment0141618Chars ++ (chunk0022SuffixChars00 ++ tail)) := by
    simp only [chunk0022Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 451) (SourceJson.white (chunk0022Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 451)
          (SourceJson.white (chunk0022LeadChars00 ++ (fragment0141618Chars ++ (chunk0022SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 451) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 450) (fragment0141618Chars ++ (chunk0022SuffixChars00 ++ tail))).bind
        (chunk0022AfterValue00 (fuel + 450) acc) := array_chunk0022_head fuel (chunk0022SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0141618Value, chunk0022SuffixChars00 ++ tail)).bind
        (chunk0022AfterValue00 (fuel + 450) acc) :=
      congrArg (fun result => result.bind (chunk0022AfterValue00 (fuel + 450) acc))
        (value_fragment0141618 (fuel + 171) (chunk0022SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 450) (SourceJson.white tail) (chunk0022Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0022_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0023_before_reader"
  err.flush

noncomputable def chunk0023LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0023SuffixChars00 : List Char := [',']
noncomputable def chunk0023Chars00 : List Char := chunk0023LeadChars00 ++ fragment0143305Chars ++ chunk0023SuffixChars00
noncomputable def chunk0023Push00 (acc : List SourceJson) : List SourceJson := fragment0143305Value :: acc

noncomputable def chunk0023AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0023_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 450)
      (SourceJson.white (chunk0023LeadChars00 ++ (fragment0143305Chars ++ rest))) acc =
      (SourceJson.value (fuel + 449) (fragment0143305Chars ++ rest)).bind
        (chunk0023AfterValue00 (fuel + 449) acc) := by rfl

theorem array_chunk0023 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 450) (SourceJson.white (chunk0023Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 449) (SourceJson.white tail) (chunk0023Push00 acc) := by
  have hinput : chunk0023Chars00 ++ tail = chunk0023LeadChars00 ++ (fragment0143305Chars ++ (chunk0023SuffixChars00 ++ tail)) := by
    simp only [chunk0023Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 450) (SourceJson.white (chunk0023Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 450)
          (SourceJson.white (chunk0023LeadChars00 ++ (fragment0143305Chars ++ (chunk0023SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 450) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 449) (fragment0143305Chars ++ (chunk0023SuffixChars00 ++ tail))).bind
        (chunk0023AfterValue00 (fuel + 449) acc) := array_chunk0023_head fuel (chunk0023SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0143305Value, chunk0023SuffixChars00 ++ tail)).bind
        (chunk0023AfterValue00 (fuel + 449) acc) :=
      congrArg (fun result => result.bind (chunk0023AfterValue00 (fuel + 449) acc))
        (value_fragment0143305 (fuel + 6) (chunk0023SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 449) (SourceJson.white tail) (chunk0023Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0023_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0016Chars00 ++ chunk0017Chars00 ++ chunk0018Chars00 ++ chunk0019Chars00 ++ chunk0020Chars00 ++ chunk0021Chars00 ++ chunk0022Chars00 ++ chunk0023Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0023Push00 (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 457) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 449) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 457) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 457) (SourceJson.white (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 457) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 456) (SourceJson.white (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))))) (chunk0016Push00 (acc)) := array_chunk0016 fuel (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 455) (SourceJson.white (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) (chunk0017Push00 (chunk0016Push00 (acc))) := array_chunk0017 fuel (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))) (chunk0016Push00 (acc))
    _ = SourceJson.array (fuel + 454) (SourceJson.white (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))) (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))) := array_chunk0018 fuel (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))) (chunk0017Push00 (chunk0016Push00 (acc)))
    _ = SourceJson.array (fuel + 453) (SourceJson.white (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))) (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))) := array_chunk0019 fuel (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))) (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))
    _ = SourceJson.array (fuel + 452) (SourceJson.white (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))) (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))) := array_chunk0020 fuel (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))) (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))
    _ = SourceJson.array (fuel + 451) (SourceJson.white (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))) (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))) := array_chunk0021 fuel (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))) (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))
    _ = SourceJson.array (fuel + 450) (SourceJson.white (chunk0023Chars00 ++ (tail))) (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))))) := array_chunk0022 fuel (chunk0023Chars00 ++ (tail)) (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))))
    _ = SourceJson.array (fuel + 449) (SourceJson.white tail) (blockPush acc) := array_chunk0023 fuel (tail) (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 131386).take 13941 = blockChars := by rfl

theorem block_original_split : sourceRest 131386 = blockChars ++ sourceRest 145327 := by
  calc
    sourceRest 131386 = (sourceRest 131386).take 13941 ++ (sourceRest 131386).drop 13941 :=
      (List.take_append_drop 13941 (sourceRest 131386)).symm
    _ = blockChars ++ (sourceRest 131386).drop 13941 :=
      congrArg (fun part => part ++ (sourceRest 131386).drop 13941) block_original_prefix
    _ = blockChars ++ sourceRest 145327 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 131386 13941)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 457) (SourceJson.white (sourceRest 131386)) acc =
      SourceJson.array (fuel + 449) (SourceJson.white (sourceRest 145327)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 457) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 145327) acc)

#print axioms object_fragment0131392_field_000
#print axioms object_fragment0131392_field_001
#print axioms object_fragment0131392_field_002
#print axioms object_fragment0131392_field_003
#print axioms object_fragment0131392_field_004
#print axioms object_fragment0131392_field_005
#print axioms object_fragment0131392_field_006
#print axioms object_fragment0131392_field_007
#print axioms object_fragment0131392_field_008
#print axioms object_fragment0131392_field_009
#print axioms value_fragment0131392
#print axioms object_fragment0133064_field_000
#print axioms object_fragment0133064_field_001
#print axioms object_fragment0133064_field_002
#print axioms object_fragment0133064_field_003
#print axioms object_fragment0133064_field_004
#print axioms object_fragment0133064_field_005
#print axioms object_fragment0133064_field_006
#print axioms object_fragment0133064_field_007
#print axioms object_fragment0133064_field_008
#print axioms object_fragment0133064_field_009
#print axioms value_fragment0133064
#print axioms object_fragment0134746_field_000
#print axioms object_fragment0134746_field_001
#print axioms object_fragment0134746_field_002
#print axioms object_fragment0134746_field_003
#print axioms object_fragment0134746_field_004
#print axioms object_fragment0134746_field_005
#print axioms object_fragment0134746_field_006
#print axioms object_fragment0134746_field_007
#print axioms object_fragment0134746_field_008
#print axioms object_fragment0134746_field_009
#print axioms value_fragment0134746
#print axioms object_fragment0136392_field_000
#print axioms object_fragment0136392_field_001
#print axioms object_fragment0136392_field_002
#print axioms object_fragment0136392_field_003
#print axioms object_fragment0136392_field_004
#print axioms object_fragment0136392_field_005
#print axioms object_fragment0136392_field_006
#print axioms object_fragment0136392_field_007
#print axioms object_fragment0136392_field_008
#print axioms object_fragment0136392_field_009
#print axioms value_fragment0136392
#print axioms object_fragment0138011_field_000
#print axioms object_fragment0138011_field_001
#print axioms object_fragment0138011_field_002
#print axioms object_fragment0138011_field_003
#print axioms object_fragment0138011_field_004
#print axioms object_fragment0138011_field_005
#print axioms object_fragment0138011_field_006
#print axioms object_fragment0138011_field_007
#print axioms object_fragment0138011_field_008
#print axioms object_fragment0138011_field_009
#print axioms value_fragment0138011
#print axioms object_fragment0139954_field_000
#print axioms object_fragment0139954_field_001
#print axioms object_fragment0139954_field_002
#print axioms object_fragment0139954_field_003
#print axioms object_fragment0139954_field_004
#print axioms object_fragment0139954_field_005
#print axioms object_fragment0139954_field_006
#print axioms object_fragment0139954_field_007
#print axioms object_fragment0139954_field_008
#print axioms object_fragment0139954_field_009
#print axioms value_fragment0139954
#print axioms object_fragment0141618_field_000
#print axioms object_fragment0141618_field_001
#print axioms object_fragment0141618_field_002
#print axioms object_fragment0141618_field_003
#print axioms object_fragment0141618_field_004
#print axioms object_fragment0141618_field_005
#print axioms object_fragment0141618_field_006
#print axioms object_fragment0141618_field_007
#print axioms object_fragment0141618_field_008
#print axioms object_fragment0141618_field_009
#print axioms value_fragment0141618
#print axioms object_fragment0143305_field_000
#print axioms object_fragment0143305_field_001
#print axioms object_fragment0143305_field_002
#print axioms object_fragment0143305_field_003
#print axioms object_fragment0143305_field_004
#print axioms object_fragment0143305_field_005
#print axioms object_fragment0143305_field_006
#print axioms object_fragment0143305_field_007
#print axioms object_fragment0143305_field_008
#print axioms object_fragment0143305_field_009
#print axioms value_fragment0143305
#print axioms array_chunk0016_head
#print axioms array_chunk0016
#print axioms array_chunk0017_head
#print axioms array_chunk0017
#print axioms array_chunk0018_head
#print axioms array_chunk0018
#print axioms array_chunk0019_head
#print axioms array_chunk0019
#print axioms array_chunk0020_head
#print axioms array_chunk0020
#print axioms array_chunk0021_head
#print axioms array_chunk0021
#print axioms array_chunk0022_head
#print axioms array_chunk0022
#print axioms array_chunk0023_head
#print axioms array_chunk0023
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock002

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
