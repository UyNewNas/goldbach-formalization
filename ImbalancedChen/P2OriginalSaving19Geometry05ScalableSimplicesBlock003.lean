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

namespace SimplicesBlock003

noncomputable def fragment0145333Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0145333Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0145333Field000Value00 : SourceJson := .number (String.ofList ['2', '4'])
noncomputable def fragment0145333Acc00100 : List (String × SourceJson) := (fragment0145333Field000Key00, fragment0145333Field000Value00) :: fragment0145333Acc00000
noncomputable def fragment0145333Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '4', ',']

theorem object_fragment0145333_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 314) (SourceJson.white (fragment0145333Field000Chars00 ++ tail)) fragment0145333Acc00000 =
      SourceJson.object (fuel + 313) (SourceJson.white tail) fragment0145333Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145333_object_field_000"
  err.flush

noncomputable def fragment0145333Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0145333Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0145333Acc00200 : List (String × SourceJson) := (fragment0145333Field001Key00, fragment0145333Field001Value00) :: fragment0145333Acc00100
noncomputable def fragment0145333Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0145333_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 313) (SourceJson.white (fragment0145333Field001Chars00 ++ tail)) fragment0145333Acc00100 =
      SourceJson.object (fuel + 312) (SourceJson.white tail) fragment0145333Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145333_object_field_001"
  err.flush

noncomputable def fragment0145333Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0145333Field002Value00 : SourceJson := .str (String.ofList ['9', '2', '0', '1', '6', '6', '3', '9', '3', '5', '0', '2', '2', '5', '9', '3', '6', '2', '6', '6', '4', '8', '7', '2', '2', '6', '2', '4', '9', '5', '9', '8', '5', '6', '1', '3', '/', '2', '0', '9', '7', '8', '3', '8', '4', '1', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0145333Acc00300 : List (String × SourceJson) := (fragment0145333Field002Key00, fragment0145333Field002Value00) :: fragment0145333Acc00200
noncomputable def fragment0145333Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '2', '0', '1', '6', '6', '3', '9', '3', '5', '0', '2', '2', '5', '9', '3', '6', '2', '6', '6', '4', '8', '7', '2', '2', '6', '2', '4', '9', '5', '9', '8', '5', '6', '1', '3', '/', '2', '0', '9', '7', '8', '3', '8', '4', '1', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0145333_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 312) (SourceJson.white (fragment0145333Field002Chars00 ++ tail)) fragment0145333Acc00200 =
      SourceJson.object (fuel + 311) (SourceJson.white tail) fragment0145333Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145333_object_field_002"
  err.flush

noncomputable def fragment0145333Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0145333Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0145333Acc00400 : List (String × SourceJson) := (fragment0145333Field003Key00, fragment0145333Field003Value00) :: fragment0145333Acc00300
noncomputable def fragment0145333Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0145333_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 311) (SourceJson.white (fragment0145333Field003Chars00 ++ tail)) fragment0145333Acc00300 =
      SourceJson.object (fuel + 310) (SourceJson.white tail) fragment0145333Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145333_object_field_003"
  err.flush

noncomputable def fragment0145333Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0145333Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0145333Acc00500 : List (String × SourceJson) := (fragment0145333Field004Key00, fragment0145333Field004Value00) :: fragment0145333Acc00400
noncomputable def fragment0145333Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0145333_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 310) (SourceJson.white (fragment0145333Field004Chars00 ++ tail)) fragment0145333Acc00400 =
      SourceJson.object (fuel + 309) (SourceJson.white tail) fragment0145333Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145333_object_field_004"
  err.flush

noncomputable def fragment0145333Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0145333Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '7', '8', '2', '3', '2', '2', '2', '9', '9', '3', '2', '7', '1', '6', '3', '3', '/', '6', '4', '4', '6', '0', '3', '2', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '6', '9', '1', '9', '8', '9', '0', '6', '1', '0', '5', '6', '9', '1', '/', '8', '0', '5', '7', '5', '4', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '6', '1', '1', '6', '4', '8', '7', '7', '9', '1', '1', '5', '0', '3', '/', '6', '4', '4', '6', '0', '3', '2', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '8', '6', '0', '4', '2', '1', '0', '8', '6', '1', '1', '7', '7', '5', '1', '/', '1', '6', '1', '1', '5', '0', '8', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '4', '6', '8', '8', '1', '4', '6', '3', '7', '9', '2', '9', '8', '9', '/', '1', '6', '1', '1', '5', '0', '8', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '0', '5', '6', '0', '7', '9', '4', '9', '6', '9', '3', '1', '7', '9', '/', '3', '2', '2', '3', '0', '1', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '2', '4', '8', '5', '0', '3', '9', '7', '7', '4', '5', '5', '9', '7', '/', '3', '2', '2', '3', '0', '1', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '4', '5', '2', '8', '5', '4', '0', '1', '0', '2', '1', '7', '1', '/', '1', '0', '7', '4', '3', '3', '8', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '8', '6', '4', '0', '8', '3', '8', '8', '6', '8', '3', '6', '1', '1', '/', '1', '0', '7', '4', '3', '3', '8', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '6', '3', '3', '2', '9', '2', '3', '0', '1', '6', '2', '5', '9', '/', '2', '6', '8', '5', '8', '4', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0145333Acc00600 : List (String × SourceJson) := (fragment0145333Field005Key00, fragment0145333Field005Value00) :: fragment0145333Acc00500
noncomputable def fragment0145333Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '8', '2', '3', '2', '2', '2', '9', '9', '3', '2', '7', '1', '6', '3', '3', '/', '6', '4', '4', '6', '0', '3', '2', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '6', '9', '1', '9', '8', '9', '0', '6', '1', '0', '5', '6', '9', '1', '/', '8', '0', '5', '7', '5', '4', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '6', '1', '1', '6', '4', '8', '7', '7', '9', '1', '1', '5', '0', '3', '/', '6', '4', '4', '6', '0', '3', '2', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '6', '0', '4', '2', '1', '0', '8', '6', '1', '1', '7', '7', '5', '1', '/', '1', '6', '1', '1', '5', '0', '8', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '4', '6', '8', '8', '1', '4', '6', '3', '7', '9', '2', '9', '8', '9', '/', '1', '6', '1', '1', '5', '0', '8', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '0', '5', '6', '0', '7', '9', '4', '9', '6', '9', '3', '1', '7', '9', '/', '3', '2', '2', '3', '0', '1', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '2', '4', '8', '5', '0', '3', '9', '7', '7', '4', '5', '5', '9', '7', '/', '3', '2', '2', '3', '0', '1', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '1', '4', '5', '2', '8', '5', '4', '0', '1', '0', '2', '1', '7', '1', '/', '1', '0', '7', '4', '3', '3', '8', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '8', '6', '4', '0', '8', '3', '8', '8', '6', '8', '3', '6', '1', '1', '/', '1', '0', '7', '4', '3', '3', '8', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '6', '3', '3', '2', '9', '2', '3', '0', '1', '6', '2', '5', '9', '/', '2', '6', '8', '5', '8', '4', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0145333_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 309) (SourceJson.white (fragment0145333Field005Chars00 ++ tail)) fragment0145333Acc00500 =
      SourceJson.object (fuel + 308) (SourceJson.white tail) fragment0145333Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145333_object_field_005"
  err.flush

noncomputable def fragment0145333Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0145333Field006Value00 : SourceJson := .str (String.ofList ['1', '0', '4', '5', '1', '1', '0', '4', '1', '6', '7', '9', '6', '8', '3', '5', '6', '3', '3', '1', '9', '0', '4', '5', '4', '4', '1', '3', '3', '0', '2', '9', '9', '4', '1', '6', '5', '4', '1', '6', '5', '9', '3', '5', '7', '2', '7', '5', '0', '0', '0', '0', '/', '4', '6', '8', '1', '2', '5', '3', '0', '1', '1', '2', '3', '6', '3', '8', '4', '1', '2', '3', '8', '4', '8', '1', '8', '1', '8', '2', '6', '4', '7', '5', '6', '3', '5', '5', '0', '9', '0', '4', '7', '1', '1', '7', '4', '9', '5', '3', '2', '0', '1', '5', '8', '6', '6', '9', '9', '2', '9', '3', '3', '4', '6', '9', '3', '9'])
noncomputable def fragment0145333Acc00700 : List (String × SourceJson) := (fragment0145333Field006Key00, fragment0145333Field006Value00) :: fragment0145333Acc00600
noncomputable def fragment0145333Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '4', '5', '1', '1', '0', '4', '1', '6', '7', '9', '6', '8', '3', '5', '6', '3', '3', '1', '9', '0', '4', '5', '4', '4', '1', '3', '3', '0', '2', '9', '9', '4', '1', '6', '5', '4', '1', '6', '5', '9', '3', '5', '7', '2', '7', '5', '0', '0', '0', '0', '/', '4', '6', '8', '1', '2', '5', '3', '0', '1', '1', '2', '3', '6', '3', '8', '4', '1', '2', '3', '8', '4', '8', '1', '8', '1', '8', '2', '6', '4', '7', '5', '6', '3', '5', '5', '0', '9', '0', '4', '7', '1', '1', '7', '4', '9', '5', '3', '2', '0', '1', '5', '8', '6', '6', '9', '9', '2', '9', '3', '3', '4', '6', '9', '3', '9', '"', ',']

theorem object_fragment0145333_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 308) (SourceJson.white (fragment0145333Field006Chars00 ++ tail)) fragment0145333Acc00600 =
      SourceJson.object (fuel + 307) (SourceJson.white tail) fragment0145333Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145333_object_field_006"
  err.flush

noncomputable def fragment0145333Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0145333Field007Value00 : SourceJson := .str (String.ofList ['1', '2', '7', '1', '5', '5', '8', '8', '2', '8', '2', '8', '3', '9', '1', '4', '5', '2', '0', '0', '2', '6', '7', '5', '0', '3', '1', '7', '0', '3', '1', '3', '6', '3', '7', '2', '3', '2', '7', '8', '9', '4', '7', '4', '7', '6', '4', '5', '0', '8', '6', '8', '9', '0', '1', '5', '1', '8', '5', '3', '1', '8', '8', '6', '9', '5', '1', '0', '4', '0', '9', '8', '3', '6', '1', '5', '1', '6', '1', '0', '3', '3', '0', '5', '1', '2', '5', '0', '4', '8', '1', '6', '1', '9', '9', '6', '5', '9', '3', '0', '2', '6', '9', '6', '6', '4', '0', '8', '3', '1', '8', '6', '4', '5', '0', '1', '6', '9', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '6', '2', '8', '8', '6', '9', '8', '0', '7', '3', '1', '5', '5', '1', '4', '6', '6', '0', '0', '9', '1', '5', '2', '3', '9', '5', '9', '8', '5', '0', '6', '7', '6', '2', '2', '6', '1', '4', '3', '3', '1', '9', '3', '1', '0', '9', '1', '9', '1', '3', '4', '7', '6', '8', '7', '6', '7', '1', '0', '0', '2', '6', '0', '9', '3', '4', '2', '0', '6', '8', '4', '1', '3', '3', '8', '6', '7', '4', '0', '6', '1', '2', '7', '3', '1', '9', '8', '7', '1', '1', '4', '4', '3', '2', '0', '5', '4', '5', '3', '7', '9', '6', '3', '1', '9', '2', '2', '0', '5', '4', '1', '3', '1', '5', '9', '4', '0', '6', '0', '8', '3', '5', '2', '7', '8', '2', '0', '5', '0', '3', '1', '8', '4', '5', '7', '8', '1', '4', '1', '2', '9', '8', '0', '9', '4', '2', '1', '9', '8', '2', '2', '6', '5', '2', '5', '7'])
noncomputable def fragment0145333Acc00800 : List (String × SourceJson) := (fragment0145333Field007Key00, fragment0145333Field007Value00) :: fragment0145333Acc00700
noncomputable def fragment0145333Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '7', '1', '5', '5', '8', '8', '2', '8', '2', '8', '3', '9', '1', '4', '5', '2', '0', '0', '2', '6', '7', '5', '0', '3', '1', '7', '0', '3', '1', '3', '6', '3', '7', '2', '3', '2', '7', '8', '9', '4', '7', '4', '7', '6', '4', '5', '0', '8', '6', '8', '9', '0', '1', '5', '1', '8', '5', '3', '1', '8', '8', '6', '9', '5', '1', '0', '4', '0', '9', '8', '3', '6', '1', '5', '1', '6', '1', '0', '3', '3', '0', '5', '1', '2', '5', '0', '4', '8', '1', '6', '1', '9', '9', '6', '5', '9', '3', '0', '2', '6', '9', '6', '6', '4', '0', '8', '3', '1', '8', '6', '4', '5', '0', '1', '6', '9', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '6', '2', '8', '8', '6', '9', '8', '0', '7', '3', '1', '5', '5', '1', '4', '6', '6', '0', '0', '9', '1', '5', '2', '3', '9', '5', '9', '8', '5', '0', '6', '7', '6', '2', '2', '6', '1', '4', '3', '3', '1', '9', '3', '1', '0', '9', '1', '9', '1', '3', '4', '7', '6', '8', '7', '6', '7', '1', '0', '0', '2', '6', '0', '9', '3', '4', '2', '0', '6', '8', '4', '1', '3', '3', '8', '6', '7', '4', '0', '6', '1', '2', '7', '3', '1', '9', '8', '7', '1', '1', '4', '4', '3', '2', '0', '5', '4', '5', '3', '7', '9', '6', '3', '1', '9', '2', '2', '0', '5', '4', '1', '3', '1', '5', '9', '4', '0', '6', '0', '8', '3', '5', '2', '7', '8', '2', '0', '5', '0', '3', '1', '8', '4', '5', '7', '8', '1', '4', '1', '2', '9', '8', '0', '9', '4', '2', '1', '9', '8', '2', '2', '6', '5', '2', '5', '7', '"', ',']

theorem object_fragment0145333_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 307) (SourceJson.white (fragment0145333Field007Chars00 ++ tail)) fragment0145333Acc00700 =
      SourceJson.object (fuel + 306) (SourceJson.white tail) fragment0145333Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145333_object_field_007"
  err.flush

noncomputable def fragment0145333Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0145333Field008Value00 : SourceJson := .str (String.ofList ['1', '7', '6', '8', '8', '0', '3', '7', '3', '1', '5', '7', '7', '4', '3', '5'])
noncomputable def fragment0145333Acc00900 : List (String × SourceJson) := (fragment0145333Field008Key00, fragment0145333Field008Value00) :: fragment0145333Acc00800
noncomputable def fragment0145333Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '6', '8', '8', '0', '3', '7', '3', '1', '5', '7', '7', '4', '3', '5', '"', ',']

theorem object_fragment0145333_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 306) (SourceJson.white (fragment0145333Field008Chars00 ++ tail)) fragment0145333Acc00800 =
      SourceJson.object (fuel + 305) (SourceJson.white tail) fragment0145333Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145333_object_field_008"
  err.flush

noncomputable def fragment0145333Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0145333Field009Value00 : SourceJson := .str (String.ofList ['5', '7', '1', '4', '6', '7', '5', '4', '4', '9', '6', '9', '4', '4', '3', '9'])
noncomputable def fragment0145333Acc01000 : List (String × SourceJson) := (fragment0145333Field009Key00, fragment0145333Field009Value00) :: fragment0145333Acc00900
noncomputable def fragment0145333Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '7', '1', '4', '6', '7', '5', '4', '4', '9', '6', '9', '4', '4', '3', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0145333_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 305) (SourceJson.white (fragment0145333Field009Chars00 ++ tail)) fragment0145333Acc00900 =
      .ok (.obj (fragment0145333Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145333_object_field_009"
  err.flush

noncomputable def fragment0145333Chars : List Char := '{' :: (fragment0145333Field000Chars00 ++ fragment0145333Field001Chars00 ++ fragment0145333Field002Chars00 ++ fragment0145333Field003Chars00 ++ fragment0145333Field004Chars00 ++ fragment0145333Field005Chars00 ++ fragment0145333Field006Chars00 ++ fragment0145333Field007Chars00 ++ fragment0145333Field008Chars00 ++ fragment0145333Field009Chars00)
noncomputable def fragment0145333Value : SourceJson := .obj (fragment0145333Acc01000.reverse)

theorem value_fragment0145333 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 315) (fragment0145333Chars ++ tail) =
      .ok (fragment0145333Value, tail) := by
  have hinput : fragment0145333Chars ++ tail = '{' :: (fragment0145333Field000Chars00 ++ (fragment0145333Field001Chars00 ++ (fragment0145333Field002Chars00 ++ (fragment0145333Field003Chars00 ++ (fragment0145333Field004Chars00 ++ (fragment0145333Field005Chars00 ++ (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0145333Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 315) (fragment0145333Chars ++ tail) =
        SourceJson.value (fuel + 315) ('{' :: (fragment0145333Field000Chars00 ++ (fragment0145333Field001Chars00 ++ (fragment0145333Field002Chars00 ++ (fragment0145333Field003Chars00 ++ (fragment0145333Field004Chars00 ++ (fragment0145333Field005Chars00 ++ (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 315)) hinput
    _ = SourceJson.object (fuel + 314) (SourceJson.white (fragment0145333Field000Chars00 ++ (fragment0145333Field001Chars00 ++ (fragment0145333Field002Chars00 ++ (fragment0145333Field003Chars00 ++ (fragment0145333Field004Chars00 ++ (fragment0145333Field005Chars00 ++ (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail)))))))))))) fragment0145333Acc00000 := by rfl
    _ = SourceJson.object (fuel + 313) (SourceJson.white (fragment0145333Field001Chars00 ++ (fragment0145333Field002Chars00 ++ (fragment0145333Field003Chars00 ++ (fragment0145333Field004Chars00 ++ (fragment0145333Field005Chars00 ++ (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail))))))))))) fragment0145333Acc00100 := object_fragment0145333_field_000 fuel (fragment0145333Field001Chars00 ++ (fragment0145333Field002Chars00 ++ (fragment0145333Field003Chars00 ++ (fragment0145333Field004Chars00 ++ (fragment0145333Field005Chars00 ++ (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 312) (SourceJson.white (fragment0145333Field002Chars00 ++ (fragment0145333Field003Chars00 ++ (fragment0145333Field004Chars00 ++ (fragment0145333Field005Chars00 ++ (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail)))))))))) fragment0145333Acc00200 := object_fragment0145333_field_001 fuel (fragment0145333Field002Chars00 ++ (fragment0145333Field003Chars00 ++ (fragment0145333Field004Chars00 ++ (fragment0145333Field005Chars00 ++ (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 311) (SourceJson.white (fragment0145333Field003Chars00 ++ (fragment0145333Field004Chars00 ++ (fragment0145333Field005Chars00 ++ (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail))))))))) fragment0145333Acc00300 := object_fragment0145333_field_002 fuel (fragment0145333Field003Chars00 ++ (fragment0145333Field004Chars00 ++ (fragment0145333Field005Chars00 ++ (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 310) (SourceJson.white (fragment0145333Field004Chars00 ++ (fragment0145333Field005Chars00 ++ (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail)))))))) fragment0145333Acc00400 := object_fragment0145333_field_003 fuel (fragment0145333Field004Chars00 ++ (fragment0145333Field005Chars00 ++ (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 309) (SourceJson.white (fragment0145333Field005Chars00 ++ (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail))))))) fragment0145333Acc00500 := object_fragment0145333_field_004 fuel (fragment0145333Field005Chars00 ++ (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 308) (SourceJson.white (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail)))))) fragment0145333Acc00600 := object_fragment0145333_field_005 fuel (fragment0145333Field006Chars00 ++ (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 307) (SourceJson.white (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail))))) fragment0145333Acc00700 := object_fragment0145333_field_006 fuel (fragment0145333Field007Chars00 ++ (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 306) (SourceJson.white (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail)))) fragment0145333Acc00800 := object_fragment0145333_field_007 fuel (fragment0145333Field008Chars00 ++ (fragment0145333Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 305) (SourceJson.white (fragment0145333Field009Chars00 ++ (tail))) fragment0145333Acc00900 := object_fragment0145333_field_008 fuel (fragment0145333Field009Chars00 ++ (tail))
    _ = .ok (fragment0145333Value, tail) := object_fragment0145333_field_009 fuel (tail)

noncomputable def fragment0147088Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0147088Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0147088Field000Value00 : SourceJson := .number (String.ofList ['2', '5'])
noncomputable def fragment0147088Acc00100 : List (String × SourceJson) := (fragment0147088Field000Key00, fragment0147088Field000Value00) :: fragment0147088Acc00000
noncomputable def fragment0147088Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '5', ',']

theorem object_fragment0147088_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0147088Field000Chars00 ++ tail)) fragment0147088Acc00000 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment0147088Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147088_object_field_000"
  err.flush

noncomputable def fragment0147088Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0147088Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['5']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0147088Acc00200 : List (String × SourceJson) := (fragment0147088Field001Key00, fragment0147088Field001Value00) :: fragment0147088Acc00100
noncomputable def fragment0147088Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0147088_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0147088Field001Chars00 ++ tail)) fragment0147088Acc00100 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0147088Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147088_object_field_001"
  err.flush

noncomputable def fragment0147088Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0147088Field002Value00 : SourceJson := .str (String.ofList ['8', '8', '5', '6', '3', '3', '0', '9', '7', '6', '8', '3', '1', '2', '7', '8', '7', '2', '7', '4', '2', '3', '7', '9', '6', '2', '3', '8', '0', '1', '3', '/', '1', '5', '5', '1', '2', '3', '5', '6', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0147088Acc00300 : List (String × SourceJson) := (fragment0147088Field002Key00, fragment0147088Field002Value00) :: fragment0147088Acc00200
noncomputable def fragment0147088Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '8', '8', '5', '6', '3', '3', '0', '9', '7', '6', '8', '3', '1', '2', '7', '8', '7', '2', '7', '4', '2', '3', '7', '9', '6', '2', '3', '8', '0', '1', '3', '/', '1', '5', '5', '1', '2', '3', '5', '6', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0147088_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0147088Field002Chars00 ++ tail)) fragment0147088Acc00200 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0147088Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147088_object_field_002"
  err.flush

noncomputable def fragment0147088Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0147088Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0147088Acc00400 : List (String × SourceJson) := (fragment0147088Field003Key00, fragment0147088Field003Value00) :: fragment0147088Acc00300
noncomputable def fragment0147088Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0147088_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0147088Field003Chars00 ++ tail)) fragment0147088Acc00300 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0147088Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147088_object_field_003"
  err.flush

noncomputable def fragment0147088Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0147088Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '9', '8', '4', '4', '0', '3', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '2', '8', '1', '0', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '8', '1', '1', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0147088Acc00500 : List (String × SourceJson) := (fragment0147088Field004Key00, fragment0147088Field004Value00) :: fragment0147088Acc00400
noncomputable def fragment0147088Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '8', '4', '4', '0', '3', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '8', '1', '0', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '8', '1', '1', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0147088_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0147088Field004Chars00 ++ tail)) fragment0147088Acc00400 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0147088Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147088_object_field_004"
  err.flush

noncomputable def fragment0147088Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0147088Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '8', '6', '7', '7', '3', '4', '5', '6', '3', '1', '1', '0', '7', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '8', '9', '7', '6', '4', '7', '1', '1', '3', '2', '1', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '9', '6', '2', '9', '7', '4', '3', '1', '5', '5', '7', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '8', '0', '4', '3', '4', '1', '6', '2', '7', '3', '3', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '6', '7', '3', '5', '5', '3', '1', '8', '6', '9', '7', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '9', '0', '4', '5', '2', '4', '8', '1', '3', '3', '/', '5', '2', '9', '6', '0', '9', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '0', '0', '5', '9', '2', '2', '8', '8', '1', '1', '/', '1', '3', '2', '4', '0', '2', '3', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '0', '9', '6', '5', '2', '3', '3', '8', '3', '/', '7', '3', '5', '5', '6', '8', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '6', '7', '8', '2', '3', '2', '7', '1', '5', '8', '9', '/', '3', '5', '3', '0', '7', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '6', '7', '8', '1', '6', '2', '1', '0', '1', '2', '9', '/', '3', '5', '3', '0', '7', '3', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0147088Acc00600 : List (String × SourceJson) := (fragment0147088Field005Key00, fragment0147088Field005Value00) :: fragment0147088Acc00500
noncomputable def fragment0147088Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '7', '7', '3', '4', '5', '6', '3', '1', '1', '0', '7', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '8', '9', '7', '6', '4', '7', '1', '1', '3', '2', '1', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '9', '6', '2', '9', '7', '4', '3', '1', '5', '5', '7', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '8', '0', '4', '3', '4', '1', '6', '2', '7', '3', '3', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '6', '7', '3', '5', '5', '3', '1', '8', '6', '9', '7', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '9', '0', '4', '5', '2', '4', '8', '1', '3', '3', '/', '5', '2', '9', '6', '0', '9', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '0', '0', '5', '9', '2', '2', '8', '8', '1', '1', '/', '1', '3', '2', '4', '0', '2', '3', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '0', '9', '6', '5', '2', '3', '3', '8', '3', '/', '7', '3', '5', '5', '6', '8', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '7', '8', '2', '3', '2', '7', '1', '5', '8', '9', '/', '3', '5', '3', '0', '7', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '7', '8', '1', '6', '2', '1', '0', '1', '2', '9', '/', '3', '5', '3', '0', '7', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0147088_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0147088Field005Chars00 ++ tail)) fragment0147088Acc00500 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0147088Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147088_object_field_005"
  err.flush

noncomputable def fragment0147088Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0147088Field006Value00 : SourceJson := .str (String.ofList ['1', '3', '6', '0', '4', '5', '1', '2', '9', '5', '5', '7', '2', '7', '3', '0', '3', '7', '8', '1', '7', '0', '0', '3', '3', '5', '9', '6', '1', '4', '9', '7', '9', '7', '3', '8', '0', '7', '6', '8', '6', '6', '1', '5', '0', '4', '0', '0', '0', '0', '0', '/', '4', '0', '8', '3', '5', '5', '2', '0', '4', '4', '8', '4', '7', '7', '0', '2', '2', '0', '8', '0', '6', '1', '2', '1', '0', '5', '2', '3', '8', '9', '5', '7', '3', '2', '6', '5', '1', '8', '5', '3', '6', '4', '1', '2', '3', '0', '7', '4', '2', '3', '5', '8', '3', '9', '8', '1', '3', '2', '0', '5', '4', '5', '8', '9', '0', '7', '8', '7'])
noncomputable def fragment0147088Acc00700 : List (String × SourceJson) := (fragment0147088Field006Key00, fragment0147088Field006Value00) :: fragment0147088Acc00600
noncomputable def fragment0147088Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '6', '0', '4', '5', '1', '2', '9', '5', '5', '7', '2', '7', '3', '0', '3', '7', '8', '1', '7', '0', '0', '3', '3', '5', '9', '6', '1', '4', '9', '7', '9', '7', '3', '8', '0', '7', '6', '8', '6', '6', '1', '5', '0', '4', '0', '0', '0', '0', '0', '/', '4', '0', '8', '3', '5', '5', '2', '0', '4', '4', '8', '4', '7', '7', '0', '2', '2', '0', '8', '0', '6', '1', '2', '1', '0', '5', '2', '3', '8', '9', '5', '7', '3', '2', '6', '5', '1', '8', '5', '3', '6', '4', '1', '2', '3', '0', '7', '4', '2', '3', '5', '8', '3', '9', '8', '1', '3', '2', '0', '5', '4', '5', '8', '9', '0', '7', '8', '7', '"', ',']

theorem object_fragment0147088_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0147088Field006Chars00 ++ tail)) fragment0147088Acc00600 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0147088Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147088_object_field_006"
  err.flush

noncomputable def fragment0147088Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0147088Field007Value00 : SourceJson := .str (String.ofList ['1', '9', '0', '7', '7', '8', '6', '3', '6', '2', '1', '9', '0', '8', '2', '6', '3', '7', '5', '8', '2', '3', '5', '3', '0', '1', '7', '5', '2', '2', '4', '2', '0', '1', '7', '8', '4', '7', '5', '0', '7', '0', '0', '0', '7', '2', '4', '1', '7', '0', '4', '8', '6', '5', '0', '8', '8', '4', '2', '0', '8', '3', '5', '4', '4', '6', '9', '0', '8', '2', '8', '7', '7', '5', '6', '0', '8', '6', '3', '7', '1', '8', '1', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '3', '1', '3', '5', '5', '4', '4', '9', '1', '0', '8', '3', '5', '8', '2', '4', '3', '0', '5', '1', '5', '7', '8', '6', '1', '6', '3', '4', '0', '4', '1', '3', '4', '7', '0', '7', '0', '7', '3', '6', '2', '3', '1', '8', '7', '1', '0', '9', '1', '8', '1', '1', '1', '8', '4', '9', '3', '5', '6', '3', '6', '7', '4', '2', '7', '0', '6', '0', '5', '3', '6', '9', '5', '6', '8', '6', '1', '2', '5', '1', '6', '0', '8', '0', '4', '2', '4', '1', '4', '6', '0', '5', '9', '1', '0', '8', '6', '5', '9', '9', '8', '7', '7', '2', '1', '5', '7', '9', '0', '2', '9', '0', '8', '6', '8', '6', '2', '0', '6', '1'])
noncomputable def fragment0147088Acc00800 : List (String × SourceJson) := (fragment0147088Field007Key00, fragment0147088Field007Value00) :: fragment0147088Acc00700
noncomputable def fragment0147088Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '0', '7', '7', '8', '6', '3', '6', '2', '1', '9', '0', '8', '2', '6', '3', '7', '5', '8', '2', '3', '5', '3', '0', '1', '7', '5', '2', '2', '4', '2', '0', '1', '7', '8', '4', '7', '5', '0', '7', '0', '0', '0', '7', '2', '4', '1', '7', '0', '4', '8', '6', '5', '0', '8', '8', '4', '2', '0', '8', '3', '5', '4', '4', '6', '9', '0', '8', '2', '8', '7', '7', '5', '6', '0', '8', '6', '3', '7', '1', '8', '1', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '3', '1', '3', '5', '5', '4', '4', '9', '1', '0', '8', '3', '5', '8', '2', '4', '3', '0', '5', '1', '5', '7', '8', '6', '1', '6', '3', '4', '0', '4', '1', '3', '4', '7', '0', '7', '0', '7', '3', '6', '2', '3', '1', '8', '7', '1', '0', '9', '1', '8', '1', '1', '1', '8', '4', '9', '3', '5', '6', '3', '6', '7', '4', '2', '7', '0', '6', '0', '5', '3', '6', '9', '5', '6', '8', '6', '1', '2', '5', '1', '6', '0', '8', '0', '4', '2', '4', '1', '4', '6', '0', '5', '9', '1', '0', '8', '6', '5', '9', '9', '8', '7', '7', '2', '1', '5', '7', '9', '0', '2', '9', '0', '8', '6', '8', '6', '2', '0', '6', '1', '"', ',']

theorem object_fragment0147088_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0147088Field007Chars00 ++ tail)) fragment0147088Acc00700 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0147088Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147088_object_field_007"
  err.flush

noncomputable def fragment0147088Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0147088Field008Value00 : SourceJson := .str (String.ofList ['2', '6', '3', '9', '5', '1', '7', '1', '4', '4', '7', '4'])
noncomputable def fragment0147088Acc00900 : List (String × SourceJson) := (fragment0147088Field008Key00, fragment0147088Field008Value00) :: fragment0147088Acc00800
noncomputable def fragment0147088Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '6', '3', '9', '5', '1', '7', '1', '4', '4', '7', '4', '"', ',']

theorem object_fragment0147088_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0147088Field008Chars00 ++ tail)) fragment0147088Acc00800 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0147088Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147088_object_field_008"
  err.flush

noncomputable def fragment0147088Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0147088Field009Value00 : SourceJson := .str (String.ofList ['7', '4', '4', '0', '8', '6', '4', '5', '7', '2', '1', '0'])
noncomputable def fragment0147088Acc01000 : List (String × SourceJson) := (fragment0147088Field009Key00, fragment0147088Field009Value00) :: fragment0147088Acc00900
noncomputable def fragment0147088Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '4', '4', '0', '8', '6', '4', '5', '7', '2', '1', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0147088_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0147088Field009Chars00 ++ tail)) fragment0147088Acc00900 =
      .ok (.obj (fragment0147088Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147088_object_field_009"
  err.flush

noncomputable def fragment0147088Chars : List Char := '{' :: (fragment0147088Field000Chars00 ++ fragment0147088Field001Chars00 ++ fragment0147088Field002Chars00 ++ fragment0147088Field003Chars00 ++ fragment0147088Field004Chars00 ++ fragment0147088Field005Chars00 ++ fragment0147088Field006Chars00 ++ fragment0147088Field007Chars00 ++ fragment0147088Field008Chars00 ++ fragment0147088Field009Chars00)
noncomputable def fragment0147088Value : SourceJson := .obj (fragment0147088Acc01000.reverse)

theorem value_fragment0147088 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 239) (fragment0147088Chars ++ tail) =
      .ok (fragment0147088Value, tail) := by
  have hinput : fragment0147088Chars ++ tail = '{' :: (fragment0147088Field000Chars00 ++ (fragment0147088Field001Chars00 ++ (fragment0147088Field002Chars00 ++ (fragment0147088Field003Chars00 ++ (fragment0147088Field004Chars00 ++ (fragment0147088Field005Chars00 ++ (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0147088Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 239) (fragment0147088Chars ++ tail) =
        SourceJson.value (fuel + 239) ('{' :: (fragment0147088Field000Chars00 ++ (fragment0147088Field001Chars00 ++ (fragment0147088Field002Chars00 ++ (fragment0147088Field003Chars00 ++ (fragment0147088Field004Chars00 ++ (fragment0147088Field005Chars00 ++ (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 239)) hinput
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0147088Field000Chars00 ++ (fragment0147088Field001Chars00 ++ (fragment0147088Field002Chars00 ++ (fragment0147088Field003Chars00 ++ (fragment0147088Field004Chars00 ++ (fragment0147088Field005Chars00 ++ (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail)))))))))))) fragment0147088Acc00000 := by rfl
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0147088Field001Chars00 ++ (fragment0147088Field002Chars00 ++ (fragment0147088Field003Chars00 ++ (fragment0147088Field004Chars00 ++ (fragment0147088Field005Chars00 ++ (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail))))))))))) fragment0147088Acc00100 := object_fragment0147088_field_000 fuel (fragment0147088Field001Chars00 ++ (fragment0147088Field002Chars00 ++ (fragment0147088Field003Chars00 ++ (fragment0147088Field004Chars00 ++ (fragment0147088Field005Chars00 ++ (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0147088Field002Chars00 ++ (fragment0147088Field003Chars00 ++ (fragment0147088Field004Chars00 ++ (fragment0147088Field005Chars00 ++ (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail)))))))))) fragment0147088Acc00200 := object_fragment0147088_field_001 fuel (fragment0147088Field002Chars00 ++ (fragment0147088Field003Chars00 ++ (fragment0147088Field004Chars00 ++ (fragment0147088Field005Chars00 ++ (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0147088Field003Chars00 ++ (fragment0147088Field004Chars00 ++ (fragment0147088Field005Chars00 ++ (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail))))))))) fragment0147088Acc00300 := object_fragment0147088_field_002 fuel (fragment0147088Field003Chars00 ++ (fragment0147088Field004Chars00 ++ (fragment0147088Field005Chars00 ++ (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0147088Field004Chars00 ++ (fragment0147088Field005Chars00 ++ (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail)))))))) fragment0147088Acc00400 := object_fragment0147088_field_003 fuel (fragment0147088Field004Chars00 ++ (fragment0147088Field005Chars00 ++ (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0147088Field005Chars00 ++ (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail))))))) fragment0147088Acc00500 := object_fragment0147088_field_004 fuel (fragment0147088Field005Chars00 ++ (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail)))))) fragment0147088Acc00600 := object_fragment0147088_field_005 fuel (fragment0147088Field006Chars00 ++ (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail))))) fragment0147088Acc00700 := object_fragment0147088_field_006 fuel (fragment0147088Field007Chars00 ++ (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail)))) fragment0147088Acc00800 := object_fragment0147088_field_007 fuel (fragment0147088Field008Chars00 ++ (fragment0147088Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0147088Field009Chars00 ++ (tail))) fragment0147088Acc00900 := object_fragment0147088_field_008 fuel (fragment0147088Field009Chars00 ++ (tail))
    _ = .ok (fragment0147088Value, tail) := object_fragment0147088_field_009 fuel (tail)

noncomputable def fragment0148691Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0148691Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0148691Field000Value00 : SourceJson := .number (String.ofList ['2', '6'])
noncomputable def fragment0148691Acc00100 : List (String × SourceJson) := (fragment0148691Field000Key00, fragment0148691Field000Value00) :: fragment0148691Acc00000
noncomputable def fragment0148691Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '6', ',']

theorem object_fragment0148691_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 407) (SourceJson.white (fragment0148691Field000Chars00 ++ tail)) fragment0148691Acc00000 =
      SourceJson.object (fuel + 406) (SourceJson.white tail) fragment0148691Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0148691_object_field_000"
  err.flush

noncomputable def fragment0148691Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0148691Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0148691Acc00200 : List (String × SourceJson) := (fragment0148691Field001Key00, fragment0148691Field001Value00) :: fragment0148691Acc00100
noncomputable def fragment0148691Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0148691_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 406) (SourceJson.white (fragment0148691Field001Chars00 ++ tail)) fragment0148691Acc00100 =
      SourceJson.object (fuel + 405) (SourceJson.white tail) fragment0148691Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0148691_object_field_001"
  err.flush

noncomputable def fragment0148691Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0148691Field002Value00 : SourceJson := .str (String.ofList ['9', '6', '8', '7', '2', '0', '2', '5', '2', '5', '8', '9', '7', '6', '9', '4', '2', '2', '7', '7', '5', '9', '7', '4', '5', '0', '0', '2', '1', '8', '1', '6', '7', '3', '4', '3', '/', '6', '6', '1', '8', '6', '0', '5', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0148691Acc00300 : List (String × SourceJson) := (fragment0148691Field002Key00, fragment0148691Field002Value00) :: fragment0148691Acc00200
noncomputable def fragment0148691Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '6', '8', '7', '2', '0', '2', '5', '2', '5', '8', '9', '7', '6', '9', '4', '2', '2', '7', '7', '5', '9', '7', '4', '5', '0', '0', '2', '1', '8', '1', '6', '7', '3', '4', '3', '/', '6', '6', '1', '8', '6', '0', '5', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0148691_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 405) (SourceJson.white (fragment0148691Field002Chars00 ++ tail)) fragment0148691Acc00200 =
      SourceJson.object (fuel + 404) (SourceJson.white tail) fragment0148691Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0148691_object_field_002"
  err.flush

noncomputable def fragment0148691Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0148691Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '2', '4', '1', '6', '9', '/', '1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0148691Acc00400 : List (String × SourceJson) := (fragment0148691Field003Key00, fragment0148691Field003Value00) :: fragment0148691Acc00300
noncomputable def fragment0148691Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '8', '2', '4', '1', '6', '9', '/', '1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0148691_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 404) (SourceJson.white (fragment0148691Field003Chars00 ++ tail)) fragment0148691Acc00300 =
      SourceJson.object (fuel + 403) (SourceJson.white tail) fragment0148691Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0148691_object_field_003"
  err.flush

noncomputable def fragment0148691Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0148691Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '9', '8', '4', '4', '0', '3', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '2', '8', '1', '0', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '8', '1', '1', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0148691Acc00500 : List (String × SourceJson) := (fragment0148691Field004Key00, fragment0148691Field004Value00) :: fragment0148691Acc00400
noncomputable def fragment0148691Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '8', '4', '4', '0', '3', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '8', '1', '0', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '8', '1', '1', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0148691_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 403) (SourceJson.white (fragment0148691Field004Chars00 ++ tail)) fragment0148691Acc00400 =
      SourceJson.object (fuel + 402) (SourceJson.white tail) fragment0148691Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0148691_object_field_004"
  err.flush

noncomputable def fragment0148691Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0148691Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '2', '3', '3', '4', '4', '3', '8', '0', '2', '7', '2', '8', '3', '7', '5', '9', '8', '7', '6', '7', '3', '/', '3', '6', '6', '8', '8', '5', '2', '9', '4', '8', '4', '8', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '7', '6', '0', '3', '4', '2', '3', '0', '9', '8', '5', '5', '7', '6', '7', '7', '6', '4', '1', '/', '4', '5', '8', '6', '0', '6', '6', '1', '8', '5', '6', '0', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '0', '8', '6', '2', '0', '3', '6', '6', '6', '3', '9', '6', '9', '2', '7', '6', '2', '7', '/', '7', '3', '3', '7', '7', '0', '5', '8', '9', '6', '9', '6', '7', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '6', '1', '6', '8', '5', '1', '1', '1', '1', '4', '2', '2', '2', '1', '4', '7', '0', '0', '1', '1', '/', '9', '1', '7', '2', '1', '3', '2', '3', '7', '1', '2', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '6', '7', '5', '9', '2', '6', '2', '2', '4', '8', '5', '6', '6', '1', '2', '9', '/', '9', '1', '7', '2', '1', '3', '2', '3', '7', '1', '2', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '9', '2', '9', '1', '1', '1', '8', '0', '3', '3', '6', '0', '1', '6', '8', '9', '7', '9', '/', '1', '8', '3', '4', '4', '2', '6', '4', '7', '4', '2', '4', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '2', '2', '7', '8', '5', '9', '1', '0', '9', '1', '4', '2', '7', '6', '7', '6', '2', '3', '7', '/', '1', '8', '3', '4', '4', '2', '6', '4', '7', '4', '2', '4', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '3', '5', '4', '6', '9', '6', '0', '7', '1', '1', '6', '8', '5', '9', '0', '6', '4', '9', '1', '/', '6', '1', '1', '4', '7', '5', '4', '9', '1', '4', '1', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '6', '9', '8', '6', '3', '3', '6', '9', '9', '9', '1', '2', '4', '5', '2', '6', '2', '1', '1', '/', '6', '1', '1', '4', '7', '5', '4', '9', '1', '4', '1', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '3', '5', '0', '4', '2', '8', '3', '3', '0', '4', '2', '0', '8', '7', '6', '6', '0', '9', '/', '1', '5', '2', '8', '6', '8', '8', '7', '2', '8', '5', '3', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0148691Acc00600 : List (String × SourceJson) := (fragment0148691Field005Key00, fragment0148691Field005Value00) :: fragment0148691Acc00500
noncomputable def fragment0148691Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '3', '3', '4', '4', '3', '8', '0', '2', '7', '2', '8', '3', '7', '5', '9', '8', '7', '6', '7', '3', '/', '3', '6', '6', '8', '8', '5', '2', '9', '4', '8', '4', '8', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '7', '6', '0', '3', '4', '2', '3', '0', '9', '8', '5', '5', '7', '6', '7', '7', '6', '4', '1', '/', '4', '5', '8', '6', '0', '6', '6', '1', '8', '5', '6', '0', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '0', '8', '6', '2', '0', '3', '6', '6', '6', '3', '9', '6', '9', '2', '7', '6', '2', '7', '/', '7', '3', '3', '7', '7', '0', '5', '8', '9', '6', '9', '6', '7', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '6', '1', '6', '8', '5', '1', '1', '1', '1', '4', '2', '2', '2', '1', '4', '7', '0', '0', '1', '1', '/', '9', '1', '7', '2', '1', '3', '2', '3', '7', '1', '2', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '6', '7', '5', '9', '2', '6', '2', '2', '4', '8', '5', '6', '6', '1', '2', '9', '/', '9', '1', '7', '2', '1', '3', '2', '3', '7', '1', '2', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '9', '2', '9', '1', '1', '1', '8', '0', '3', '3', '6', '0', '1', '6', '8', '9', '7', '9', '/', '1', '8', '3', '4', '4', '2', '6', '4', '7', '4', '2', '4', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '0', '2', '2', '7', '8', '5', '9', '1', '0', '9', '1', '4', '2', '7', '6', '7', '6', '2', '3', '7', '/', '1', '8', '3', '4', '4', '2', '6', '4', '7', '4', '2', '4', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '3', '5', '4', '6', '9', '6', '0', '7', '1', '1', '6', '8', '5', '9', '0', '6', '4', '9', '1', '/', '6', '1', '1', '4', '7', '5', '4', '9', '1', '4', '1', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '9', '8', '6', '3', '3', '6', '9', '9', '9', '1', '2', '4', '5', '2', '6', '2', '1', '1', '/', '6', '1', '1', '4', '7', '5', '4', '9', '1', '4', '1', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '3', '5', '0', '4', '2', '8', '3', '3', '0', '4', '2', '0', '8', '7', '6', '6', '0', '9', '/', '1', '5', '2', '8', '6', '8', '8', '7', '2', '8', '5', '3', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0148691_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 402) (SourceJson.white (fragment0148691Field005Chars00 ++ tail)) fragment0148691Acc00500 =
      SourceJson.object (fuel + 401) (SourceJson.white tail) fragment0148691Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0148691_object_field_005"
  err.flush

noncomputable def fragment0148691Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0148691Field006Value00 : SourceJson := .str (String.ofList ['1', '2', '1', '9', '8', '7', '7', '7', '6', '8', '4', '6', '9', '6', '6', '5', '6', '0', '5', '8', '2', '3', '4', '6', '4', '7', '8', '0', '8', '4', '6', '8', '0', '6', '0', '1', '8', '5', '8', '5', '9', '5', '3', '7', '3', '0', '5', '6', '0', '0', '0', '0', '0', '/', '7', '2', '0', '2', '3', '1', '8', '1', '2', '3', '1', '7', '3', '4', '0', '3', '4', '4', '8', '7', '2', '3', '0', '1', '0', '4', '0', '5', '6', '9', '8', '4', '9', '3', '2', '5', '2', '7', '9', '3', '6', '1', '6', '7', '3', '8', '2', '9', '4', '4', '7', '1', '7', '0', '0', '5', '8', '7', '0', '1', '5', '6', '0', '8', '1', '3'])
noncomputable def fragment0148691Acc00700 : List (String × SourceJson) := (fragment0148691Field006Key00, fragment0148691Field006Value00) :: fragment0148691Acc00600
noncomputable def fragment0148691Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '1', '9', '8', '7', '7', '7', '6', '8', '4', '6', '9', '6', '6', '5', '6', '0', '5', '8', '2', '3', '4', '6', '4', '7', '8', '0', '8', '4', '6', '8', '0', '6', '0', '1', '8', '5', '8', '5', '9', '5', '3', '7', '3', '0', '5', '6', '0', '0', '0', '0', '0', '/', '7', '2', '0', '2', '3', '1', '8', '1', '2', '3', '1', '7', '3', '4', '0', '3', '4', '4', '8', '7', '2', '3', '0', '1', '0', '4', '0', '5', '6', '9', '8', '4', '9', '3', '2', '5', '2', '7', '9', '3', '6', '1', '6', '7', '3', '8', '2', '9', '4', '4', '7', '1', '7', '0', '0', '5', '8', '7', '0', '1', '5', '6', '0', '8', '1', '3', '"', ',']

theorem object_fragment0148691_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 401) (SourceJson.white (fragment0148691Field006Chars00 ++ tail)) fragment0148691Acc00600 =
      SourceJson.object (fuel + 400) (SourceJson.white tail) fragment0148691Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0148691_object_field_006"
  err.flush

noncomputable def fragment0148691Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0148691Field007Value00 : SourceJson := .str (String.ofList ['5', '8', '7', '6', '8', '1', '0', '5', '6', '5', '7', '9', '9', '1', '3', '1', '1', '2', '1', '2', '4', '3', '8', '1', '7', '7', '8', '1', '6', '2', '9', '3', '7', '1', '8', '5', '1', '0', '0', '8', '8', '8', '6', '3', '7', '5', '3', '6', '9', '8', '3', '0', '7', '6', '4', '6', '8', '2', '8', '2', '8', '1', '3', '0', '6', '8', '5', '0', '6', '8', '6', '8', '0', '2', '0', '0', '1', '4', '0', '1', '1', '0', '8', '8', '4', '3', '6', '1', '5', '4', '3', '7', '7', '1', '4', '6', '6', '2', '6', '4', '6', '3', '9', '2', '1', '4', '5', '1', '7', '0', '8', '3', '6', '8', '8', '5', '9', '9', '9', '0', '2', '7', '7', '0', '3', '5', '2', '3', '6', '6', '5', '3', '5', '7', '4', '8', '6', '1', '0', '7', '0', '2', '6', '0', '9', '4', '9', '6', '3', '8', '0', '5', '4', '5', '1', '7', '4', '0', '7', '6', '5', '7', '4', '2', '9', '5', '6', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '7', '8', '8', '9', '4', '0', '7', '1', '9', '2', '7', '9', '3', '5', '3', '5', '9', '6', '5', '9', '9', '7', '7', '4', '7', '2', '8', '9', '0', '0', '2', '5', '3', '1', '2', '1', '1', '3', '8', '6', '3', '7', '0', '8', '9', '6', '4', '0', '1', '6', '7', '9', '3', '7', '4', '4', '3', '4', '5', '3', '2', '2', '7', '9', '5', '6', '5', '2', '9', '2', '8', '2', '4', '8', '3', '4', '8', '9', '7', '3', '7', '1', '1', '6', '5', '1', '0', '6', '9', '0', '6', '9', '0', '4', '2', '6', '3', '8', '3', '8', '7', '4', '1', '5', '0', '0', '5', '9', '1', '3', '7', '8', '4', '4', '4', '7', '2', '6', '4', '8', '3', '3', '1', '8', '4', '3', '7', '0', '8', '7', '8', '0', '1', '9', '0', '7', '3', '6', '9', '6', '0', '9', '6', '0', '8', '4', '9', '7', '8', '5', '9', '2', '2', '3', '1', '0', '2', '7', '7', '9', '3', '5', '1', '1', '0', '9', '0', '4', '9', '8', '3', '2', '5', '2', '0', '4', '7', '3', '6', '5', '0', '1', '5', '2', '7', '0', '0', '2', '8', '5', '0', '7', '8', '0', '8', '5', '6', '8', '7', '7', '9', '3', '3'])
noncomputable def fragment0148691Acc00800 : List (String × SourceJson) := (fragment0148691Field007Key00, fragment0148691Field007Value00) :: fragment0148691Acc00700
noncomputable def fragment0148691Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '8', '7', '6', '8', '1', '0', '5', '6', '5', '7', '9', '9', '1', '3', '1', '1', '2', '1', '2', '4', '3', '8', '1', '7', '7', '8', '1', '6', '2', '9', '3', '7', '1', '8', '5', '1', '0', '0', '8', '8', '8', '6', '3', '7', '5', '3', '6', '9', '8', '3', '0', '7', '6', '4', '6', '8', '2', '8', '2', '8', '1', '3', '0', '6', '8', '5', '0', '6', '8', '6', '8', '0', '2', '0', '0', '1', '4', '0', '1', '1', '0', '8', '8', '4', '3', '6', '1', '5', '4', '3', '7', '7', '1', '4', '6', '6', '2', '6', '4', '6', '3', '9', '2', '1', '4', '5', '1', '7', '0', '8', '3', '6', '8', '8', '5', '9', '9', '9', '0', '2', '7', '7', '0', '3', '5', '2', '3', '6', '6', '5', '3', '5', '7', '4', '8', '6', '1', '0', '7', '0', '2', '6', '0', '9', '4', '9', '6', '3', '8', '0', '5', '4', '5', '1', '7', '4', '0', '7', '6', '5', '7', '4', '2', '9', '5', '6', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '7', '8', '8', '9', '4', '0', '7', '1', '9', '2', '7', '9', '3', '5', '3', '5', '9', '6', '5', '9', '9', '7', '7', '4', '7', '2', '8', '9', '0', '0', '2', '5', '3', '1', '2', '1', '1', '3', '8', '6', '3', '7', '0', '8', '9', '6', '4', '0', '1', '6', '7', '9', '3', '7', '4', '4', '3', '4', '5', '3', '2', '2', '7', '9', '5', '6', '5', '2', '9', '2', '8', '2', '4', '8', '3', '4', '8', '9', '7', '3', '7', '1', '1', '6', '5', '1', '0', '6', '9', '0', '6', '9', '0', '4', '2', '6', '3', '8', '3', '8', '7', '4', '1', '5', '0', '0', '5', '9', '1', '3', '7', '8', '4', '4', '4', '7', '2', '6', '4', '8', '3', '3', '1', '8', '4', '3', '7', '0', '8', '7', '8', '0', '1', '9', '0', '7', '3', '6', '9', '6', '0', '9', '6', '0', '8', '4', '9', '7', '8', '5', '9', '2', '2', '3', '1', '0', '2', '7', '7', '9', '3', '5', '1', '1', '0', '9', '0', '4', '9', '8', '3', '2', '5', '2', '0', '4', '7', '3', '6', '5', '0', '1', '5', '2', '7', '0', '0', '2', '8', '5', '0', '7', '8', '0', '8', '5', '6', '8', '7', '7', '9', '3', '3', '"', ',']

theorem object_fragment0148691_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0148691Field007Chars00 ++ tail)) fragment0148691Acc00700 =
      SourceJson.object (fuel + 399) (SourceJson.white tail) fragment0148691Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0148691_object_field_007"
  err.flush

noncomputable def fragment0148691Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0148691Field008Value00 : SourceJson := .str (String.ofList ['1', '3', '4', '1', '9', '1', '0', '6', '5', '2', '0', '2', '8', '6', '3', '5'])
noncomputable def fragment0148691Acc00900 : List (String × SourceJson) := (fragment0148691Field008Key00, fragment0148691Field008Value00) :: fragment0148691Acc00800
noncomputable def fragment0148691Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '4', '1', '9', '1', '0', '6', '5', '2', '0', '2', '8', '6', '3', '5', '"', ',']

theorem object_fragment0148691_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 399) (SourceJson.white (fragment0148691Field008Chars00 ++ tail)) fragment0148691Acc00800 =
      SourceJson.object (fuel + 398) (SourceJson.white tail) fragment0148691Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0148691_object_field_008"
  err.flush

noncomputable def fragment0148691Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0148691Field009Value00 : SourceJson := .str (String.ofList ['3', '9', '4', '9', '5', '3', '9', '7', '7', '3', '4', '1', '8', '6', '0', '3'])
noncomputable def fragment0148691Acc01000 : List (String × SourceJson) := (fragment0148691Field009Key00, fragment0148691Field009Value00) :: fragment0148691Acc00900
noncomputable def fragment0148691Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '9', '4', '9', '5', '3', '9', '7', '7', '3', '4', '1', '8', '6', '0', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0148691_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 398) (SourceJson.white (fragment0148691Field009Chars00 ++ tail)) fragment0148691Acc00900 =
      .ok (.obj (fragment0148691Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0148691_object_field_009"
  err.flush

noncomputable def fragment0148691Chars : List Char := '{' :: (fragment0148691Field000Chars00 ++ fragment0148691Field001Chars00 ++ fragment0148691Field002Chars00 ++ fragment0148691Field003Chars00 ++ fragment0148691Field004Chars00 ++ fragment0148691Field005Chars00 ++ fragment0148691Field006Chars00 ++ fragment0148691Field007Chars00 ++ fragment0148691Field008Chars00 ++ fragment0148691Field009Chars00)
noncomputable def fragment0148691Value : SourceJson := .obj (fragment0148691Acc01000.reverse)

theorem value_fragment0148691 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 408) (fragment0148691Chars ++ tail) =
      .ok (fragment0148691Value, tail) := by
  have hinput : fragment0148691Chars ++ tail = '{' :: (fragment0148691Field000Chars00 ++ (fragment0148691Field001Chars00 ++ (fragment0148691Field002Chars00 ++ (fragment0148691Field003Chars00 ++ (fragment0148691Field004Chars00 ++ (fragment0148691Field005Chars00 ++ (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0148691Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 408) (fragment0148691Chars ++ tail) =
        SourceJson.value (fuel + 408) ('{' :: (fragment0148691Field000Chars00 ++ (fragment0148691Field001Chars00 ++ (fragment0148691Field002Chars00 ++ (fragment0148691Field003Chars00 ++ (fragment0148691Field004Chars00 ++ (fragment0148691Field005Chars00 ++ (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 408)) hinput
    _ = SourceJson.object (fuel + 407) (SourceJson.white (fragment0148691Field000Chars00 ++ (fragment0148691Field001Chars00 ++ (fragment0148691Field002Chars00 ++ (fragment0148691Field003Chars00 ++ (fragment0148691Field004Chars00 ++ (fragment0148691Field005Chars00 ++ (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail)))))))))))) fragment0148691Acc00000 := by rfl
    _ = SourceJson.object (fuel + 406) (SourceJson.white (fragment0148691Field001Chars00 ++ (fragment0148691Field002Chars00 ++ (fragment0148691Field003Chars00 ++ (fragment0148691Field004Chars00 ++ (fragment0148691Field005Chars00 ++ (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail))))))))))) fragment0148691Acc00100 := object_fragment0148691_field_000 fuel (fragment0148691Field001Chars00 ++ (fragment0148691Field002Chars00 ++ (fragment0148691Field003Chars00 ++ (fragment0148691Field004Chars00 ++ (fragment0148691Field005Chars00 ++ (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 405) (SourceJson.white (fragment0148691Field002Chars00 ++ (fragment0148691Field003Chars00 ++ (fragment0148691Field004Chars00 ++ (fragment0148691Field005Chars00 ++ (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail)))))))))) fragment0148691Acc00200 := object_fragment0148691_field_001 fuel (fragment0148691Field002Chars00 ++ (fragment0148691Field003Chars00 ++ (fragment0148691Field004Chars00 ++ (fragment0148691Field005Chars00 ++ (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 404) (SourceJson.white (fragment0148691Field003Chars00 ++ (fragment0148691Field004Chars00 ++ (fragment0148691Field005Chars00 ++ (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail))))))))) fragment0148691Acc00300 := object_fragment0148691_field_002 fuel (fragment0148691Field003Chars00 ++ (fragment0148691Field004Chars00 ++ (fragment0148691Field005Chars00 ++ (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 403) (SourceJson.white (fragment0148691Field004Chars00 ++ (fragment0148691Field005Chars00 ++ (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail)))))))) fragment0148691Acc00400 := object_fragment0148691_field_003 fuel (fragment0148691Field004Chars00 ++ (fragment0148691Field005Chars00 ++ (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 402) (SourceJson.white (fragment0148691Field005Chars00 ++ (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail))))))) fragment0148691Acc00500 := object_fragment0148691_field_004 fuel (fragment0148691Field005Chars00 ++ (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 401) (SourceJson.white (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail)))))) fragment0148691Acc00600 := object_fragment0148691_field_005 fuel (fragment0148691Field006Chars00 ++ (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail))))) fragment0148691Acc00700 := object_fragment0148691_field_006 fuel (fragment0148691Field007Chars00 ++ (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 399) (SourceJson.white (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail)))) fragment0148691Acc00800 := object_fragment0148691_field_007 fuel (fragment0148691Field008Chars00 ++ (fragment0148691Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 398) (SourceJson.white (fragment0148691Field009Chars00 ++ (tail))) fragment0148691Acc00900 := object_fragment0148691_field_008 fuel (fragment0148691Field009Chars00 ++ (tail))
    _ = .ok (fragment0148691Value, tail) := object_fragment0148691_field_009 fuel (tail)

noncomputable def fragment0150642Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0150642Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0150642Field000Value00 : SourceJson := .number (String.ofList ['2', '7'])
noncomputable def fragment0150642Acc00100 : List (String × SourceJson) := (fragment0150642Field000Key00, fragment0150642Field000Value00) :: fragment0150642Acc00000
noncomputable def fragment0150642Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '7', ',']

theorem object_fragment0150642_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0150642Field000Chars00 ++ tail)) fragment0150642Acc00000 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0150642Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0150642_object_field_000"
  err.flush

noncomputable def fragment0150642Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0150642Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '6']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0150642Acc00200 : List (String × SourceJson) := (fragment0150642Field001Key00, fragment0150642Field001Value00) :: fragment0150642Acc00100
noncomputable def fragment0150642Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0150642_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0150642Field001Chars00 ++ tail)) fragment0150642Acc00100 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0150642Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0150642_object_field_001"
  err.flush

noncomputable def fragment0150642Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0150642Field002Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '1', '8', '2', '5', '9', '0', '3', '3', '8', '4', '5', '3', '4', '2', '8', '9', '7', '5', '5', '7', '6', '8', '6', '1', '7', '3', '/', '5', '4', '0', '7', '3', '5', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0150642Acc00300 : List (String × SourceJson) := (fragment0150642Field002Key00, fragment0150642Field002Value00) :: fragment0150642Acc00200
noncomputable def fragment0150642Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '2', '8', '0', '1', '8', '2', '5', '9', '0', '3', '3', '8', '4', '5', '3', '4', '2', '8', '9', '7', '5', '5', '7', '6', '8', '6', '1', '7', '3', '/', '5', '4', '0', '7', '3', '5', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0150642_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0150642Field002Chars00 ++ tail)) fragment0150642Acc00200 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0150642Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0150642_object_field_002"
  err.flush

noncomputable def fragment0150642Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0150642Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0150642Acc00400 : List (String × SourceJson) := (fragment0150642Field003Key00, fragment0150642Field003Value00) :: fragment0150642Acc00300
noncomputable def fragment0150642Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0150642_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0150642Field003Chars00 ++ tail)) fragment0150642Acc00300 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0150642Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0150642_object_field_003"
  err.flush

noncomputable def fragment0150642Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0150642Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0150642Acc00500 : List (String × SourceJson) := (fragment0150642Field004Key00, fragment0150642Field004Value00) :: fragment0150642Acc00400
noncomputable def fragment0150642Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0150642_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0150642Field004Chars00 ++ tail)) fragment0150642Acc00400 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0150642Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0150642_object_field_004"
  err.flush

noncomputable def fragment0150642Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0150642Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '7', '2', '9', '0', '9', '3', '0', '0', '4', '5', '6', '8', '1', '/', '1', '9', '9', '3', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '4', '1', '3', '9', '5', '4', '1', '1', '8', '7', '/', '2', '4', '9', '2', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '3', '3', '0', '6', '9', '3', '6', '6', '9', '1', '/', '3', '9', '8', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '3', '3', '5', '0', '2', '2', '1', '1', '5', '6', '7', '/', '4', '9', '8', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '8', '2', '1', '6', '2', '1', '2', '1', '8', '1', '3', '/', '4', '9', '8', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '2', '8', '3', '0', '5', '8', '4', '3', '9', '/', '1', '9', '9', '3', '8', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '3', '9', '8', '7', '5', '0', '0', '1', '8', '6', '9', '/', '9', '9', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '2', '8', '4', '3', '5', '6', '1', '5', '7', '0', '7', '/', '3', '3', '2', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '3', '5', '7', '2', '9', '5', '9', '0', '4', '9', '/', '1', '1', '0', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '7', '3', '3', '7', '8', '8', '8', '3', '6', '3', '/', '8', '3', '0', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0150642Acc00600 : List (String × SourceJson) := (fragment0150642Field005Key00, fragment0150642Field005Value00) :: fragment0150642Acc00500
noncomputable def fragment0150642Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '9', '0', '9', '3', '0', '0', '4', '5', '6', '8', '1', '/', '1', '9', '9', '3', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '4', '1', '3', '9', '5', '4', '1', '1', '8', '7', '/', '2', '4', '9', '2', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '3', '3', '0', '6', '9', '3', '6', '6', '9', '1', '/', '3', '9', '8', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '3', '3', '5', '0', '2', '2', '1', '1', '5', '6', '7', '/', '4', '9', '8', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '8', '2', '1', '6', '2', '1', '2', '1', '8', '1', '3', '/', '4', '9', '8', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '2', '8', '3', '0', '5', '8', '4', '3', '9', '/', '1', '9', '9', '3', '8', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '3', '9', '8', '7', '5', '0', '0', '1', '8', '6', '9', '/', '9', '9', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '8', '4', '3', '5', '6', '1', '5', '7', '0', '7', '/', '3', '3', '2', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '3', '5', '7', '2', '9', '5', '9', '0', '4', '9', '/', '1', '1', '0', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '7', '3', '3', '7', '8', '8', '8', '3', '6', '3', '/', '8', '3', '0', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0150642_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0150642Field005Chars00 ++ tail)) fragment0150642Acc00500 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0150642Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0150642_object_field_005"
  err.flush

noncomputable def fragment0150642Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0150642Field006Value00 : SourceJson := .str (String.ofList ['1', '0', '5', '0', '2', '4', '5', '8', '2', '5', '9', '6', '0', '8', '5', '5', '1', '9', '7', '7', '2', '0', '6', '6', '4', '3', '0', '9', '7', '5', '4', '6', '0', '1', '0', '3', '8', '2', '0', '4', '1', '0', '8', '8', '0', '0', '0', '0', '/', '2', '7', '9', '6', '0', '3', '5', '2', '3', '0', '7', '0', '9', '4', '1', '9', '9', '7', '8', '8', '9', '1', '3', '1', '0', '6', '8', '8', '3', '1', '8', '2', '4', '3', '6', '1', '2', '0', '6', '6', '9', '0', '3', '8', '9', '5', '9', '7', '9', '0', '5', '5', '7', '7', '7', '4', '2', '6', '7', '6', '1', '4', '6', '2', '1'])
noncomputable def fragment0150642Acc00700 : List (String × SourceJson) := (fragment0150642Field006Key00, fragment0150642Field006Value00) :: fragment0150642Acc00600
noncomputable def fragment0150642Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '5', '0', '2', '4', '5', '8', '2', '5', '9', '6', '0', '8', '5', '5', '1', '9', '7', '7', '2', '0', '6', '6', '4', '3', '0', '9', '7', '5', '4', '6', '0', '1', '0', '3', '8', '2', '0', '4', '1', '0', '8', '8', '0', '0', '0', '0', '/', '2', '7', '9', '6', '0', '3', '5', '2', '3', '0', '7', '0', '9', '4', '1', '9', '9', '7', '8', '8', '9', '1', '3', '1', '0', '6', '8', '8', '3', '1', '8', '2', '4', '3', '6', '1', '2', '0', '6', '6', '9', '0', '3', '8', '9', '5', '9', '7', '9', '0', '5', '5', '7', '7', '7', '4', '2', '6', '7', '6', '1', '4', '6', '2', '1', '"', ',']

theorem object_fragment0150642_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0150642Field006Chars00 ++ tail)) fragment0150642Acc00600 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0150642Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0150642_object_field_006"
  err.flush

noncomputable def fragment0150642Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0150642Field007Value00 : SourceJson := .str (String.ofList ['1', '8', '7', '9', '4', '7', '5', '8', '5', '1', '5', '5', '0', '6', '1', '5', '3', '0', '2', '9', '3', '4', '8', '2', '9', '7', '9', '1', '4', '0', '5', '4', '3', '2', '8', '5', '3', '3', '4', '4', '8', '4', '4', '5', '1', '1', '8', '8', '5', '7', '0', '5', '4', '1', '3', '2', '3', '1', '4', '8', '0', '2', '7', '4', '4', '3', '0', '8', '6', '4', '1', '9', '9', '6', '3', '8', '5', '4', '9', '7', '9', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '7', '1', '3', '3', '7', '8', '4', '9', '0', '4', '4', '9', '3', '9', '4', '3', '9', '2', '4', '4', '8', '0', '6', '7', '1', '8', '5', '3', '4', '7', '2', '3', '2', '6', '5', '7', '7', '5', '9', '1', '9', '9', '7', '5', '3', '4', '7', '2', '3', '1', '2', '6', '4', '7', '0', '9', '8', '2', '1', '3', '3', '8', '3', '0', '9', '6', '0', '1', '0', '0', '1', '0', '5', '4', '3', '1', '4', '8', '9', '2', '6', '7', '9', '8', '2', '6', '8', '5', '6', '2', '9', '7', '5', '8', '8', '0', '8', '8', '8', '6', '5', '7', '4', '1', '3', '3', '2', '3', '0', '4', '9', '5', '6', '1', '8', '1', '0', '4', '3'])
noncomputable def fragment0150642Acc00800 : List (String × SourceJson) := (fragment0150642Field007Key00, fragment0150642Field007Value00) :: fragment0150642Acc00700
noncomputable def fragment0150642Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '7', '9', '4', '7', '5', '8', '5', '1', '5', '5', '0', '6', '1', '5', '3', '0', '2', '9', '3', '4', '8', '2', '9', '7', '9', '1', '4', '0', '5', '4', '3', '2', '8', '5', '3', '3', '4', '4', '8', '4', '4', '5', '1', '1', '8', '8', '5', '7', '0', '5', '4', '1', '3', '2', '3', '1', '4', '8', '0', '2', '7', '4', '4', '3', '0', '8', '6', '4', '1', '9', '9', '6', '3', '8', '5', '4', '9', '7', '9', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '7', '1', '3', '3', '7', '8', '4', '9', '0', '4', '4', '9', '3', '9', '4', '3', '9', '2', '4', '4', '8', '0', '6', '7', '1', '8', '5', '3', '4', '7', '2', '3', '2', '6', '5', '7', '7', '5', '9', '1', '9', '9', '7', '5', '3', '4', '7', '2', '3', '1', '2', '6', '4', '7', '0', '9', '8', '2', '1', '3', '3', '8', '3', '0', '9', '6', '0', '1', '0', '0', '1', '0', '5', '4', '3', '1', '4', '8', '9', '2', '6', '7', '9', '8', '2', '6', '8', '5', '6', '2', '9', '7', '5', '8', '8', '0', '8', '8', '8', '6', '5', '7', '4', '1', '3', '3', '2', '3', '0', '4', '9', '5', '6', '1', '8', '1', '0', '4', '3', '"', ',']

theorem object_fragment0150642_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0150642Field007Chars00 ++ tail)) fragment0150642Acc00700 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0150642Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0150642_object_field_007"
  err.flush

noncomputable def fragment0150642Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0150642Field008Value00 : SourceJson := .str (String.ofList ['2', '9', '7', '5', '9', '6', '5', '6', '1', '2', '4', '9'])
noncomputable def fragment0150642Acc00900 : List (String × SourceJson) := (fragment0150642Field008Key00, fragment0150642Field008Value00) :: fragment0150642Acc00800
noncomputable def fragment0150642Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '9', '7', '5', '9', '6', '5', '6', '1', '2', '4', '9', '"', ',']

theorem object_fragment0150642_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0150642Field008Chars00 ++ tail)) fragment0150642Acc00800 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0150642Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0150642_object_field_008"
  err.flush

noncomputable def fragment0150642Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0150642Field009Value00 : SourceJson := .str (String.ofList ['8', '9', '0', '9', '4', '7', '4', '4', '2', '4', '5', '3'])
noncomputable def fragment0150642Acc01000 : List (String × SourceJson) := (fragment0150642Field009Key00, fragment0150642Field009Value00) :: fragment0150642Acc00900
noncomputable def fragment0150642Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '9', '0', '9', '4', '7', '4', '4', '2', '4', '5', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0150642_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0150642Field009Chars00 ++ tail)) fragment0150642Acc00900 =
      .ok (.obj (fragment0150642Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0150642_object_field_009"
  err.flush

noncomputable def fragment0150642Chars : List Char := '{' :: (fragment0150642Field000Chars00 ++ fragment0150642Field001Chars00 ++ fragment0150642Field002Chars00 ++ fragment0150642Field003Chars00 ++ fragment0150642Field004Chars00 ++ fragment0150642Field005Chars00 ++ fragment0150642Field006Chars00 ++ fragment0150642Field007Chars00 ++ fragment0150642Field008Chars00 ++ fragment0150642Field009Chars00)
noncomputable def fragment0150642Value : SourceJson := .obj (fragment0150642Acc01000.reverse)

theorem value_fragment0150642 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 237) (fragment0150642Chars ++ tail) =
      .ok (fragment0150642Value, tail) := by
  have hinput : fragment0150642Chars ++ tail = '{' :: (fragment0150642Field000Chars00 ++ (fragment0150642Field001Chars00 ++ (fragment0150642Field002Chars00 ++ (fragment0150642Field003Chars00 ++ (fragment0150642Field004Chars00 ++ (fragment0150642Field005Chars00 ++ (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0150642Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 237) (fragment0150642Chars ++ tail) =
        SourceJson.value (fuel + 237) ('{' :: (fragment0150642Field000Chars00 ++ (fragment0150642Field001Chars00 ++ (fragment0150642Field002Chars00 ++ (fragment0150642Field003Chars00 ++ (fragment0150642Field004Chars00 ++ (fragment0150642Field005Chars00 ++ (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 237)) hinput
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0150642Field000Chars00 ++ (fragment0150642Field001Chars00 ++ (fragment0150642Field002Chars00 ++ (fragment0150642Field003Chars00 ++ (fragment0150642Field004Chars00 ++ (fragment0150642Field005Chars00 ++ (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail)))))))))))) fragment0150642Acc00000 := by rfl
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0150642Field001Chars00 ++ (fragment0150642Field002Chars00 ++ (fragment0150642Field003Chars00 ++ (fragment0150642Field004Chars00 ++ (fragment0150642Field005Chars00 ++ (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail))))))))))) fragment0150642Acc00100 := object_fragment0150642_field_000 fuel (fragment0150642Field001Chars00 ++ (fragment0150642Field002Chars00 ++ (fragment0150642Field003Chars00 ++ (fragment0150642Field004Chars00 ++ (fragment0150642Field005Chars00 ++ (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0150642Field002Chars00 ++ (fragment0150642Field003Chars00 ++ (fragment0150642Field004Chars00 ++ (fragment0150642Field005Chars00 ++ (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail)))))))))) fragment0150642Acc00200 := object_fragment0150642_field_001 fuel (fragment0150642Field002Chars00 ++ (fragment0150642Field003Chars00 ++ (fragment0150642Field004Chars00 ++ (fragment0150642Field005Chars00 ++ (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0150642Field003Chars00 ++ (fragment0150642Field004Chars00 ++ (fragment0150642Field005Chars00 ++ (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail))))))))) fragment0150642Acc00300 := object_fragment0150642_field_002 fuel (fragment0150642Field003Chars00 ++ (fragment0150642Field004Chars00 ++ (fragment0150642Field005Chars00 ++ (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0150642Field004Chars00 ++ (fragment0150642Field005Chars00 ++ (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail)))))))) fragment0150642Acc00400 := object_fragment0150642_field_003 fuel (fragment0150642Field004Chars00 ++ (fragment0150642Field005Chars00 ++ (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0150642Field005Chars00 ++ (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail))))))) fragment0150642Acc00500 := object_fragment0150642_field_004 fuel (fragment0150642Field005Chars00 ++ (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail)))))) fragment0150642Acc00600 := object_fragment0150642_field_005 fuel (fragment0150642Field006Chars00 ++ (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail))))) fragment0150642Acc00700 := object_fragment0150642_field_006 fuel (fragment0150642Field007Chars00 ++ (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail)))) fragment0150642Acc00800 := object_fragment0150642_field_007 fuel (fragment0150642Field008Chars00 ++ (fragment0150642Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0150642Field009Chars00 ++ (tail))) fragment0150642Acc00900 := object_fragment0150642_field_008 fuel (fragment0150642Field009Chars00 ++ (tail))
    _ = .ok (fragment0150642Value, tail) := object_fragment0150642_field_009 fuel (tail)

noncomputable def fragment0152230Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0152230Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0152230Field000Value00 : SourceJson := .number (String.ofList ['2', '8'])
noncomputable def fragment0152230Acc00100 : List (String × SourceJson) := (fragment0152230Field000Key00, fragment0152230Field000Value00) :: fragment0152230Acc00000
noncomputable def fragment0152230Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '8', ',']

theorem object_fragment0152230_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0152230Field000Chars00 ++ tail)) fragment0152230Acc00000 =
      SourceJson.object (fuel + 399) (SourceJson.white tail) fragment0152230Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0152230_object_field_000"
  err.flush

noncomputable def fragment0152230Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0152230Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['4'])]
noncomputable def fragment0152230Acc00200 : List (String × SourceJson) := (fragment0152230Field001Key00, fragment0152230Field001Value00) :: fragment0152230Acc00100
noncomputable def fragment0152230Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0152230_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 399) (SourceJson.white (fragment0152230Field001Chars00 ++ tail)) fragment0152230Acc00100 =
      SourceJson.object (fuel + 398) (SourceJson.white tail) fragment0152230Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0152230_object_field_001"
  err.flush

noncomputable def fragment0152230Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0152230Field002Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '8', '5', '9', '8', '0', '5', '8', '2', '2', '4', '9', '8', '4', '5', '6', '7', '9', '9', '4', '5', '4', '5', '8', '3', '1', '0', '8', '1', '/', '4', '3', '0', '8', '9', '8', '8', '0', '0', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0152230Acc00300 : List (String × SourceJson) := (fragment0152230Field002Key00, fragment0152230Field002Value00) :: fragment0152230Acc00200
noncomputable def fragment0152230Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '4', '5', '8', '5', '9', '8', '0', '5', '8', '2', '2', '4', '9', '8', '4', '5', '6', '7', '9', '9', '4', '5', '4', '5', '8', '3', '1', '0', '8', '1', '/', '4', '3', '0', '8', '9', '8', '8', '0', '0', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0152230_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 398) (SourceJson.white (fragment0152230Field002Chars00 ++ tail)) fragment0152230Acc00200 =
      SourceJson.object (fuel + 397) (SourceJson.white tail) fragment0152230Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0152230_object_field_002"
  err.flush

noncomputable def fragment0152230Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0152230Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '8', '7', '1', '0', '3', '7', '/', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0152230Acc00400 : List (String × SourceJson) := (fragment0152230Field003Key00, fragment0152230Field003Value00) :: fragment0152230Acc00300
noncomputable def fragment0152230Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '8', '7', '1', '0', '3', '7', '/', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0152230_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 397) (SourceJson.white (fragment0152230Field003Chars00 ++ tail)) fragment0152230Acc00300 =
      SourceJson.object (fuel + 396) (SourceJson.white tail) fragment0152230Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0152230_object_field_003"
  err.flush

noncomputable def fragment0152230Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0152230Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0152230Acc00500 : List (String × SourceJson) := (fragment0152230Field004Key00, fragment0152230Field004Value00) :: fragment0152230Acc00400
noncomputable def fragment0152230Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '5', '9', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0152230_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 396) (SourceJson.white (fragment0152230Field004Chars00 ++ tail)) fragment0152230Acc00400 =
      SourceJson.object (fuel + 395) (SourceJson.white tail) fragment0152230Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0152230_object_field_004"
  err.flush

noncomputable def fragment0152230Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0152230Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '1', '4', '8', '8', '9', '0', '7', '2', '2', '4', '9', '7', '8', '4', '6', '6', '6', '0', '1', '3', '9', '/', '2', '5', '1', '1', '6', '7', '0', '3', '0', '5', '8', '3', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '0', '8', '6', '0', '7', '7', '5', '8', '2', '4', '0', '8', '4', '0', '0', '8', '6', '9', '1', '/', '3', '1', '3', '9', '5', '8', '7', '8', '8', '2', '2', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '7', '0', '7', '8', '4', '9', '8', '0', '2', '8', '2', '5', '4', '5', '7', '2', '1', '6', '0', '1', '/', '1', '2', '5', '5', '8', '3', '5', '1', '5', '2', '9', '1', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '0', '9', '4', '7', '0', '1', '6', '8', '7', '3', '7', '1', '1', '7', '0', '9', '0', '2', '6', '1', '/', '6', '2', '7', '9', '1', '7', '5', '7', '6', '4', '5', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '6', '9', '9', '0', '2', '6', '2', '7', '7', '5', '7', '3', '7', '6', '1', '0', '1', '6', '7', '/', '6', '2', '7', '9', '1', '7', '5', '7', '6', '4', '5', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '6', '1', '2', '6', '0', '6', '3', '6', '6', '9', '6', '0', '5', '3', '6', '0', '7', '8', '9', '/', '1', '2', '5', '5', '8', '3', '5', '1', '5', '2', '9', '1', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '2', '7', '7', '0', '1', '8', '9', '9', '0', '9', '3', '0', '5', '6', '8', '2', '0', '7', '/', '7', '3', '8', '7', '2', '6', '5', '6', '0', '5', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '7', '8', '1', '1', '3', '4', '5', '7', '4', '0', '5', '6', '8', '5', '8', '4', '1', '7', '/', '4', '1', '8', '6', '1', '1', '7', '1', '7', '6', '3', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '2', '8', '9', '5', '8', '7', '2', '1', '5', '0', '2', '7', '3', '6', '2', '0', '9', '7', '/', '4', '1', '8', '6', '1', '1', '7', '1', '7', '6', '3', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '8', '2', '2', '1', '0', '3', '6', '3', '3', '8', '4', '9', '6', '0', '6', '9', '3', '9', '/', '1', '0', '4', '6', '5', '2', '9', '2', '9', '4', '0', '9', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0152230Acc00600 : List (String × SourceJson) := (fragment0152230Field005Key00, fragment0152230Field005Value00) :: fragment0152230Acc00500
noncomputable def fragment0152230Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '4', '8', '8', '9', '0', '7', '2', '2', '4', '9', '7', '8', '4', '6', '6', '6', '0', '1', '3', '9', '/', '2', '5', '1', '1', '6', '7', '0', '3', '0', '5', '8', '3', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '0', '8', '6', '0', '7', '7', '5', '8', '2', '4', '0', '8', '4', '0', '0', '8', '6', '9', '1', '/', '3', '1', '3', '9', '5', '8', '7', '8', '8', '2', '2', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '7', '0', '7', '8', '4', '9', '8', '0', '2', '8', '2', '5', '4', '5', '7', '2', '1', '6', '0', '1', '/', '1', '2', '5', '5', '8', '3', '5', '1', '5', '2', '9', '1', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '9', '4', '7', '0', '1', '6', '8', '7', '3', '7', '1', '1', '7', '0', '9', '0', '2', '6', '1', '/', '6', '2', '7', '9', '1', '7', '5', '7', '6', '4', '5', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '6', '9', '9', '0', '2', '6', '2', '7', '7', '5', '7', '3', '7', '6', '1', '0', '1', '6', '7', '/', '6', '2', '7', '9', '1', '7', '5', '7', '6', '4', '5', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '6', '1', '2', '6', '0', '6', '3', '6', '6', '9', '6', '0', '5', '3', '6', '0', '7', '8', '9', '/', '1', '2', '5', '5', '8', '3', '5', '1', '5', '2', '9', '1', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '7', '7', '0', '1', '8', '9', '9', '0', '9', '3', '0', '5', '6', '8', '2', '0', '7', '/', '7', '3', '8', '7', '2', '6', '5', '6', '0', '5', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '7', '8', '1', '1', '3', '4', '5', '7', '4', '0', '5', '6', '8', '5', '8', '4', '1', '7', '/', '4', '1', '8', '6', '1', '1', '7', '1', '7', '6', '3', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '2', '8', '9', '5', '8', '7', '2', '1', '5', '0', '2', '7', '3', '6', '2', '0', '9', '7', '/', '4', '1', '8', '6', '1', '1', '7', '1', '7', '6', '3', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '8', '2', '2', '1', '0', '3', '6', '3', '3', '8', '4', '9', '6', '0', '6', '9', '3', '9', '/', '1', '0', '4', '6', '5', '2', '9', '2', '9', '4', '0', '9', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0152230_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 395) (SourceJson.white (fragment0152230Field005Chars00 ++ tail)) fragment0152230Acc00500 =
      SourceJson.object (fuel + 394) (SourceJson.white tail) fragment0152230Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0152230_object_field_005"
  err.flush

noncomputable def fragment0152230Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0152230Field006Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '0', '3', '6', '2', '9', '0', '2', '3', '3', '5', '8', '1', '3', '4', '2', '7', '4', '8', '3', '5', '4', '6', '7', '0', '2', '7', '6', '0', '8', '6', '0', '9', '2', '6', '3', '0', '0', '6', '8', '9', '2', '6', '8', '7', '3', '6', '0', '0', '/', '2', '1', '3', '5', '0', '3', '4', '7', '8', '7', '0', '9', '1', '4', '2', '7', '0', '3', '8', '7', '2', '4', '3', '0', '5', '7', '8', '0', '9', '3', '5', '0', '4', '5', '7', '3', '1', '4', '4', '9', '2', '6', '3', '4', '1', '3', '5', '1', '7', '9', '6', '4', '4', '1', '9', '2', '4', '7', '4', '8', '9', '7', '6', '1', '5', '3', '3', '9'])
noncomputable def fragment0152230Acc00700 : List (String × SourceJson) := (fragment0152230Field006Key00, fragment0152230Field006Value00) :: fragment0152230Acc00600
noncomputable def fragment0152230Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '8', '0', '3', '6', '2', '9', '0', '2', '3', '3', '5', '8', '1', '3', '4', '2', '7', '4', '8', '3', '5', '4', '6', '7', '0', '2', '7', '6', '0', '8', '6', '0', '9', '2', '6', '3', '0', '0', '6', '8', '9', '2', '6', '8', '7', '3', '6', '0', '0', '/', '2', '1', '3', '5', '0', '3', '4', '7', '8', '7', '0', '9', '1', '4', '2', '7', '0', '3', '8', '7', '2', '4', '3', '0', '5', '7', '8', '0', '9', '3', '5', '0', '4', '5', '7', '3', '1', '4', '4', '9', '2', '6', '3', '4', '1', '3', '5', '1', '7', '9', '6', '4', '4', '1', '9', '2', '4', '7', '4', '8', '9', '7', '6', '1', '5', '3', '3', '9', '"', ',']

theorem object_fragment0152230_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 394) (SourceJson.white (fragment0152230Field006Chars00 ++ tail)) fragment0152230Acc00600 =
      SourceJson.object (fuel + 393) (SourceJson.white tail) fragment0152230Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0152230_object_field_006"
  err.flush

noncomputable def fragment0152230Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0152230Field007Value00 : SourceJson := .str (String.ofList ['6', '8', '0', '6', '7', '4', '5', '5', '1', '6', '0', '4', '0', '5', '7', '5', '6', '6', '9', '0', '8', '7', '5', '5', '1', '3', '3', '9', '6', '3', '1', '4', '0', '7', '2', '3', '9', '7', '8', '1', '7', '7', '2', '5', '0', '3', '8', '0', '6', '8', '2', '4', '9', '6', '7', '9', '8', '6', '4', '4', '5', '1', '0', '8', '9', '1', '0', '2', '1', '1', '4', '5', '2', '3', '2', '7', '1', '1', '8', '1', '5', '4', '2', '5', '1', '3', '4', '7', '0', '2', '4', '4', '8', '7', '1', '2', '1', '7', '0', '8', '9', '9', '2', '2', '7', '7', '3', '7', '8', '8', '5', '4', '1', '8', '7', '5', '6', '4', '2', '2', '2', '4', '0', '0', '2', '9', '1', '5', '7', '1', '6', '0', '6', '8', '2', '4', '0', '4', '5', '8', '4', '5', '1', '6', '3', '6', '0', '2', '7', '4', '1', '2', '4', '9', '6', '4', '6', '9', '7', '7', '3', '5', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '4', '5', '9', '1', '3', '0', '8', '7', '0', '1', '2', '2', '6', '9', '3', '7', '5', '5', '6', '4', '6', '2', '1', '2', '9', '8', '0', '5', '1', '4', '8', '2', '2', '9', '0', '5', '4', '0', '6', '5', '4', '6', '7', '0', '3', '4', '5', '1', '4', '5', '6', '4', '2', '9', '5', '0', '5', '3', '5', '9', '5', '3', '7', '8', '7', '8', '6', '4', '5', '4', '5', '1', '7', '2', '3', '4', '4', '6', '9', '5', '9', '2', '8', '4', '4', '4', '4', '5', '6', '3', '5', '9', '6', '2', '0', '7', '9', '4', '3', '7', '7', '9', '2', '8', '9', '1', '3', '4', '0', '7', '2', '7', '0', '3', '1', '0', '0', '7', '8', '4', '9', '4', '9', '3', '5', '5', '7', '8', '8', '4', '2', '0', '4', '1', '1', '4', '5', '4', '7', '4', '7', '7', '2', '5', '8', '1', '2', '6', '7', '7', '3', '0', '8', '5', '4', '3', '9', '8', '8', '2', '3', '9', '1', '3', '8', '6', '1', '7', '4', '6', '5', '3', '7', '2', '6', '3', '1', '0', '1', '7', '8', '1', '7', '0', '7', '3', '2', '9', '4', '0', '8', '7', '3', '3', '4', '7', '6', '1', '3', '6', '7', '7'])
noncomputable def fragment0152230Acc00800 : List (String × SourceJson) := (fragment0152230Field007Key00, fragment0152230Field007Value00) :: fragment0152230Acc00700
noncomputable def fragment0152230Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '8', '0', '6', '7', '4', '5', '5', '1', '6', '0', '4', '0', '5', '7', '5', '6', '6', '9', '0', '8', '7', '5', '5', '1', '3', '3', '9', '6', '3', '1', '4', '0', '7', '2', '3', '9', '7', '8', '1', '7', '7', '2', '5', '0', '3', '8', '0', '6', '8', '2', '4', '9', '6', '7', '9', '8', '6', '4', '4', '5', '1', '0', '8', '9', '1', '0', '2', '1', '1', '4', '5', '2', '3', '2', '7', '1', '1', '8', '1', '5', '4', '2', '5', '1', '3', '4', '7', '0', '2', '4', '4', '8', '7', '1', '2', '1', '7', '0', '8', '9', '9', '2', '2', '7', '7', '3', '7', '8', '8', '5', '4', '1', '8', '7', '5', '6', '4', '2', '2', '2', '4', '0', '0', '2', '9', '1', '5', '7', '1', '6', '0', '6', '8', '2', '4', '0', '4', '5', '8', '4', '5', '1', '6', '3', '6', '0', '2', '7', '4', '1', '2', '4', '9', '6', '4', '6', '9', '7', '7', '3', '5', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '4', '5', '9', '1', '3', '0', '8', '7', '0', '1', '2', '2', '6', '9', '3', '7', '5', '5', '6', '4', '6', '2', '1', '2', '9', '8', '0', '5', '1', '4', '8', '2', '2', '9', '0', '5', '4', '0', '6', '5', '4', '6', '7', '0', '3', '4', '5', '1', '4', '5', '6', '4', '2', '9', '5', '0', '5', '3', '5', '9', '5', '3', '7', '8', '7', '8', '6', '4', '5', '4', '5', '1', '7', '2', '3', '4', '4', '6', '9', '5', '9', '2', '8', '4', '4', '4', '4', '5', '6', '3', '5', '9', '6', '2', '0', '7', '9', '4', '3', '7', '7', '9', '2', '8', '9', '1', '3', '4', '0', '7', '2', '7', '0', '3', '1', '0', '0', '7', '8', '4', '9', '4', '9', '3', '5', '5', '7', '8', '8', '4', '2', '0', '4', '1', '1', '4', '5', '4', '7', '4', '7', '7', '2', '5', '8', '1', '2', '6', '7', '7', '3', '0', '8', '5', '4', '3', '9', '8', '8', '2', '3', '9', '1', '3', '8', '6', '1', '7', '4', '6', '5', '3', '7', '2', '6', '3', '1', '0', '1', '7', '8', '1', '7', '0', '7', '3', '2', '9', '4', '0', '8', '7', '3', '3', '4', '7', '6', '1', '3', '6', '7', '7', '"', ',']

theorem object_fragment0152230_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 393) (SourceJson.white (fragment0152230Field007Chars00 ++ tail)) fragment0152230Acc00700 =
      SourceJson.object (fuel + 392) (SourceJson.white tail) fragment0152230Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0152230_object_field_007"
  err.flush

noncomputable def fragment0152230Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0152230Field008Value00 : SourceJson := .str (String.ofList ['4', '0', '0', '9', '0', '7', '6', '0', '1', '6', '8', '4'])
noncomputable def fragment0152230Acc00900 : List (String × SourceJson) := (fragment0152230Field008Key00, fragment0152230Field008Value00) :: fragment0152230Acc00800
noncomputable def fragment0152230Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '0', '9', '0', '7', '6', '0', '1', '6', '8', '4', '"', ',']

theorem object_fragment0152230_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 392) (SourceJson.white (fragment0152230Field008Chars00 ++ tail)) fragment0152230Acc00800 =
      SourceJson.object (fuel + 391) (SourceJson.white tail) fragment0152230Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0152230_object_field_008"
  err.flush

noncomputable def fragment0152230Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0152230Field009Value00 : SourceJson := .str (String.ofList ['9', '8', '7', '8', '6', '0', '4', '3', '5', '6', '0', '4'])
noncomputable def fragment0152230Acc01000 : List (String × SourceJson) := (fragment0152230Field009Key00, fragment0152230Field009Value00) :: fragment0152230Acc00900
noncomputable def fragment0152230Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '8', '7', '8', '6', '0', '4', '3', '5', '6', '0', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0152230_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 391) (SourceJson.white (fragment0152230Field009Chars00 ++ tail)) fragment0152230Acc00900 =
      .ok (.obj (fragment0152230Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0152230_object_field_009"
  err.flush

noncomputable def fragment0152230Chars : List Char := '{' :: (fragment0152230Field000Chars00 ++ fragment0152230Field001Chars00 ++ fragment0152230Field002Chars00 ++ fragment0152230Field003Chars00 ++ fragment0152230Field004Chars00 ++ fragment0152230Field005Chars00 ++ fragment0152230Field006Chars00 ++ fragment0152230Field007Chars00 ++ fragment0152230Field008Chars00 ++ fragment0152230Field009Chars00)
noncomputable def fragment0152230Value : SourceJson := .obj (fragment0152230Acc01000.reverse)

theorem value_fragment0152230 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 401) (fragment0152230Chars ++ tail) =
      .ok (fragment0152230Value, tail) := by
  have hinput : fragment0152230Chars ++ tail = '{' :: (fragment0152230Field000Chars00 ++ (fragment0152230Field001Chars00 ++ (fragment0152230Field002Chars00 ++ (fragment0152230Field003Chars00 ++ (fragment0152230Field004Chars00 ++ (fragment0152230Field005Chars00 ++ (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0152230Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 401) (fragment0152230Chars ++ tail) =
        SourceJson.value (fuel + 401) ('{' :: (fragment0152230Field000Chars00 ++ (fragment0152230Field001Chars00 ++ (fragment0152230Field002Chars00 ++ (fragment0152230Field003Chars00 ++ (fragment0152230Field004Chars00 ++ (fragment0152230Field005Chars00 ++ (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 401)) hinput
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0152230Field000Chars00 ++ (fragment0152230Field001Chars00 ++ (fragment0152230Field002Chars00 ++ (fragment0152230Field003Chars00 ++ (fragment0152230Field004Chars00 ++ (fragment0152230Field005Chars00 ++ (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail)))))))))))) fragment0152230Acc00000 := by rfl
    _ = SourceJson.object (fuel + 399) (SourceJson.white (fragment0152230Field001Chars00 ++ (fragment0152230Field002Chars00 ++ (fragment0152230Field003Chars00 ++ (fragment0152230Field004Chars00 ++ (fragment0152230Field005Chars00 ++ (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail))))))))))) fragment0152230Acc00100 := object_fragment0152230_field_000 fuel (fragment0152230Field001Chars00 ++ (fragment0152230Field002Chars00 ++ (fragment0152230Field003Chars00 ++ (fragment0152230Field004Chars00 ++ (fragment0152230Field005Chars00 ++ (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 398) (SourceJson.white (fragment0152230Field002Chars00 ++ (fragment0152230Field003Chars00 ++ (fragment0152230Field004Chars00 ++ (fragment0152230Field005Chars00 ++ (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail)))))))))) fragment0152230Acc00200 := object_fragment0152230_field_001 fuel (fragment0152230Field002Chars00 ++ (fragment0152230Field003Chars00 ++ (fragment0152230Field004Chars00 ++ (fragment0152230Field005Chars00 ++ (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 397) (SourceJson.white (fragment0152230Field003Chars00 ++ (fragment0152230Field004Chars00 ++ (fragment0152230Field005Chars00 ++ (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail))))))))) fragment0152230Acc00300 := object_fragment0152230_field_002 fuel (fragment0152230Field003Chars00 ++ (fragment0152230Field004Chars00 ++ (fragment0152230Field005Chars00 ++ (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 396) (SourceJson.white (fragment0152230Field004Chars00 ++ (fragment0152230Field005Chars00 ++ (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail)))))))) fragment0152230Acc00400 := object_fragment0152230_field_003 fuel (fragment0152230Field004Chars00 ++ (fragment0152230Field005Chars00 ++ (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 395) (SourceJson.white (fragment0152230Field005Chars00 ++ (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail))))))) fragment0152230Acc00500 := object_fragment0152230_field_004 fuel (fragment0152230Field005Chars00 ++ (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 394) (SourceJson.white (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail)))))) fragment0152230Acc00600 := object_fragment0152230_field_005 fuel (fragment0152230Field006Chars00 ++ (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 393) (SourceJson.white (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail))))) fragment0152230Acc00700 := object_fragment0152230_field_006 fuel (fragment0152230Field007Chars00 ++ (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 392) (SourceJson.white (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail)))) fragment0152230Acc00800 := object_fragment0152230_field_007 fuel (fragment0152230Field008Chars00 ++ (fragment0152230Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 391) (SourceJson.white (fragment0152230Field009Chars00 ++ (tail))) fragment0152230Acc00900 := object_fragment0152230_field_008 fuel (fragment0152230Field009Chars00 ++ (tail))
    _ = .ok (fragment0152230Value, tail) := object_fragment0152230_field_009 fuel (tail)

noncomputable def fragment0154158Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0154158Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0154158Field000Value00 : SourceJson := .number (String.ofList ['2', '9'])
noncomputable def fragment0154158Acc00100 : List (String × SourceJson) := (fragment0154158Field000Key00, fragment0154158Field000Value00) :: fragment0154158Acc00000
noncomputable def fragment0154158Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '9', ',']

theorem object_fragment0154158_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 408) (SourceJson.white (fragment0154158Field000Chars00 ++ tail)) fragment0154158Acc00000 =
      SourceJson.object (fuel + 407) (SourceJson.white tail) fragment0154158Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0154158_object_field_000"
  err.flush

noncomputable def fragment0154158Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0154158Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['5']), .number (String.ofList ['4'])]
noncomputable def fragment0154158Acc00200 : List (String × SourceJson) := (fragment0154158Field001Key00, fragment0154158Field001Value00) :: fragment0154158Acc00100
noncomputable def fragment0154158Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0154158_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 407) (SourceJson.white (fragment0154158Field001Chars00 ++ tail)) fragment0154158Acc00100 =
      SourceJson.object (fuel + 406) (SourceJson.white tail) fragment0154158Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0154158_object_field_001"
  err.flush

noncomputable def fragment0154158Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0154158Field002Value00 : SourceJson := .str (String.ofList ['1', '2', '2', '5', '7', '5', '9', '6', '3', '0', '9', '9', '2', '0', '5', '4', '7', '2', '5', '9', '1', '5', '6', '7', '4', '7', '7', '6', '7', '0', '6', '9', '6', '4', '4', '7', '7', '/', '1', '4', '3', '4', '0', '3', '1', '2', '0', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0154158Acc00300 : List (String × SourceJson) := (fragment0154158Field002Key00, fragment0154158Field002Value00) :: fragment0154158Acc00200
noncomputable def fragment0154158Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '2', '2', '5', '7', '5', '9', '6', '3', '0', '9', '9', '2', '0', '5', '4', '7', '2', '5', '9', '1', '5', '6', '7', '4', '7', '7', '6', '7', '0', '6', '9', '6', '4', '4', '7', '7', '/', '1', '4', '3', '4', '0', '3', '1', '2', '0', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0154158_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 406) (SourceJson.white (fragment0154158Field002Chars00 ++ tail)) fragment0154158Acc00200 =
      SourceJson.object (fuel + 405) (SourceJson.white tail) fragment0154158Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0154158_object_field_002"
  err.flush

noncomputable def fragment0154158Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0154158Field003Value00 : SourceJson := .str (String.ofList ['2', '2', '1', '0', '8', '2', '6', '9', '/', '2', '8', '2', '8', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0154158Acc00400 : List (String × SourceJson) := (fragment0154158Field003Key00, fragment0154158Field003Value00) :: fragment0154158Acc00300
noncomputable def fragment0154158Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '2', '1', '0', '8', '2', '6', '9', '/', '2', '8', '2', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0154158_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 405) (SourceJson.white (fragment0154158Field003Chars00 ++ tail)) fragment0154158Acc00300 =
      SourceJson.object (fuel + 404) (SourceJson.white tail) fragment0154158Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0154158_object_field_003"
  err.flush

noncomputable def fragment0154158Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0154158Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '9', '8', '4', '4', '0', '3', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '2', '8', '1', '0', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '4', '6', '8', '7', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '8', '1', '1', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0154158Acc00500 : List (String × SourceJson) := (fragment0154158Field004Key00, fragment0154158Field004Value00) :: fragment0154158Acc00400
noncomputable def fragment0154158Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '8', '4', '4', '0', '3', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '8', '1', '0', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '4', '6', '8', '7', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '8', '1', '1', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0154158_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 404) (SourceJson.white (fragment0154158Field004Chars00 ++ tail)) fragment0154158Acc00400 =
      SourceJson.object (fuel + 403) (SourceJson.white tail) fragment0154158Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0154158_object_field_004"
  err.flush

noncomputable def fragment0154158Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0154158Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '0', '4', '4', '4', '9', '7', '4', '9', '7', '9', '5', '9', '3', '8', '2', '9', '9', '4', '6', '2', '9', '/', '4', '6', '3', '8', '8', '9', '4', '9', '5', '7', '1', '7', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '3', '0', '8', '5', '7', '0', '3', '0', '4', '1', '8', '1', '0', '4', '5', '7', '1', '1', '/', '4', '4', '6', '0', '4', '7', '5', '9', '2', '0', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '9', '4', '7', '3', '5', '4', '8', '9', '5', '6', '7', '2', '0', '7', '7', '8', '9', '9', '/', '5', '1', '5', '4', '3', '2', '7', '7', '3', '0', '1', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '1', '9', '1', '0', '9', '3', '7', '8', '2', '4', '6', '8', '8', '9', '2', '1', '3', '4', '3', '/', '1', '1', '5', '9', '7', '2', '3', '7', '3', '9', '2', '9', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '9', '0', '4', '6', '1', '3', '5', '0', '0', '2', '8', '7', '2', '0', '4', '4', '0', '7', '9', '1', '/', '3', '4', '7', '9', '1', '7', '1', '2', '1', '7', '8', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '3', '8', '4', '4', '9', '6', '0', '3', '4', '5', '9', '1', '1', '9', '6', '4', '9', '9', '/', '2', '3', '1', '9', '4', '4', '7', '4', '7', '8', '5', '8', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '5', '5', '4', '2', '6', '4', '6', '6', '6', '1', '7', '9', '7', '9', '1', '7', '2', '7', '6', '3', '/', '6', '9', '5', '8', '3', '4', '2', '4', '3', '5', '7', '6', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '9', '4', '0', '0', '7', '5', '2', '7', '6', '2', '8', '0', '0', '7', '3', '3', '9', '4', '8', '7', '/', '6', '9', '5', '8', '3', '4', '2', '4', '3', '5', '7', '6', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '2', '1', '9', '8', '6', '0', '1', '7', '5', '6', '0', '9', '0', '9', '0', '4', '4', '1', '9', '/', '5', '3', '5', '2', '5', '7', '1', '1', '0', '4', '4', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '4', '1', '2', '4', '8', '6', '4', '8', '6', '1', '7', '0', '8', '3', '0', '9', '1', '7', '/', '4', '4', '6', '0', '4', '7', '5', '9', '2', '0', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0154158Acc00600 : List (String × SourceJson) := (fragment0154158Field005Key00, fragment0154158Field005Value00) :: fragment0154158Acc00500
noncomputable def fragment0154158Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '4', '4', '4', '9', '7', '4', '9', '7', '9', '5', '9', '3', '8', '2', '9', '9', '4', '6', '2', '9', '/', '4', '6', '3', '8', '8', '9', '4', '9', '5', '7', '1', '7', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '3', '0', '8', '5', '7', '0', '3', '0', '4', '1', '8', '1', '0', '4', '5', '7', '1', '1', '/', '4', '4', '6', '0', '4', '7', '5', '9', '2', '0', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '9', '4', '7', '3', '5', '4', '8', '9', '5', '6', '7', '2', '0', '7', '7', '8', '9', '9', '/', '5', '1', '5', '4', '3', '2', '7', '7', '3', '0', '1', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '1', '9', '1', '0', '9', '3', '7', '8', '2', '4', '6', '8', '8', '9', '2', '1', '3', '4', '3', '/', '1', '1', '5', '9', '7', '2', '3', '7', '3', '9', '2', '9', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '9', '0', '4', '6', '1', '3', '5', '0', '0', '2', '8', '7', '2', '0', '4', '4', '0', '7', '9', '1', '/', '3', '4', '7', '9', '1', '7', '1', '2', '1', '7', '8', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '3', '8', '4', '4', '9', '6', '0', '3', '4', '5', '9', '1', '1', '9', '6', '4', '9', '9', '/', '2', '3', '1', '9', '4', '4', '7', '4', '7', '8', '5', '8', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '5', '5', '4', '2', '6', '4', '6', '6', '6', '1', '7', '9', '7', '9', '1', '7', '2', '7', '6', '3', '/', '6', '9', '5', '8', '3', '4', '2', '4', '3', '5', '7', '6', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '9', '4', '0', '0', '7', '5', '2', '7', '6', '2', '8', '0', '0', '7', '3', '3', '9', '4', '8', '7', '/', '6', '9', '5', '8', '3', '4', '2', '4', '3', '5', '7', '6', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '2', '1', '9', '8', '6', '0', '1', '7', '5', '6', '0', '9', '0', '9', '0', '4', '4', '1', '9', '/', '5', '3', '5', '2', '5', '7', '1', '1', '0', '4', '4', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '1', '2', '4', '8', '6', '4', '8', '6', '1', '7', '0', '8', '3', '0', '9', '1', '7', '/', '4', '4', '6', '0', '4', '7', '5', '9', '2', '0', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0154158_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 403) (SourceJson.white (fragment0154158Field005Chars00 ++ tail)) fragment0154158Acc00500 =
      SourceJson.object (fuel + 402) (SourceJson.white tail) fragment0154158Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0154158_object_field_005"
  err.flush

noncomputable def fragment0154158Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0154158Field006Value00 : SourceJson := .str (String.ofList ['7', '9', '3', '5', '3', '8', '1', '6', '0', '8', '0', '8', '9', '0', '4', '2', '3', '7', '9', '4', '2', '9', '4', '3', '6', '0', '2', '8', '4', '6', '9', '5', '3', '5', '6', '5', '3', '3', '3', '8', '3', '5', '1', '2', '0', '6', '4', '0', '0', '0', '0', '0', '/', '4', '3', '8', '3', '9', '4', '2', '1', '6', '5', '3', '8', '6', '1', '9', '0', '4', '7', '1', '7', '0', '8', '9', '2', '6', '4', '2', '9', '8', '9', '0', '1', '2', '3', '6', '5', '1', '1', '2', '3', '3', '1', '2', '1', '2', '2', '5', '7', '9', '0', '0', '6', '1', '8', '7', '0', '7', '0', '8', '9', '6', '2', '9', '8', '1', '3'])
noncomputable def fragment0154158Acc00700 : List (String × SourceJson) := (fragment0154158Field006Key00, fragment0154158Field006Value00) :: fragment0154158Acc00600
noncomputable def fragment0154158Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '9', '3', '5', '3', '8', '1', '6', '0', '8', '0', '8', '9', '0', '4', '2', '3', '7', '9', '4', '2', '9', '4', '3', '6', '0', '2', '8', '4', '6', '9', '5', '3', '5', '6', '5', '3', '3', '3', '8', '3', '5', '1', '2', '0', '6', '4', '0', '0', '0', '0', '0', '/', '4', '3', '8', '3', '9', '4', '2', '1', '6', '5', '3', '8', '6', '1', '9', '0', '4', '7', '1', '7', '0', '8', '9', '2', '6', '4', '2', '9', '8', '9', '0', '1', '2', '3', '6', '5', '1', '1', '2', '3', '3', '1', '2', '1', '2', '2', '5', '7', '9', '0', '0', '6', '1', '8', '7', '0', '7', '0', '8', '9', '6', '2', '9', '8', '1', '3', '"', ',']

theorem object_fragment0154158_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 402) (SourceJson.white (fragment0154158Field006Chars00 ++ tail)) fragment0154158Acc00600 =
      SourceJson.object (fuel + 401) (SourceJson.white tail) fragment0154158Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0154158_object_field_006"
  err.flush

noncomputable def fragment0154158Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0154158Field007Value00 : SourceJson := .str (String.ofList ['2', '8', '0', '2', '8', '7', '9', '4', '0', '4', '5', '6', '2', '8', '6', '4', '7', '8', '6', '8', '3', '6', '0', '5', '0', '8', '6', '1', '5', '8', '1', '0', '9', '7', '7', '2', '4', '9', '1', '9', '0', '0', '6', '6', '3', '1', '0', '3', '9', '1', '0', '6', '3', '0', '0', '4', '5', '3', '9', '1', '5', '3', '1', '6', '7', '7', '1', '1', '0', '6', '5', '8', '5', '3', '2', '6', '4', '4', '9', '2', '2', '0', '0', '9', '5', '8', '3', '1', '9', '6', '8', '6', '9', '2', '0', '6', '6', '9', '2', '5', '8', '0', '6', '7', '1', '6', '8', '2', '2', '9', '1', '3', '4', '5', '3', '7', '1', '9', '8', '8', '6', '4', '6', '3', '8', '8', '4', '9', '6', '7', '3', '3', '7', '1', '7', '6', '8', '4', '9', '5', '1', '9', '0', '4', '1', '6', '1', '5', '8', '1', '8', '5', '5', '6', '6', '6', '7', '9', '7', '3', '1', '2', '4', '0', '1', '7', '3', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '4', '1', '3', '9', '4', '8', '9', '4', '5', '5', '5', '6', '0', '4', '5', '0', '4', '3', '1', '3', '7', '6', '8', '4', '4', '9', '4', '1', '1', '5', '3', '6', '7', '4', '1', '7', '5', '8', '8', '1', '3', '8', '5', '2', '5', '7', '6', '3', '0', '8', '3', '6', '0', '2', '2', '4', '5', '1', '7', '0', '4', '0', '1', '7', '8', '8', '8', '2', '2', '7', '3', '9', '7', '1', '4', '5', '8', '0', '3', '8', '8', '0', '1', '1', '3', '9', '9', '8', '4', '6', '8', '8', '4', '3', '9', '2', '1', '8', '5', '6', '4', '3', '1', '4', '9', '7', '0', '8', '2', '5', '1', '8', '8', '0', '4', '6', '1', '5', '6', '2', '8', '3', '9', '6', '1', '4', '6', '9', '9', '0', '5', '4', '2', '4', '8', '6', '9', '2', '0', '2', '5', '3', '2', '9', '7', '4', '1', '9', '3', '3', '2', '5', '0', '4', '1', '7', '1', '0', '1', '5', '7', '3', '6', '3', '7', '6', '6', '2', '7', '3', '7', '4', '3', '1', '7', '6', '8', '6', '8', '6', '8', '2', '3', '6', '2', '2', '7', '6', '2', '6', '2', '5', '0', '7', '0', '2', '7', '9', '5', '4', '0', '0', '5', '1'])
noncomputable def fragment0154158Acc00800 : List (String × SourceJson) := (fragment0154158Field007Key00, fragment0154158Field007Value00) :: fragment0154158Acc00700
noncomputable def fragment0154158Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '8', '0', '2', '8', '7', '9', '4', '0', '4', '5', '6', '2', '8', '6', '4', '7', '8', '6', '8', '3', '6', '0', '5', '0', '8', '6', '1', '5', '8', '1', '0', '9', '7', '7', '2', '4', '9', '1', '9', '0', '0', '6', '6', '3', '1', '0', '3', '9', '1', '0', '6', '3', '0', '0', '4', '5', '3', '9', '1', '5', '3', '1', '6', '7', '7', '1', '1', '0', '6', '5', '8', '5', '3', '2', '6', '4', '4', '9', '2', '2', '0', '0', '9', '5', '8', '3', '1', '9', '6', '8', '6', '9', '2', '0', '6', '6', '9', '2', '5', '8', '0', '6', '7', '1', '6', '8', '2', '2', '9', '1', '3', '4', '5', '3', '7', '1', '9', '8', '8', '6', '4', '6', '3', '8', '8', '4', '9', '6', '7', '3', '3', '7', '1', '7', '6', '8', '4', '9', '5', '1', '9', '0', '4', '1', '6', '1', '5', '8', '1', '8', '5', '5', '6', '6', '6', '7', '9', '7', '3', '1', '2', '4', '0', '1', '7', '3', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '4', '1', '3', '9', '4', '8', '9', '4', '5', '5', '5', '6', '0', '4', '5', '0', '4', '3', '1', '3', '7', '6', '8', '4', '4', '9', '4', '1', '1', '5', '3', '6', '7', '4', '1', '7', '5', '8', '8', '1', '3', '8', '5', '2', '5', '7', '6', '3', '0', '8', '3', '6', '0', '2', '2', '4', '5', '1', '7', '0', '4', '0', '1', '7', '8', '8', '8', '2', '2', '7', '3', '9', '7', '1', '4', '5', '8', '0', '3', '8', '8', '0', '1', '1', '3', '9', '9', '8', '4', '6', '8', '8', '4', '3', '9', '2', '1', '8', '5', '6', '4', '3', '1', '4', '9', '7', '0', '8', '2', '5', '1', '8', '8', '0', '4', '6', '1', '5', '6', '2', '8', '3', '9', '6', '1', '4', '6', '9', '9', '0', '5', '4', '2', '4', '8', '6', '9', '2', '0', '2', '5', '3', '2', '9', '7', '4', '1', '9', '3', '3', '2', '5', '0', '4', '1', '7', '1', '0', '1', '5', '7', '3', '6', '3', '7', '6', '6', '2', '7', '3', '7', '4', '3', '1', '7', '6', '8', '6', '8', '6', '8', '2', '3', '6', '2', '2', '7', '6', '2', '6', '2', '5', '0', '7', '0', '2', '7', '9', '5', '4', '0', '0', '5', '1', '"', ',']

theorem object_fragment0154158_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 401) (SourceJson.white (fragment0154158Field007Chars00 ++ tail)) fragment0154158Acc00700 =
      SourceJson.object (fuel + 400) (SourceJson.white tail) fragment0154158Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0154158_object_field_007"
  err.flush

noncomputable def fragment0154158Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0154158Field008Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '4', '1', '1', '0', '3', '9', '6', '3', '9', '7', '0', '7', '2'])
noncomputable def fragment0154158Acc00900 : List (String × SourceJson) := (fragment0154158Field008Key00, fragment0154158Field008Value00) :: fragment0154158Acc00800
noncomputable def fragment0154158Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '3', '4', '1', '1', '0', '3', '9', '6', '3', '9', '7', '0', '7', '2', '"', ',']

theorem object_fragment0154158_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0154158Field008Chars00 ++ tail)) fragment0154158Acc00800 =
      SourceJson.object (fuel + 399) (SourceJson.white tail) fragment0154158Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0154158_object_field_008"
  err.flush

noncomputable def fragment0154158Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0154158Field009Value00 : SourceJson := .str (String.ofList ['3', '4', '6', '2', '2', '5', '0', '5', '8', '6', '3', '0', '1', '4', '6', '9'])
noncomputable def fragment0154158Acc01000 : List (String × SourceJson) := (fragment0154158Field009Key00, fragment0154158Field009Value00) :: fragment0154158Acc00900
noncomputable def fragment0154158Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '4', '6', '2', '2', '5', '0', '5', '8', '6', '3', '0', '1', '4', '6', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0154158_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 399) (SourceJson.white (fragment0154158Field009Chars00 ++ tail)) fragment0154158Acc00900 =
      .ok (.obj (fragment0154158Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0154158_object_field_009"
  err.flush

noncomputable def fragment0154158Chars : List Char := '{' :: (fragment0154158Field000Chars00 ++ fragment0154158Field001Chars00 ++ fragment0154158Field002Chars00 ++ fragment0154158Field003Chars00 ++ fragment0154158Field004Chars00 ++ fragment0154158Field005Chars00 ++ fragment0154158Field006Chars00 ++ fragment0154158Field007Chars00 ++ fragment0154158Field008Chars00 ++ fragment0154158Field009Chars00)
noncomputable def fragment0154158Value : SourceJson := .obj (fragment0154158Acc01000.reverse)

theorem value_fragment0154158 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 409) (fragment0154158Chars ++ tail) =
      .ok (fragment0154158Value, tail) := by
  have hinput : fragment0154158Chars ++ tail = '{' :: (fragment0154158Field000Chars00 ++ (fragment0154158Field001Chars00 ++ (fragment0154158Field002Chars00 ++ (fragment0154158Field003Chars00 ++ (fragment0154158Field004Chars00 ++ (fragment0154158Field005Chars00 ++ (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0154158Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 409) (fragment0154158Chars ++ tail) =
        SourceJson.value (fuel + 409) ('{' :: (fragment0154158Field000Chars00 ++ (fragment0154158Field001Chars00 ++ (fragment0154158Field002Chars00 ++ (fragment0154158Field003Chars00 ++ (fragment0154158Field004Chars00 ++ (fragment0154158Field005Chars00 ++ (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 409)) hinput
    _ = SourceJson.object (fuel + 408) (SourceJson.white (fragment0154158Field000Chars00 ++ (fragment0154158Field001Chars00 ++ (fragment0154158Field002Chars00 ++ (fragment0154158Field003Chars00 ++ (fragment0154158Field004Chars00 ++ (fragment0154158Field005Chars00 ++ (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail)))))))))))) fragment0154158Acc00000 := by rfl
    _ = SourceJson.object (fuel + 407) (SourceJson.white (fragment0154158Field001Chars00 ++ (fragment0154158Field002Chars00 ++ (fragment0154158Field003Chars00 ++ (fragment0154158Field004Chars00 ++ (fragment0154158Field005Chars00 ++ (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail))))))))))) fragment0154158Acc00100 := object_fragment0154158_field_000 fuel (fragment0154158Field001Chars00 ++ (fragment0154158Field002Chars00 ++ (fragment0154158Field003Chars00 ++ (fragment0154158Field004Chars00 ++ (fragment0154158Field005Chars00 ++ (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 406) (SourceJson.white (fragment0154158Field002Chars00 ++ (fragment0154158Field003Chars00 ++ (fragment0154158Field004Chars00 ++ (fragment0154158Field005Chars00 ++ (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail)))))))))) fragment0154158Acc00200 := object_fragment0154158_field_001 fuel (fragment0154158Field002Chars00 ++ (fragment0154158Field003Chars00 ++ (fragment0154158Field004Chars00 ++ (fragment0154158Field005Chars00 ++ (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 405) (SourceJson.white (fragment0154158Field003Chars00 ++ (fragment0154158Field004Chars00 ++ (fragment0154158Field005Chars00 ++ (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail))))))))) fragment0154158Acc00300 := object_fragment0154158_field_002 fuel (fragment0154158Field003Chars00 ++ (fragment0154158Field004Chars00 ++ (fragment0154158Field005Chars00 ++ (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 404) (SourceJson.white (fragment0154158Field004Chars00 ++ (fragment0154158Field005Chars00 ++ (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail)))))))) fragment0154158Acc00400 := object_fragment0154158_field_003 fuel (fragment0154158Field004Chars00 ++ (fragment0154158Field005Chars00 ++ (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 403) (SourceJson.white (fragment0154158Field005Chars00 ++ (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail))))))) fragment0154158Acc00500 := object_fragment0154158_field_004 fuel (fragment0154158Field005Chars00 ++ (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 402) (SourceJson.white (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail)))))) fragment0154158Acc00600 := object_fragment0154158_field_005 fuel (fragment0154158Field006Chars00 ++ (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 401) (SourceJson.white (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail))))) fragment0154158Acc00700 := object_fragment0154158_field_006 fuel (fragment0154158Field007Chars00 ++ (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail)))) fragment0154158Acc00800 := object_fragment0154158_field_007 fuel (fragment0154158Field008Chars00 ++ (fragment0154158Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 399) (SourceJson.white (fragment0154158Field009Chars00 ++ (tail))) fragment0154158Acc00900 := object_fragment0154158_field_008 fuel (fragment0154158Field009Chars00 ++ (tail))
    _ = .ok (fragment0154158Value, tail) := object_fragment0154158_field_009 fuel (tail)

noncomputable def fragment0156115Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0156115Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0156115Field000Value00 : SourceJson := .number (String.ofList ['3', '0'])
noncomputable def fragment0156115Acc00100 : List (String × SourceJson) := (fragment0156115Field000Key00, fragment0156115Field000Value00) :: fragment0156115Acc00000
noncomputable def fragment0156115Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '0', ',']

theorem object_fragment0156115_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 427) (SourceJson.white (fragment0156115Field000Chars00 ++ tail)) fragment0156115Acc00000 =
      SourceJson.object (fuel + 426) (SourceJson.white tail) fragment0156115Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0156115_object_field_000"
  err.flush

noncomputable def fragment0156115Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0156115Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['4'])]
noncomputable def fragment0156115Acc00200 : List (String × SourceJson) := (fragment0156115Field001Key00, fragment0156115Field001Value00) :: fragment0156115Acc00100
noncomputable def fragment0156115Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0156115_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 426) (SourceJson.white (fragment0156115Field001Chars00 ++ tail)) fragment0156115Acc00100 =
      SourceJson.object (fuel + 425) (SourceJson.white tail) fragment0156115Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0156115_object_field_001"
  err.flush

noncomputable def fragment0156115Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0156115Field002Value00 : SourceJson := .str (String.ofList ['2', '0', '8', '3', '7', '4', '4', '8', '2', '0', '8', '9', '4', '2', '0', '0', '3', '5', '7', '4', '1', '7', '0', '5', '9', '5', '7', '6', '5', '7', '1', '1', '2', '2', '1', '3', '/', '2', '9', '8', '7', '5', '6', '5', '0', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0156115Acc00300 : List (String × SourceJson) := (fragment0156115Field002Key00, fragment0156115Field002Value00) :: fragment0156115Acc00200
noncomputable def fragment0156115Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '0', '8', '3', '7', '4', '4', '8', '2', '0', '8', '9', '4', '2', '0', '0', '3', '5', '7', '4', '1', '7', '0', '5', '9', '5', '7', '6', '5', '7', '1', '1', '2', '2', '1', '3', '/', '2', '9', '8', '7', '5', '6', '5', '0', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0156115_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 425) (SourceJson.white (fragment0156115Field002Chars00 ++ tail)) fragment0156115Acc00200 =
      SourceJson.object (fuel + 424) (SourceJson.white tail) fragment0156115Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0156115_object_field_002"
  err.flush

noncomputable def fragment0156115Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0156115Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '1', '8', '7', '4', '8', '6', '7', '/', '4', '2', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0156115Acc00400 : List (String × SourceJson) := (fragment0156115Field003Key00, fragment0156115Field003Value00) :: fragment0156115Acc00300
noncomputable def fragment0156115Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '1', '8', '7', '4', '8', '6', '7', '/', '4', '2', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0156115_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 424) (SourceJson.white (fragment0156115Field003Chars00 ++ tail)) fragment0156115Acc00300 =
      SourceJson.object (fuel + 423) (SourceJson.white tail) fragment0156115Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0156115_object_field_003"
  err.flush

noncomputable def fragment0156115Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0156115Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0156115Acc00500 : List (String × SourceJson) := (fragment0156115Field004Key00, fragment0156115Field004Value00) :: fragment0156115Acc00400
noncomputable def fragment0156115Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0156115_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 423) (SourceJson.white (fragment0156115Field004Chars00 ++ tail)) fragment0156115Acc00400 =
      SourceJson.object (fuel + 422) (SourceJson.white tail) fragment0156115Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0156115_object_field_004"
  err.flush

noncomputable def fragment0156115Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0156115Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '7', '4', '0', '6', '4', '6', '1', '1', '6', '1', '8', '9', '2', '1', '8', '3', '5', '9', '8', '1', '2', '1', '7', '/', '2', '0', '2', '6', '1', '3', '3', '7', '9', '2', '7', '9', '3', '3', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '1', '4', '7', '0', '5', '5', '1', '1', '3', '2', '9', '4', '6', '6', '8', '5', '1', '0', '1', '/', '1', '9', '4', '8', '2', '0', '5', '5', '6', '9', '9', '9', '3', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '7', '3', '4', '6', '7', '0', '6', '3', '5', '2', '8', '5', '1', '0', '7', '8', '7', '6', '9', '6', '3', '/', '1', '0', '1', '3', '0', '6', '6', '8', '9', '6', '3', '9', '6', '6', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '2', '8', '1', '4', '8', '3', '0', '3', '1', '5', '9', '7', '8', '5', '9', '4', '0', '8', '0', '6', '3', '/', '5', '0', '6', '5', '3', '3', '4', '4', '8', '1', '9', '8', '3', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '2', '0', '3', '6', '2', '1', '8', '0', '9', '0', '9', '5', '5', '4', '6', '2', '7', '9', '4', '6', '1', '/', '5', '0', '6', '5', '3', '3', '4', '4', '8', '1', '9', '8', '3', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '0', '5', '8', '8', '3', '0', '1', '8', '6', '1', '2', '9', '2', '6', '8', '7', '0', '8', '7', '9', '/', '1', '0', '1', '3', '0', '6', '6', '8', '9', '6', '3', '9', '6', '6', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '5', '7', '1', '2', '6', '7', '6', '2', '0', '6', '3', '3', '3', '2', '9', '2', '1', '1', '0', '1', '/', '5', '9', '5', '9', '2', '1', '7', '0', '3', '7', '6', '2', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '9', '4', '5', '1', '5', '5', '9', '8', '3', '0', '5', '0', '4', '8', '1', '3', '6', '3', '7', '1', '/', '3', '3', '7', '6', '8', '8', '9', '6', '5', '4', '6', '5', '5', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '0', '9', '5', '9', '5', '9', '3', '3', '8', '4', '4', '1', '2', '2', '2', '1', '5', '6', '7', '/', '2', '5', '9', '7', '6', '0', '7', '4', '2', '6', '6', '5', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '2', '4', '4', '9', '0', '7', '9', '5', '1', '7', '8', '6', '4', '1', '1', '3', '0', '2', '9', '/', '6', '4', '9', '4', '0', '1', '8', '5', '6', '6', '6', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0156115Acc00600 : List (String × SourceJson) := (fragment0156115Field005Key00, fragment0156115Field005Value00) :: fragment0156115Acc00500
noncomputable def fragment0156115Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '4', '0', '6', '4', '6', '1', '1', '6', '1', '8', '9', '2', '1', '8', '3', '5', '9', '8', '1', '2', '1', '7', '/', '2', '0', '2', '6', '1', '3', '3', '7', '9', '2', '7', '9', '3', '3', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '1', '4', '7', '0', '5', '5', '1', '1', '3', '2', '9', '4', '6', '6', '8', '5', '1', '0', '1', '/', '1', '9', '4', '8', '2', '0', '5', '5', '6', '9', '9', '9', '3', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '7', '3', '4', '6', '7', '0', '6', '3', '5', '2', '8', '5', '1', '0', '7', '8', '7', '6', '9', '6', '3', '/', '1', '0', '1', '3', '0', '6', '6', '8', '9', '6', '3', '9', '6', '6', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '2', '8', '1', '4', '8', '3', '0', '3', '1', '5', '9', '7', '8', '5', '9', '4', '0', '8', '0', '6', '3', '/', '5', '0', '6', '5', '3', '3', '4', '4', '8', '1', '9', '8', '3', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '2', '0', '3', '6', '2', '1', '8', '0', '9', '0', '9', '5', '5', '4', '6', '2', '7', '9', '4', '6', '1', '/', '5', '0', '6', '5', '3', '3', '4', '4', '8', '1', '9', '8', '3', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '0', '5', '8', '8', '3', '0', '1', '8', '6', '1', '2', '9', '2', '6', '8', '7', '0', '8', '7', '9', '/', '1', '0', '1', '3', '0', '6', '6', '8', '9', '6', '3', '9', '6', '6', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '5', '7', '1', '2', '6', '7', '6', '2', '0', '6', '3', '3', '3', '2', '9', '2', '1', '1', '0', '1', '/', '5', '9', '5', '9', '2', '1', '7', '0', '3', '7', '6', '2', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '9', '4', '5', '1', '5', '5', '9', '8', '3', '0', '5', '0', '4', '8', '1', '3', '6', '3', '7', '1', '/', '3', '3', '7', '6', '8', '8', '9', '6', '5', '4', '6', '5', '5', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '0', '9', '5', '9', '5', '9', '3', '3', '8', '4', '4', '1', '2', '2', '2', '1', '5', '6', '7', '/', '2', '5', '9', '7', '6', '0', '7', '4', '2', '6', '6', '5', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '4', '4', '9', '0', '7', '9', '5', '1', '7', '8', '6', '4', '1', '1', '3', '0', '2', '9', '/', '6', '4', '9', '4', '0', '1', '8', '5', '6', '6', '6', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0156115_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 422) (SourceJson.white (fragment0156115Field005Chars00 ++ tail)) fragment0156115Acc00500 =
      SourceJson.object (fuel + 421) (SourceJson.white tail) fragment0156115Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0156115_object_field_005"
  err.flush

noncomputable def fragment0156115Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0156115Field006Value00 : SourceJson := .str (String.ofList ['8', '5', '5', '1', '1', '1', '3', '6', '6', '0', '2', '6', '1', '5', '5', '6', '1', '0', '6', '1', '2', '8', '6', '9', '1', '8', '4', '9', '7', '2', '9', '3', '9', '9', '0', '2', '5', '9', '7', '7', '4', '4', '8', '2', '0', '6', '4', '3', '4', '3', '0', '4', '0', '0', '/', '5', '7', '2', '7', '2', '7', '1', '1', '0', '7', '4', '7', '8', '4', '0', '7', '2', '5', '7', '9', '2', '9', '7', '8', '2', '4', '1', '1', '7', '6', '8', '8', '5', '9', '1', '2', '0', '1', '8', '4', '4', '9', '7', '8', '5', '4', '1', '6', '1', '0', '6', '3', '6', '8', '6', '3', '3', '3', '8', '6', '6', '3', '5', '9', '3', '4', '3', '3'])
noncomputable def fragment0156115Acc00700 : List (String × SourceJson) := (fragment0156115Field006Key00, fragment0156115Field006Value00) :: fragment0156115Acc00600
noncomputable def fragment0156115Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '5', '5', '1', '1', '1', '3', '6', '6', '0', '2', '6', '1', '5', '5', '6', '1', '0', '6', '1', '2', '8', '6', '9', '1', '8', '4', '9', '7', '2', '9', '3', '9', '9', '0', '2', '5', '9', '7', '7', '4', '4', '8', '2', '0', '6', '4', '3', '4', '3', '0', '4', '0', '0', '/', '5', '7', '2', '7', '2', '7', '1', '1', '0', '7', '4', '7', '8', '4', '0', '7', '2', '5', '7', '9', '2', '9', '7', '8', '2', '4', '1', '1', '7', '6', '8', '8', '5', '9', '1', '2', '0', '1', '8', '4', '4', '9', '7', '8', '5', '4', '1', '6', '1', '0', '6', '3', '6', '8', '6', '3', '3', '3', '8', '6', '6', '3', '5', '9', '3', '4', '3', '3', '"', ',']

theorem object_fragment0156115_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 421) (SourceJson.white (fragment0156115Field006Chars00 ++ tail)) fragment0156115Acc00600 =
      SourceJson.object (fuel + 420) (SourceJson.white tail) fragment0156115Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0156115_object_field_006"
  err.flush

noncomputable def fragment0156115Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0156115Field007Value00 : SourceJson := .str (String.ofList ['6', '2', '6', '8', '8', '5', '4', '7', '4', '6', '5', '8', '9', '2', '0', '2', '0', '8', '5', '7', '3', '1', '2', '1', '7', '3', '6', '4', '7', '0', '0', '4', '1', '5', '2', '2', '8', '5', '9', '4', '4', '5', '7', '6', '3', '0', '7', '5', '1', '2', '6', '8', '2', '9', '9', '1', '5', '9', '8', '6', '6', '0', '4', '7', '9', '7', '0', '6', '3', '9', '5', '0', '5', '3', '6', '3', '1', '0', '4', '4', '3', '6', '2', '3', '1', '9', '3', '7', '5', '5', '4', '3', '8', '9', '5', '9', '0', '4', '6', '8', '1', '7', '8', '7', '8', '7', '6', '7', '9', '4', '2', '1', '2', '2', '1', '0', '2', '9', '4', '2', '4', '8', '2', '5', '1', '5', '1', '4', '0', '7', '5', '2', '4', '2', '2', '8', '0', '7', '9', '2', '3', '8', '6', '8', '6', '0', '8', '8', '3', '6', '3', '0', '2', '3', '7', '9', '6', '7', '2', '8', '1', '5', '0', '7', '0', '3', '6', '8', '3', '2', '1', '8', '2', '1', '9', '9', '9', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '1', '2', '1', '8', '2', '6', '9', '3', '3', '7', '4', '6', '2', '5', '4', '0', '9', '0', '8', '2', '8', '5', '5', '8', '4', '2', '5', '6', '0', '1', '7', '3', '7', '2', '1', '2', '0', '7', '6', '2', '1', '7', '2', '0', '4', '0', '9', '7', '6', '8', '7', '7', '1', '1', '9', '2', '0', '7', '1', '8', '9', '3', '9', '8', '3', '4', '9', '6', '1', '0', '1', '8', '1', '6', '7', '0', '8', '3', '6', '7', '0', '4', '8', '1', '7', '1', '0', '8', '4', '0', '2', '1', '0', '2', '9', '5', '2', '7', '3', '0', '3', '5', '4', '4', '0', '1', '0', '9', '2', '0', '9', '9', '8', '8', '1', '0', '4', '4', '6', '3', '8', '7', '9', '3', '9', '5', '6', '5', '6', '1', '5', '2', '7', '0', '8', '2', '8', '7', '8', '1', '7', '5', '4', '7', '9', '0', '0', '4', '8', '9', '4', '8', '0', '3', '3', '1', '3', '1', '6', '7', '3', '9', '1', '9', '9', '6', '6', '5', '9', '9', '1', '1', '4', '5', '8', '9', '7', '4', '8', '8', '9', '0', '0', '7', '9', '6', '5', '2', '5', '8', '3', '6', '7', '7', '3', '1', '8', '4', '0', '7', '6', '5', '8', '6', '8', '8', '8', '4', '4', '8', '9', '6', '9'])
noncomputable def fragment0156115Acc00800 : List (String × SourceJson) := (fragment0156115Field007Key00, fragment0156115Field007Value00) :: fragment0156115Acc00700
noncomputable def fragment0156115Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '2', '6', '8', '8', '5', '4', '7', '4', '6', '5', '8', '9', '2', '0', '2', '0', '8', '5', '7', '3', '1', '2', '1', '7', '3', '6', '4', '7', '0', '0', '4', '1', '5', '2', '2', '8', '5', '9', '4', '4', '5', '7', '6', '3', '0', '7', '5', '1', '2', '6', '8', '2', '9', '9', '1', '5', '9', '8', '6', '6', '0', '4', '7', '9', '7', '0', '6', '3', '9', '5', '0', '5', '3', '6', '3', '1', '0', '4', '4', '3', '6', '2', '3', '1', '9', '3', '7', '5', '5', '4', '3', '8', '9', '5', '9', '0', '4', '6', '8', '1', '7', '8', '7', '8', '7', '6', '7', '9', '4', '2', '1', '2', '2', '1', '0', '2', '9', '4', '2', '4', '8', '2', '5', '1', '5', '1', '4', '0', '7', '5', '2', '4', '2', '2', '8', '0', '7', '9', '2', '3', '8', '6', '8', '6', '0', '8', '8', '3', '6', '3', '0', '2', '3', '7', '9', '6', '7', '2', '8', '1', '5', '0', '7', '0', '3', '6', '8', '3', '2', '1', '8', '2', '1', '9', '9', '9', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '1', '2', '1', '8', '2', '6', '9', '3', '3', '7', '4', '6', '2', '5', '4', '0', '9', '0', '8', '2', '8', '5', '5', '8', '4', '2', '5', '6', '0', '1', '7', '3', '7', '2', '1', '2', '0', '7', '6', '2', '1', '7', '2', '0', '4', '0', '9', '7', '6', '8', '7', '7', '1', '1', '9', '2', '0', '7', '1', '8', '9', '3', '9', '8', '3', '4', '9', '6', '1', '0', '1', '8', '1', '6', '7', '0', '8', '3', '6', '7', '0', '4', '8', '1', '7', '1', '0', '8', '4', '0', '2', '1', '0', '2', '9', '5', '2', '7', '3', '0', '3', '5', '4', '4', '0', '1', '0', '9', '2', '0', '9', '9', '8', '8', '1', '0', '4', '4', '6', '3', '8', '7', '9', '3', '9', '5', '6', '5', '6', '1', '5', '2', '7', '0', '8', '2', '8', '7', '8', '1', '7', '5', '4', '7', '9', '0', '0', '4', '8', '9', '4', '8', '0', '3', '3', '1', '3', '1', '6', '7', '3', '9', '1', '9', '9', '6', '6', '5', '9', '9', '1', '1', '4', '5', '8', '9', '7', '4', '8', '8', '9', '0', '0', '7', '9', '6', '5', '2', '5', '8', '3', '6', '7', '7', '3', '1', '8', '4', '0', '7', '6', '5', '8', '6', '8', '8', '8', '4', '4', '8', '9', '6', '9', '"', ',']

theorem object_fragment0156115_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 420) (SourceJson.white (fragment0156115Field007Chars00 ++ tail)) fragment0156115Acc00700 =
      SourceJson.object (fuel + 419) (SourceJson.white tail) fragment0156115Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0156115_object_field_007"
  err.flush

noncomputable def fragment0156115Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0156115Field008Value00 : SourceJson := .str (String.ofList ['1', '1', '8', '2', '9', '1', '7', '6', '7', '5', '8', '6', '9', '2', '5', '3'])
noncomputable def fragment0156115Acc00900 : List (String × SourceJson) := (fragment0156115Field008Key00, fragment0156115Field008Value00) :: fragment0156115Acc00800
noncomputable def fragment0156115Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '8', '2', '9', '1', '7', '6', '7', '5', '8', '6', '9', '2', '5', '3', '"', ',']

theorem object_fragment0156115_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 419) (SourceJson.white (fragment0156115Field008Chars00 ++ tail)) fragment0156115Acc00800 =
      SourceJson.object (fuel + 418) (SourceJson.white tail) fragment0156115Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0156115_object_field_008"
  err.flush

noncomputable def fragment0156115Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0156115Field009Value00 : SourceJson := .str (String.ofList ['2', '9', '0', '0', '7', '9', '9', '3', '3', '9', '7', '1', '4', '0', '0', '8'])
noncomputable def fragment0156115Acc01000 : List (String × SourceJson) := (fragment0156115Field009Key00, fragment0156115Field009Value00) :: fragment0156115Acc00900
noncomputable def fragment0156115Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '9', '0', '0', '7', '9', '9', '3', '3', '9', '7', '1', '4', '0', '0', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0156115_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 418) (SourceJson.white (fragment0156115Field009Chars00 ++ tail)) fragment0156115Acc00900 =
      .ok (.obj (fragment0156115Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0156115_object_field_009"
  err.flush

noncomputable def fragment0156115Chars : List Char := '{' :: (fragment0156115Field000Chars00 ++ fragment0156115Field001Chars00 ++ fragment0156115Field002Chars00 ++ fragment0156115Field003Chars00 ++ fragment0156115Field004Chars00 ++ fragment0156115Field005Chars00 ++ fragment0156115Field006Chars00 ++ fragment0156115Field007Chars00 ++ fragment0156115Field008Chars00 ++ fragment0156115Field009Chars00)
noncomputable def fragment0156115Value : SourceJson := .obj (fragment0156115Acc01000.reverse)

theorem value_fragment0156115 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 428) (fragment0156115Chars ++ tail) =
      .ok (fragment0156115Value, tail) := by
  have hinput : fragment0156115Chars ++ tail = '{' :: (fragment0156115Field000Chars00 ++ (fragment0156115Field001Chars00 ++ (fragment0156115Field002Chars00 ++ (fragment0156115Field003Chars00 ++ (fragment0156115Field004Chars00 ++ (fragment0156115Field005Chars00 ++ (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0156115Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 428) (fragment0156115Chars ++ tail) =
        SourceJson.value (fuel + 428) ('{' :: (fragment0156115Field000Chars00 ++ (fragment0156115Field001Chars00 ++ (fragment0156115Field002Chars00 ++ (fragment0156115Field003Chars00 ++ (fragment0156115Field004Chars00 ++ (fragment0156115Field005Chars00 ++ (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 428)) hinput
    _ = SourceJson.object (fuel + 427) (SourceJson.white (fragment0156115Field000Chars00 ++ (fragment0156115Field001Chars00 ++ (fragment0156115Field002Chars00 ++ (fragment0156115Field003Chars00 ++ (fragment0156115Field004Chars00 ++ (fragment0156115Field005Chars00 ++ (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail)))))))))))) fragment0156115Acc00000 := by rfl
    _ = SourceJson.object (fuel + 426) (SourceJson.white (fragment0156115Field001Chars00 ++ (fragment0156115Field002Chars00 ++ (fragment0156115Field003Chars00 ++ (fragment0156115Field004Chars00 ++ (fragment0156115Field005Chars00 ++ (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail))))))))))) fragment0156115Acc00100 := object_fragment0156115_field_000 fuel (fragment0156115Field001Chars00 ++ (fragment0156115Field002Chars00 ++ (fragment0156115Field003Chars00 ++ (fragment0156115Field004Chars00 ++ (fragment0156115Field005Chars00 ++ (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 425) (SourceJson.white (fragment0156115Field002Chars00 ++ (fragment0156115Field003Chars00 ++ (fragment0156115Field004Chars00 ++ (fragment0156115Field005Chars00 ++ (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail)))))))))) fragment0156115Acc00200 := object_fragment0156115_field_001 fuel (fragment0156115Field002Chars00 ++ (fragment0156115Field003Chars00 ++ (fragment0156115Field004Chars00 ++ (fragment0156115Field005Chars00 ++ (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 424) (SourceJson.white (fragment0156115Field003Chars00 ++ (fragment0156115Field004Chars00 ++ (fragment0156115Field005Chars00 ++ (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail))))))))) fragment0156115Acc00300 := object_fragment0156115_field_002 fuel (fragment0156115Field003Chars00 ++ (fragment0156115Field004Chars00 ++ (fragment0156115Field005Chars00 ++ (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 423) (SourceJson.white (fragment0156115Field004Chars00 ++ (fragment0156115Field005Chars00 ++ (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail)))))))) fragment0156115Acc00400 := object_fragment0156115_field_003 fuel (fragment0156115Field004Chars00 ++ (fragment0156115Field005Chars00 ++ (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 422) (SourceJson.white (fragment0156115Field005Chars00 ++ (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail))))))) fragment0156115Acc00500 := object_fragment0156115_field_004 fuel (fragment0156115Field005Chars00 ++ (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 421) (SourceJson.white (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail)))))) fragment0156115Acc00600 := object_fragment0156115_field_005 fuel (fragment0156115Field006Chars00 ++ (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 420) (SourceJson.white (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail))))) fragment0156115Acc00700 := object_fragment0156115_field_006 fuel (fragment0156115Field007Chars00 ++ (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 419) (SourceJson.white (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail)))) fragment0156115Acc00800 := object_fragment0156115_field_007 fuel (fragment0156115Field008Chars00 ++ (fragment0156115Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 418) (SourceJson.white (fragment0156115Field009Chars00 ++ (tail))) fragment0156115Acc00900 := object_fragment0156115_field_008 fuel (fragment0156115Field009Chars00 ++ (tail))
    _ = .ok (fragment0156115Value, tail) := object_fragment0156115_field_009 fuel (tail)

noncomputable def fragment0158122Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0158122Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0158122Field000Value00 : SourceJson := .number (String.ofList ['3', '1'])
noncomputable def fragment0158122Acc00100 : List (String × SourceJson) := (fragment0158122Field000Key00, fragment0158122Field000Value00) :: fragment0158122Acc00000
noncomputable def fragment0158122Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '1', ',']

theorem object_fragment0158122_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 311) (SourceJson.white (fragment0158122Field000Chars00 ++ tail)) fragment0158122Acc00000 =
      SourceJson.object (fuel + 310) (SourceJson.white tail) fragment0158122Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158122_object_field_000"
  err.flush

noncomputable def fragment0158122Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0158122Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0158122Acc00200 : List (String × SourceJson) := (fragment0158122Field001Key00, fragment0158122Field001Value00) :: fragment0158122Acc00100
noncomputable def fragment0158122Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0158122_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 310) (SourceJson.white (fragment0158122Field001Chars00 ++ tail)) fragment0158122Acc00100 =
      SourceJson.object (fuel + 309) (SourceJson.white tail) fragment0158122Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158122_object_field_001"
  err.flush

noncomputable def fragment0158122Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0158122Field002Value00 : SourceJson := .str (String.ofList ['6', '3', '6', '2', '4', '6', '8', '2', '8', '0', '8', '1', '5', '3', '7', '6', '9', '6', '2', '3', '5', '0', '6', '8', '4', '4', '9', '2', '6', '2', '8', '7', '3', '1', '7', '/', '1', '8', '6', '7', '3', '4', '0', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0158122Acc00300 : List (String × SourceJson) := (fragment0158122Field002Key00, fragment0158122Field002Value00) :: fragment0158122Acc00200
noncomputable def fragment0158122Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '3', '6', '2', '4', '6', '8', '2', '8', '0', '8', '1', '5', '3', '7', '6', '9', '6', '2', '3', '5', '0', '6', '8', '4', '4', '9', '2', '6', '2', '8', '7', '3', '1', '7', '/', '1', '8', '6', '7', '3', '4', '0', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0158122_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 309) (SourceJson.white (fragment0158122Field002Chars00 ++ tail)) fragment0158122Acc00200 =
      SourceJson.object (fuel + 308) (SourceJson.white tail) fragment0158122Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158122_object_field_002"
  err.flush

noncomputable def fragment0158122Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0158122Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0158122Acc00400 : List (String × SourceJson) := (fragment0158122Field003Key00, fragment0158122Field003Value00) :: fragment0158122Acc00300
noncomputable def fragment0158122Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0158122_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 308) (SourceJson.white (fragment0158122Field003Chars00 ++ tail)) fragment0158122Acc00300 =
      SourceJson.object (fuel + 307) (SourceJson.white tail) fragment0158122Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158122_object_field_003"
  err.flush

noncomputable def fragment0158122Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0158122Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '5', '3', '1', '2', '4', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0158122Acc00500 : List (String × SourceJson) := (fragment0158122Field004Key00, fragment0158122Field004Value00) :: fragment0158122Acc00400
noncomputable def fragment0158122Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '3', '1', '2', '4', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0158122_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 307) (SourceJson.white (fragment0158122Field004Chars00 ++ tail)) fragment0158122Acc00400 =
      SourceJson.object (fuel + 306) (SourceJson.white tail) fragment0158122Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158122_object_field_004"
  err.flush

noncomputable def fragment0158122Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0158122Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '4', '5', '3', '3', '7', '8', '1', '6', '3', '9', '1', '2', '5', '6', '4', '1', '/', '3', '9', '0', '9', '8', '8', '8', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '4', '1', '7', '7', '1', '1', '1', '7', '7', '1', '0', '8', '5', '7', '/', '4', '8', '8', '7', '3', '6', '1', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '0', '7', '2', '4', '7', '6', '0', '5', '8', '7', '1', '3', '9', '9', '/', '3', '9', '0', '9', '8', '8', '8', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '5', '6', '1', '4', '1', '5', '8', '0', '9', '6', '1', '1', '4', '7', '/', '9', '7', '7', '4', '7', '2', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '7', '8', '6', '0', '2', '4', '8', '2', '0', '1', '4', '6', '3', '5', '3', '/', '9', '7', '7', '4', '7', '2', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '9', '2', '8', '8', '0', '1', '5', '4', '6', '5', '2', '4', '3', '/', '1', '9', '5', '4', '9', '4', '4', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '1', '7', '0', '6', '5', '4', '9', '3', '8', '3', '4', '9', '8', '9', '/', '1', '9', '5', '4', '9', '4', '4', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '0', '0', '4', '4', '7', '4', '6', '2', '2', '4', '7', '6', '2', '7', '/', '6', '5', '1', '6', '4', '8', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '4', '6', '0', '9', '9', '2', '8', '2', '2', '5', '2', '4', '2', '7', '/', '6', '5', '1', '6', '4', '8', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '3', '7', '2', '7', '7', '6', '3', '2', '4', '0', '1', '9', '3', '/', '1', '6', '2', '9', '1', '2', '0', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0158122Acc00600 : List (String × SourceJson) := (fragment0158122Field005Key00, fragment0158122Field005Value00) :: fragment0158122Acc00500
noncomputable def fragment0158122Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '5', '3', '3', '7', '8', '1', '6', '3', '9', '1', '2', '5', '6', '4', '1', '/', '3', '9', '0', '9', '8', '8', '8', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '4', '1', '7', '7', '1', '1', '1', '7', '7', '1', '0', '8', '5', '7', '/', '4', '8', '8', '7', '3', '6', '1', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '0', '7', '2', '4', '7', '6', '0', '5', '8', '7', '1', '3', '9', '9', '/', '3', '9', '0', '9', '8', '8', '8', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '5', '6', '1', '4', '1', '5', '8', '0', '9', '6', '1', '1', '4', '7', '/', '9', '7', '7', '4', '7', '2', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '8', '6', '0', '2', '4', '8', '2', '0', '1', '4', '6', '3', '5', '3', '/', '9', '7', '7', '4', '7', '2', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '9', '2', '8', '8', '0', '1', '5', '4', '6', '5', '2', '4', '3', '/', '1', '9', '5', '4', '9', '4', '4', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '1', '7', '0', '6', '5', '4', '9', '3', '8', '3', '4', '9', '8', '9', '/', '1', '9', '5', '4', '9', '4', '4', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '0', '0', '4', '4', '7', '4', '6', '2', '2', '4', '7', '6', '2', '7', '/', '6', '5', '1', '6', '4', '8', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '6', '0', '9', '9', '2', '8', '2', '2', '5', '2', '4', '2', '7', '/', '6', '5', '1', '6', '4', '8', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '3', '7', '2', '7', '7', '6', '3', '2', '4', '0', '1', '9', '3', '/', '1', '6', '2', '9', '1', '2', '0', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0158122_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 306) (SourceJson.white (fragment0158122Field005Chars00 ++ tail)) fragment0158122Acc00500 =
      SourceJson.object (fuel + 305) (SourceJson.white tail) fragment0158122Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158122_object_field_005"
  err.flush

noncomputable def fragment0158122Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0158122Field006Value00 : SourceJson := .str (String.ofList ['6', '1', '4', '2', '6', '6', '8', '9', '1', '2', '9', '3', '1', '4', '7', '5', '4', '2', '3', '8', '4', '7', '5', '5', '3', '8', '6', '4', '5', '8', '5', '8', '9', '5', '1', '6', '5', '8', '5', '1', '4', '8', '7', '6', '8', '0', '0', '0', '0', '0', '0', '/', '3', '3', '1', '9', '1', '2', '2', '9', '2', '2', '6', '1', '9', '4', '4', '4', '5', '0', '5', '3', '3', '0', '6', '1', '0', '4', '5', '0', '2', '2', '2', '2', '3', '4', '5', '8', '4', '2', '4', '0', '0', '2', '9', '2', '7', '3', '3', '4', '4', '0', '4', '9', '2', '7', '9', '9', '6', '0', '3', '8', '1', '3', '7', '2', '7'])
noncomputable def fragment0158122Acc00700 : List (String × SourceJson) := (fragment0158122Field006Key00, fragment0158122Field006Value00) :: fragment0158122Acc00600
noncomputable def fragment0158122Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '1', '4', '2', '6', '6', '8', '9', '1', '2', '9', '3', '1', '4', '7', '5', '4', '2', '3', '8', '4', '7', '5', '5', '3', '8', '6', '4', '5', '8', '5', '8', '9', '5', '1', '6', '5', '8', '5', '1', '4', '8', '7', '6', '8', '0', '0', '0', '0', '0', '0', '/', '3', '3', '1', '9', '1', '2', '2', '9', '2', '2', '6', '1', '9', '4', '4', '4', '5', '0', '5', '3', '3', '0', '6', '1', '0', '4', '5', '0', '2', '2', '2', '2', '3', '4', '5', '8', '4', '2', '4', '0', '0', '2', '9', '2', '7', '3', '3', '4', '4', '0', '4', '9', '2', '7', '9', '9', '6', '0', '3', '8', '1', '3', '7', '2', '7', '"', ',']

theorem object_fragment0158122_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 305) (SourceJson.white (fragment0158122Field006Chars00 ++ tail)) fragment0158122Acc00600 =
      SourceJson.object (fuel + 304) (SourceJson.white tail) fragment0158122Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158122_object_field_006"
  err.flush

noncomputable def fragment0158122Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0158122Field007Value00 : SourceJson := .str (String.ofList ['7', '3', '2', '4', '1', '2', '4', '9', '6', '3', '3', '8', '4', '8', '9', '6', '9', '9', '7', '8', '7', '4', '6', '5', '9', '4', '3', '0', '7', '1', '6', '5', '6', '1', '6', '0', '3', '4', '8', '5', '8', '2', '0', '0', '6', '0', '5', '5', '1', '0', '3', '6', '7', '8', '5', '9', '7', '2', '3', '4', '5', '4', '1', '6', '8', '8', '2', '0', '2', '9', '0', '4', '2', '2', '7', '8', '3', '8', '9', '9', '2', '1', '5', '8', '1', '7', '0', '0', '1', '1', '1', '1', '8', '6', '7', '6', '6', '7', '8', '5', '8', '0', '3', '0', '5', '1', '2', '6', '9', '6', '9', '9', '9', '0', '7', '0', '9', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '4', '1', '7', '3', '9', '3', '9', '9', '9', '1', '6', '6', '6', '3', '2', '0', '7', '5', '8', '9', '8', '3', '0', '0', '2', '9', '5', '9', '5', '3', '4', '5', '1', '5', '7', '6', '3', '1', '7', '6', '1', '8', '4', '4', '2', '9', '6', '0', '3', '9', '2', '1', '7', '0', '2', '4', '5', '2', '5', '8', '6', '7', '5', '9', '7', '7', '7', '0', '6', '4', '2', '1', '3', '7', '4', '9', '7', '3', '4', '6', '7', '0', '0', '9', '4', '1', '3', '6', '7', '3', '8', '5', '3', '5', '1', '3', '4', '4', '4', '9', '2', '4', '6', '5', '6', '1', '9', '9', '2', '4', '6', '1', '4', '4', '4', '7', '1', '0', '3', '5', '7', '0', '9', '8', '4', '8', '9', '3', '8', '0', '8', '3', '5', '0', '4', '3', '3', '0', '0', '2', '3', '5', '7', '1', '9', '2', '4', '6', '5', '3', '1', '0', '8', '2', '7'])
noncomputable def fragment0158122Acc00800 : List (String × SourceJson) := (fragment0158122Field007Key00, fragment0158122Field007Value00) :: fragment0158122Acc00700
noncomputable def fragment0158122Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '3', '2', '4', '1', '2', '4', '9', '6', '3', '3', '8', '4', '8', '9', '6', '9', '9', '7', '8', '7', '4', '6', '5', '9', '4', '3', '0', '7', '1', '6', '5', '6', '1', '6', '0', '3', '4', '8', '5', '8', '2', '0', '0', '6', '0', '5', '5', '1', '0', '3', '6', '7', '8', '5', '9', '7', '2', '3', '4', '5', '4', '1', '6', '8', '8', '2', '0', '2', '9', '0', '4', '2', '2', '7', '8', '3', '8', '9', '9', '2', '1', '5', '8', '1', '7', '0', '0', '1', '1', '1', '1', '8', '6', '7', '6', '6', '7', '8', '5', '8', '0', '3', '0', '5', '1', '2', '6', '9', '6', '9', '9', '9', '0', '7', '0', '9', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '4', '1', '7', '3', '9', '3', '9', '9', '9', '1', '6', '6', '6', '3', '2', '0', '7', '5', '8', '9', '8', '3', '0', '0', '2', '9', '5', '9', '5', '3', '4', '5', '1', '5', '7', '6', '3', '1', '7', '6', '1', '8', '4', '4', '2', '9', '6', '0', '3', '9', '2', '1', '7', '0', '2', '4', '5', '2', '5', '8', '6', '7', '5', '9', '7', '7', '7', '0', '6', '4', '2', '1', '3', '7', '4', '9', '7', '3', '4', '6', '7', '0', '0', '9', '4', '1', '3', '6', '7', '3', '8', '5', '3', '5', '1', '3', '4', '4', '4', '9', '2', '4', '6', '5', '6', '1', '9', '9', '2', '4', '6', '1', '4', '4', '4', '7', '1', '0', '3', '5', '7', '0', '9', '8', '4', '8', '9', '3', '8', '0', '8', '3', '5', '0', '4', '3', '3', '0', '0', '2', '3', '5', '7', '1', '9', '2', '4', '6', '5', '3', '1', '0', '8', '2', '7', '"', ',']

theorem object_fragment0158122_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 304) (SourceJson.white (fragment0158122Field007Chars00 ++ tail)) fragment0158122Acc00700 =
      SourceJson.object (fuel + 303) (SourceJson.white tail) fragment0158122Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158122_object_field_007"
  err.flush

noncomputable def fragment0158122Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0158122Field008Value00 : SourceJson := .str (String.ofList ['1', '4', '6', '6', '2', '6', '7', '9', '9', '3', '8', '3', '7', '8', '8', '3'])
noncomputable def fragment0158122Acc00900 : List (String × SourceJson) := (fragment0158122Field008Key00, fragment0158122Field008Value00) :: fragment0158122Acc00800
noncomputable def fragment0158122Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '6', '6', '2', '6', '7', '9', '9', '3', '8', '3', '7', '8', '8', '3', '"', ',']

theorem object_fragment0158122_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 303) (SourceJson.white (fragment0158122Field008Chars00 ++ tail)) fragment0158122Acc00800 =
      SourceJson.object (fuel + 302) (SourceJson.white tail) fragment0158122Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158122_object_field_008"
  err.flush

noncomputable def fragment0158122Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0158122Field009Value00 : SourceJson := .str (String.ofList ['4', '6', '7', '3', '0', '9', '7', '7', '7', '6', '4', '9', '6', '2', '8', '4'])
noncomputable def fragment0158122Acc01000 : List (String × SourceJson) := (fragment0158122Field009Key00, fragment0158122Field009Value00) :: fragment0158122Acc00900
noncomputable def fragment0158122Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '6', '7', '3', '0', '9', '7', '7', '7', '6', '4', '9', '6', '2', '8', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0158122_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 302) (SourceJson.white (fragment0158122Field009Chars00 ++ tail)) fragment0158122Acc00900 =
      .ok (.obj (fragment0158122Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158122_object_field_009"
  err.flush

noncomputable def fragment0158122Chars : List Char := '{' :: (fragment0158122Field000Chars00 ++ fragment0158122Field001Chars00 ++ fragment0158122Field002Chars00 ++ fragment0158122Field003Chars00 ++ fragment0158122Field004Chars00 ++ fragment0158122Field005Chars00 ++ fragment0158122Field006Chars00 ++ fragment0158122Field007Chars00 ++ fragment0158122Field008Chars00 ++ fragment0158122Field009Chars00)
noncomputable def fragment0158122Value : SourceJson := .obj (fragment0158122Acc01000.reverse)

theorem value_fragment0158122 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 312) (fragment0158122Chars ++ tail) =
      .ok (fragment0158122Value, tail) := by
  have hinput : fragment0158122Chars ++ tail = '{' :: (fragment0158122Field000Chars00 ++ (fragment0158122Field001Chars00 ++ (fragment0158122Field002Chars00 ++ (fragment0158122Field003Chars00 ++ (fragment0158122Field004Chars00 ++ (fragment0158122Field005Chars00 ++ (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0158122Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 312) (fragment0158122Chars ++ tail) =
        SourceJson.value (fuel + 312) ('{' :: (fragment0158122Field000Chars00 ++ (fragment0158122Field001Chars00 ++ (fragment0158122Field002Chars00 ++ (fragment0158122Field003Chars00 ++ (fragment0158122Field004Chars00 ++ (fragment0158122Field005Chars00 ++ (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 312)) hinput
    _ = SourceJson.object (fuel + 311) (SourceJson.white (fragment0158122Field000Chars00 ++ (fragment0158122Field001Chars00 ++ (fragment0158122Field002Chars00 ++ (fragment0158122Field003Chars00 ++ (fragment0158122Field004Chars00 ++ (fragment0158122Field005Chars00 ++ (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail)))))))))))) fragment0158122Acc00000 := by rfl
    _ = SourceJson.object (fuel + 310) (SourceJson.white (fragment0158122Field001Chars00 ++ (fragment0158122Field002Chars00 ++ (fragment0158122Field003Chars00 ++ (fragment0158122Field004Chars00 ++ (fragment0158122Field005Chars00 ++ (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail))))))))))) fragment0158122Acc00100 := object_fragment0158122_field_000 fuel (fragment0158122Field001Chars00 ++ (fragment0158122Field002Chars00 ++ (fragment0158122Field003Chars00 ++ (fragment0158122Field004Chars00 ++ (fragment0158122Field005Chars00 ++ (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 309) (SourceJson.white (fragment0158122Field002Chars00 ++ (fragment0158122Field003Chars00 ++ (fragment0158122Field004Chars00 ++ (fragment0158122Field005Chars00 ++ (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail)))))))))) fragment0158122Acc00200 := object_fragment0158122_field_001 fuel (fragment0158122Field002Chars00 ++ (fragment0158122Field003Chars00 ++ (fragment0158122Field004Chars00 ++ (fragment0158122Field005Chars00 ++ (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 308) (SourceJson.white (fragment0158122Field003Chars00 ++ (fragment0158122Field004Chars00 ++ (fragment0158122Field005Chars00 ++ (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail))))))))) fragment0158122Acc00300 := object_fragment0158122_field_002 fuel (fragment0158122Field003Chars00 ++ (fragment0158122Field004Chars00 ++ (fragment0158122Field005Chars00 ++ (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 307) (SourceJson.white (fragment0158122Field004Chars00 ++ (fragment0158122Field005Chars00 ++ (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail)))))))) fragment0158122Acc00400 := object_fragment0158122_field_003 fuel (fragment0158122Field004Chars00 ++ (fragment0158122Field005Chars00 ++ (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 306) (SourceJson.white (fragment0158122Field005Chars00 ++ (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail))))))) fragment0158122Acc00500 := object_fragment0158122_field_004 fuel (fragment0158122Field005Chars00 ++ (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 305) (SourceJson.white (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail)))))) fragment0158122Acc00600 := object_fragment0158122_field_005 fuel (fragment0158122Field006Chars00 ++ (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 304) (SourceJson.white (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail))))) fragment0158122Acc00700 := object_fragment0158122_field_006 fuel (fragment0158122Field007Chars00 ++ (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 303) (SourceJson.white (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail)))) fragment0158122Acc00800 := object_fragment0158122_field_007 fuel (fragment0158122Field008Chars00 ++ (fragment0158122Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 302) (SourceJson.white (fragment0158122Field009Chars00 ++ (tail))) fragment0158122Acc00900 := object_fragment0158122_field_008 fuel (fragment0158122Field009Chars00 ++ (tail))
    _ = .ok (fragment0158122Value, tail) := object_fragment0158122_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0024_before_reader"
  err.flush

noncomputable def chunk0024LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0024SuffixChars00 : List Char := [',']
noncomputable def chunk0024Chars00 : List Char := chunk0024LeadChars00 ++ fragment0145333Chars ++ chunk0024SuffixChars00
noncomputable def chunk0024Push00 (acc : List SourceJson) : List SourceJson := fragment0145333Value :: acc

noncomputable def chunk0024AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0024_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 449)
      (SourceJson.white (chunk0024LeadChars00 ++ (fragment0145333Chars ++ rest))) acc =
      (SourceJson.value (fuel + 448) (fragment0145333Chars ++ rest)).bind
        (chunk0024AfterValue00 (fuel + 448) acc) := by rfl

theorem array_chunk0024 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 449) (SourceJson.white (chunk0024Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 448) (SourceJson.white tail) (chunk0024Push00 acc) := by
  have hinput : chunk0024Chars00 ++ tail = chunk0024LeadChars00 ++ (fragment0145333Chars ++ (chunk0024SuffixChars00 ++ tail)) := by
    simp only [chunk0024Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 449) (SourceJson.white (chunk0024Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 449)
          (SourceJson.white (chunk0024LeadChars00 ++ (fragment0145333Chars ++ (chunk0024SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 449) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 448) (fragment0145333Chars ++ (chunk0024SuffixChars00 ++ tail))).bind
        (chunk0024AfterValue00 (fuel + 448) acc) := array_chunk0024_head fuel (chunk0024SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0145333Value, chunk0024SuffixChars00 ++ tail)).bind
        (chunk0024AfterValue00 (fuel + 448) acc) :=
      congrArg (fun result => result.bind (chunk0024AfterValue00 (fuel + 448) acc))
        (value_fragment0145333 (fuel + 133) (chunk0024SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 448) (SourceJson.white tail) (chunk0024Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0024_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0025_before_reader"
  err.flush

noncomputable def chunk0025LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0025SuffixChars00 : List Char := [',']
noncomputable def chunk0025Chars00 : List Char := chunk0025LeadChars00 ++ fragment0147088Chars ++ chunk0025SuffixChars00
noncomputable def chunk0025Push00 (acc : List SourceJson) : List SourceJson := fragment0147088Value :: acc

noncomputable def chunk0025AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0025_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 448)
      (SourceJson.white (chunk0025LeadChars00 ++ (fragment0147088Chars ++ rest))) acc =
      (SourceJson.value (fuel + 447) (fragment0147088Chars ++ rest)).bind
        (chunk0025AfterValue00 (fuel + 447) acc) := by rfl

theorem array_chunk0025 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 448) (SourceJson.white (chunk0025Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 447) (SourceJson.white tail) (chunk0025Push00 acc) := by
  have hinput : chunk0025Chars00 ++ tail = chunk0025LeadChars00 ++ (fragment0147088Chars ++ (chunk0025SuffixChars00 ++ tail)) := by
    simp only [chunk0025Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 448) (SourceJson.white (chunk0025Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 448)
          (SourceJson.white (chunk0025LeadChars00 ++ (fragment0147088Chars ++ (chunk0025SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 448) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 447) (fragment0147088Chars ++ (chunk0025SuffixChars00 ++ tail))).bind
        (chunk0025AfterValue00 (fuel + 447) acc) := array_chunk0025_head fuel (chunk0025SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0147088Value, chunk0025SuffixChars00 ++ tail)).bind
        (chunk0025AfterValue00 (fuel + 447) acc) :=
      congrArg (fun result => result.bind (chunk0025AfterValue00 (fuel + 447) acc))
        (value_fragment0147088 (fuel + 208) (chunk0025SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 447) (SourceJson.white tail) (chunk0025Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0025_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0026_before_reader"
  err.flush

noncomputable def chunk0026LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0026SuffixChars00 : List Char := [',']
noncomputable def chunk0026Chars00 : List Char := chunk0026LeadChars00 ++ fragment0148691Chars ++ chunk0026SuffixChars00
noncomputable def chunk0026Push00 (acc : List SourceJson) : List SourceJson := fragment0148691Value :: acc

noncomputable def chunk0026AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0026_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 447)
      (SourceJson.white (chunk0026LeadChars00 ++ (fragment0148691Chars ++ rest))) acc =
      (SourceJson.value (fuel + 446) (fragment0148691Chars ++ rest)).bind
        (chunk0026AfterValue00 (fuel + 446) acc) := by rfl

theorem array_chunk0026 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 447) (SourceJson.white (chunk0026Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 446) (SourceJson.white tail) (chunk0026Push00 acc) := by
  have hinput : chunk0026Chars00 ++ tail = chunk0026LeadChars00 ++ (fragment0148691Chars ++ (chunk0026SuffixChars00 ++ tail)) := by
    simp only [chunk0026Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 447) (SourceJson.white (chunk0026Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 447)
          (SourceJson.white (chunk0026LeadChars00 ++ (fragment0148691Chars ++ (chunk0026SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 447) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 446) (fragment0148691Chars ++ (chunk0026SuffixChars00 ++ tail))).bind
        (chunk0026AfterValue00 (fuel + 446) acc) := array_chunk0026_head fuel (chunk0026SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0148691Value, chunk0026SuffixChars00 ++ tail)).bind
        (chunk0026AfterValue00 (fuel + 446) acc) :=
      congrArg (fun result => result.bind (chunk0026AfterValue00 (fuel + 446) acc))
        (value_fragment0148691 (fuel + 38) (chunk0026SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 446) (SourceJson.white tail) (chunk0026Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0026_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0027_before_reader"
  err.flush

noncomputable def chunk0027LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0027SuffixChars00 : List Char := [',']
noncomputable def chunk0027Chars00 : List Char := chunk0027LeadChars00 ++ fragment0150642Chars ++ chunk0027SuffixChars00
noncomputable def chunk0027Push00 (acc : List SourceJson) : List SourceJson := fragment0150642Value :: acc

noncomputable def chunk0027AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0027_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 446)
      (SourceJson.white (chunk0027LeadChars00 ++ (fragment0150642Chars ++ rest))) acc =
      (SourceJson.value (fuel + 445) (fragment0150642Chars ++ rest)).bind
        (chunk0027AfterValue00 (fuel + 445) acc) := by rfl

theorem array_chunk0027 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 446) (SourceJson.white (chunk0027Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 445) (SourceJson.white tail) (chunk0027Push00 acc) := by
  have hinput : chunk0027Chars00 ++ tail = chunk0027LeadChars00 ++ (fragment0150642Chars ++ (chunk0027SuffixChars00 ++ tail)) := by
    simp only [chunk0027Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 446) (SourceJson.white (chunk0027Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 446)
          (SourceJson.white (chunk0027LeadChars00 ++ (fragment0150642Chars ++ (chunk0027SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 446) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 445) (fragment0150642Chars ++ (chunk0027SuffixChars00 ++ tail))).bind
        (chunk0027AfterValue00 (fuel + 445) acc) := array_chunk0027_head fuel (chunk0027SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0150642Value, chunk0027SuffixChars00 ++ tail)).bind
        (chunk0027AfterValue00 (fuel + 445) acc) :=
      congrArg (fun result => result.bind (chunk0027AfterValue00 (fuel + 445) acc))
        (value_fragment0150642 (fuel + 208) (chunk0027SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 445) (SourceJson.white tail) (chunk0027Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0027_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0028_before_reader"
  err.flush

noncomputable def chunk0028LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0028SuffixChars00 : List Char := [',']
noncomputable def chunk0028Chars00 : List Char := chunk0028LeadChars00 ++ fragment0152230Chars ++ chunk0028SuffixChars00
noncomputable def chunk0028Push00 (acc : List SourceJson) : List SourceJson := fragment0152230Value :: acc

noncomputable def chunk0028AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0028_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 445)
      (SourceJson.white (chunk0028LeadChars00 ++ (fragment0152230Chars ++ rest))) acc =
      (SourceJson.value (fuel + 444) (fragment0152230Chars ++ rest)).bind
        (chunk0028AfterValue00 (fuel + 444) acc) := by rfl

theorem array_chunk0028 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 445) (SourceJson.white (chunk0028Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 444) (SourceJson.white tail) (chunk0028Push00 acc) := by
  have hinput : chunk0028Chars00 ++ tail = chunk0028LeadChars00 ++ (fragment0152230Chars ++ (chunk0028SuffixChars00 ++ tail)) := by
    simp only [chunk0028Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 445) (SourceJson.white (chunk0028Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 445)
          (SourceJson.white (chunk0028LeadChars00 ++ (fragment0152230Chars ++ (chunk0028SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 445) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 444) (fragment0152230Chars ++ (chunk0028SuffixChars00 ++ tail))).bind
        (chunk0028AfterValue00 (fuel + 444) acc) := array_chunk0028_head fuel (chunk0028SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0152230Value, chunk0028SuffixChars00 ++ tail)).bind
        (chunk0028AfterValue00 (fuel + 444) acc) :=
      congrArg (fun result => result.bind (chunk0028AfterValue00 (fuel + 444) acc))
        (value_fragment0152230 (fuel + 43) (chunk0028SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 444) (SourceJson.white tail) (chunk0028Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0028_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0029_before_reader"
  err.flush

noncomputable def chunk0029LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0029SuffixChars00 : List Char := [',']
noncomputable def chunk0029Chars00 : List Char := chunk0029LeadChars00 ++ fragment0154158Chars ++ chunk0029SuffixChars00
noncomputable def chunk0029Push00 (acc : List SourceJson) : List SourceJson := fragment0154158Value :: acc

noncomputable def chunk0029AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0029_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 444)
      (SourceJson.white (chunk0029LeadChars00 ++ (fragment0154158Chars ++ rest))) acc =
      (SourceJson.value (fuel + 443) (fragment0154158Chars ++ rest)).bind
        (chunk0029AfterValue00 (fuel + 443) acc) := by rfl

theorem array_chunk0029 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 444) (SourceJson.white (chunk0029Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 443) (SourceJson.white tail) (chunk0029Push00 acc) := by
  have hinput : chunk0029Chars00 ++ tail = chunk0029LeadChars00 ++ (fragment0154158Chars ++ (chunk0029SuffixChars00 ++ tail)) := by
    simp only [chunk0029Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 444) (SourceJson.white (chunk0029Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 444)
          (SourceJson.white (chunk0029LeadChars00 ++ (fragment0154158Chars ++ (chunk0029SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 444) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 443) (fragment0154158Chars ++ (chunk0029SuffixChars00 ++ tail))).bind
        (chunk0029AfterValue00 (fuel + 443) acc) := array_chunk0029_head fuel (chunk0029SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0154158Value, chunk0029SuffixChars00 ++ tail)).bind
        (chunk0029AfterValue00 (fuel + 443) acc) :=
      congrArg (fun result => result.bind (chunk0029AfterValue00 (fuel + 443) acc))
        (value_fragment0154158 (fuel + 34) (chunk0029SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 443) (SourceJson.white tail) (chunk0029Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0029_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0030_before_reader"
  err.flush

noncomputable def chunk0030LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0030SuffixChars00 : List Char := [',']
noncomputable def chunk0030Chars00 : List Char := chunk0030LeadChars00 ++ fragment0156115Chars ++ chunk0030SuffixChars00
noncomputable def chunk0030Push00 (acc : List SourceJson) : List SourceJson := fragment0156115Value :: acc

noncomputable def chunk0030AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0030_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 443)
      (SourceJson.white (chunk0030LeadChars00 ++ (fragment0156115Chars ++ rest))) acc =
      (SourceJson.value (fuel + 442) (fragment0156115Chars ++ rest)).bind
        (chunk0030AfterValue00 (fuel + 442) acc) := by rfl

theorem array_chunk0030 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 443) (SourceJson.white (chunk0030Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 442) (SourceJson.white tail) (chunk0030Push00 acc) := by
  have hinput : chunk0030Chars00 ++ tail = chunk0030LeadChars00 ++ (fragment0156115Chars ++ (chunk0030SuffixChars00 ++ tail)) := by
    simp only [chunk0030Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 443) (SourceJson.white (chunk0030Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 443)
          (SourceJson.white (chunk0030LeadChars00 ++ (fragment0156115Chars ++ (chunk0030SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 443) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 442) (fragment0156115Chars ++ (chunk0030SuffixChars00 ++ tail))).bind
        (chunk0030AfterValue00 (fuel + 442) acc) := array_chunk0030_head fuel (chunk0030SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0156115Value, chunk0030SuffixChars00 ++ tail)).bind
        (chunk0030AfterValue00 (fuel + 442) acc) :=
      congrArg (fun result => result.bind (chunk0030AfterValue00 (fuel + 442) acc))
        (value_fragment0156115 (fuel + 14) (chunk0030SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 442) (SourceJson.white tail) (chunk0030Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0030_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0031_before_reader"
  err.flush

noncomputable def chunk0031LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0031SuffixChars00 : List Char := [',']
noncomputable def chunk0031Chars00 : List Char := chunk0031LeadChars00 ++ fragment0158122Chars ++ chunk0031SuffixChars00
noncomputable def chunk0031Push00 (acc : List SourceJson) : List SourceJson := fragment0158122Value :: acc

noncomputable def chunk0031AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0031_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 442)
      (SourceJson.white (chunk0031LeadChars00 ++ (fragment0158122Chars ++ rest))) acc =
      (SourceJson.value (fuel + 441) (fragment0158122Chars ++ rest)).bind
        (chunk0031AfterValue00 (fuel + 441) acc) := by rfl

theorem array_chunk0031 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 442) (SourceJson.white (chunk0031Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 441) (SourceJson.white tail) (chunk0031Push00 acc) := by
  have hinput : chunk0031Chars00 ++ tail = chunk0031LeadChars00 ++ (fragment0158122Chars ++ (chunk0031SuffixChars00 ++ tail)) := by
    simp only [chunk0031Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 442) (SourceJson.white (chunk0031Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 442)
          (SourceJson.white (chunk0031LeadChars00 ++ (fragment0158122Chars ++ (chunk0031SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 442) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 441) (fragment0158122Chars ++ (chunk0031SuffixChars00 ++ tail))).bind
        (chunk0031AfterValue00 (fuel + 441) acc) := array_chunk0031_head fuel (chunk0031SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0158122Value, chunk0031SuffixChars00 ++ tail)).bind
        (chunk0031AfterValue00 (fuel + 441) acc) :=
      congrArg (fun result => result.bind (chunk0031AfterValue00 (fuel + 441) acc))
        (value_fragment0158122 (fuel + 129) (chunk0031SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 441) (SourceJson.white tail) (chunk0031Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0031_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0024Chars00 ++ chunk0025Chars00 ++ chunk0026Chars00 ++ chunk0027Chars00 ++ chunk0028Chars00 ++ chunk0029Chars00 ++ chunk0030Chars00 ++ chunk0031Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0031Push00 (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 449) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 441) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0024Chars00 ++ (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 449) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 449) (SourceJson.white (chunk0024Chars00 ++ (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 449) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 448) (SourceJson.white (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))))) (chunk0024Push00 (acc)) := array_chunk0024 fuel (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 447) (SourceJson.white (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) (chunk0025Push00 (chunk0024Push00 (acc))) := array_chunk0025 fuel (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))) (chunk0024Push00 (acc))
    _ = SourceJson.array (fuel + 446) (SourceJson.white (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))) (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))) := array_chunk0026 fuel (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))) (chunk0025Push00 (chunk0024Push00 (acc)))
    _ = SourceJson.array (fuel + 445) (SourceJson.white (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))) (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))) := array_chunk0027 fuel (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))) (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))
    _ = SourceJson.array (fuel + 444) (SourceJson.white (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))) (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))) := array_chunk0028 fuel (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))) (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))
    _ = SourceJson.array (fuel + 443) (SourceJson.white (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))) (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))) := array_chunk0029 fuel (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))) (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))
    _ = SourceJson.array (fuel + 442) (SourceJson.white (chunk0031Chars00 ++ (tail))) (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))))) := array_chunk0030 fuel (chunk0031Chars00 ++ (tail)) (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))))
    _ = SourceJson.array (fuel + 441) (SourceJson.white tail) (blockPush acc) := array_chunk0031 fuel (tail) (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 145327).take 14534 = blockChars := by rfl

theorem block_original_split : sourceRest 145327 = blockChars ++ sourceRest 159861 := by
  calc
    sourceRest 145327 = (sourceRest 145327).take 14534 ++ (sourceRest 145327).drop 14534 :=
      (List.take_append_drop 14534 (sourceRest 145327)).symm
    _ = blockChars ++ (sourceRest 145327).drop 14534 :=
      congrArg (fun part => part ++ (sourceRest 145327).drop 14534) block_original_prefix
    _ = blockChars ++ sourceRest 159861 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 145327 14534)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 449) (SourceJson.white (sourceRest 145327)) acc =
      SourceJson.array (fuel + 441) (SourceJson.white (sourceRest 159861)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 449) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 159861) acc)

#print axioms object_fragment0145333_field_000
#print axioms object_fragment0145333_field_001
#print axioms object_fragment0145333_field_002
#print axioms object_fragment0145333_field_003
#print axioms object_fragment0145333_field_004
#print axioms object_fragment0145333_field_005
#print axioms object_fragment0145333_field_006
#print axioms object_fragment0145333_field_007
#print axioms object_fragment0145333_field_008
#print axioms object_fragment0145333_field_009
#print axioms value_fragment0145333
#print axioms object_fragment0147088_field_000
#print axioms object_fragment0147088_field_001
#print axioms object_fragment0147088_field_002
#print axioms object_fragment0147088_field_003
#print axioms object_fragment0147088_field_004
#print axioms object_fragment0147088_field_005
#print axioms object_fragment0147088_field_006
#print axioms object_fragment0147088_field_007
#print axioms object_fragment0147088_field_008
#print axioms object_fragment0147088_field_009
#print axioms value_fragment0147088
#print axioms object_fragment0148691_field_000
#print axioms object_fragment0148691_field_001
#print axioms object_fragment0148691_field_002
#print axioms object_fragment0148691_field_003
#print axioms object_fragment0148691_field_004
#print axioms object_fragment0148691_field_005
#print axioms object_fragment0148691_field_006
#print axioms object_fragment0148691_field_007
#print axioms object_fragment0148691_field_008
#print axioms object_fragment0148691_field_009
#print axioms value_fragment0148691
#print axioms object_fragment0150642_field_000
#print axioms object_fragment0150642_field_001
#print axioms object_fragment0150642_field_002
#print axioms object_fragment0150642_field_003
#print axioms object_fragment0150642_field_004
#print axioms object_fragment0150642_field_005
#print axioms object_fragment0150642_field_006
#print axioms object_fragment0150642_field_007
#print axioms object_fragment0150642_field_008
#print axioms object_fragment0150642_field_009
#print axioms value_fragment0150642
#print axioms object_fragment0152230_field_000
#print axioms object_fragment0152230_field_001
#print axioms object_fragment0152230_field_002
#print axioms object_fragment0152230_field_003
#print axioms object_fragment0152230_field_004
#print axioms object_fragment0152230_field_005
#print axioms object_fragment0152230_field_006
#print axioms object_fragment0152230_field_007
#print axioms object_fragment0152230_field_008
#print axioms object_fragment0152230_field_009
#print axioms value_fragment0152230
#print axioms object_fragment0154158_field_000
#print axioms object_fragment0154158_field_001
#print axioms object_fragment0154158_field_002
#print axioms object_fragment0154158_field_003
#print axioms object_fragment0154158_field_004
#print axioms object_fragment0154158_field_005
#print axioms object_fragment0154158_field_006
#print axioms object_fragment0154158_field_007
#print axioms object_fragment0154158_field_008
#print axioms object_fragment0154158_field_009
#print axioms value_fragment0154158
#print axioms object_fragment0156115_field_000
#print axioms object_fragment0156115_field_001
#print axioms object_fragment0156115_field_002
#print axioms object_fragment0156115_field_003
#print axioms object_fragment0156115_field_004
#print axioms object_fragment0156115_field_005
#print axioms object_fragment0156115_field_006
#print axioms object_fragment0156115_field_007
#print axioms object_fragment0156115_field_008
#print axioms object_fragment0156115_field_009
#print axioms value_fragment0156115
#print axioms object_fragment0158122_field_000
#print axioms object_fragment0158122_field_001
#print axioms object_fragment0158122_field_002
#print axioms object_fragment0158122_field_003
#print axioms object_fragment0158122_field_004
#print axioms object_fragment0158122_field_005
#print axioms object_fragment0158122_field_006
#print axioms object_fragment0158122_field_007
#print axioms object_fragment0158122_field_008
#print axioms object_fragment0158122_field_009
#print axioms value_fragment0158122
#print axioms array_chunk0024_head
#print axioms array_chunk0024
#print axioms array_chunk0025_head
#print axioms array_chunk0025
#print axioms array_chunk0026_head
#print axioms array_chunk0026
#print axioms array_chunk0027_head
#print axioms array_chunk0027
#print axioms array_chunk0028_head
#print axioms array_chunk0028
#print axioms array_chunk0029_head
#print axioms array_chunk0029
#print axioms array_chunk0030_head
#print axioms array_chunk0030
#print axioms array_chunk0031_head
#print axioms array_chunk0031
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock003

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
