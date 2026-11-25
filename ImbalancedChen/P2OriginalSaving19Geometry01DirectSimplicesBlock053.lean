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

namespace SimplicesBlock053

noncomputable def fragment0404176Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0404176Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0404176Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '4'])
noncomputable def fragment0404176Acc00100 : List (String × SourceJson) := (fragment0404176Field000Key00, fragment0404176Field000Value00) :: fragment0404176Acc00000
noncomputable def fragment0404176Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '4', ',']

theorem object_fragment0404176_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 221) (SourceJson.white (fragment0404176Field000Chars00 ++ tail)) fragment0404176Acc00000 =
      SourceJson.object (fuel + 220) (SourceJson.white tail) fragment0404176Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0404176_object_field_000"
  err.flush

noncomputable def fragment0404176Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0404176Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['0'])]
noncomputable def fragment0404176Acc00200 : List (String × SourceJson) := (fragment0404176Field001Key00, fragment0404176Field001Value00) :: fragment0404176Acc00100
noncomputable def fragment0404176Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0404176_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment0404176Field001Chars00 ++ tail)) fragment0404176Acc00100 =
      SourceJson.object (fuel + 219) (SourceJson.white tail) fragment0404176Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0404176_object_field_001"
  err.flush

noncomputable def fragment0404176Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0404176Field002Value00 : SourceJson := .str (String.ofList ['2', '1', '1', '7', '2', '8', '0', '4', '2', '9', '3', '8', '1', '8', '0', '0', '0', '3', '5', '3', '1', '6', '2', '4', '8', '6', '4', '6', '0', '0', '9', '7', '9', '9', '0', '1', '5', '1', '5', '6', '9', '1', '/', '1', '2', '1', '8', '1', '7', '5', '3', '5', '2', '1', '5', '9', '1', '0', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0404176Acc00300 : List (String × SourceJson) := (fragment0404176Field002Key00, fragment0404176Field002Value00) :: fragment0404176Acc00200
noncomputable def fragment0404176Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '1', '1', '7', '2', '8', '0', '4', '2', '9', '3', '8', '1', '8', '0', '0', '0', '3', '5', '3', '1', '6', '2', '4', '8', '6', '4', '6', '0', '0', '9', '7', '9', '9', '0', '1', '5', '1', '5', '6', '9', '1', '/', '1', '2', '1', '8', '1', '7', '5', '3', '5', '2', '1', '5', '9', '1', '0', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0404176_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 219) (SourceJson.white (fragment0404176Field002Chars00 ++ tail)) fragment0404176Acc00200 =
      SourceJson.object (fuel + 218) (SourceJson.white tail) fragment0404176Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0404176_object_field_002"
  err.flush

noncomputable def fragment0404176Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0404176Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0404176Acc00400 : List (String × SourceJson) := (fragment0404176Field003Key00, fragment0404176Field003Value00) :: fragment0404176Acc00300
noncomputable def fragment0404176Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0404176_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0404176Field003Chars00 ++ tail)) fragment0404176Acc00300 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment0404176Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0404176_object_field_003"
  err.flush

noncomputable def fragment0404176Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0404176Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '6', '3', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['8', '0', '7', '/', '1', '7', '7', '9', '2'])]
noncomputable def fragment0404176Acc00500 : List (String × SourceJson) := (fragment0404176Field004Key00, fragment0404176Field004Value00) :: fragment0404176Acc00400
noncomputable def fragment0404176Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '6', '3', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '7', '/', '1', '7', '7', '9', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0404176_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0404176Field004Chars00 ++ tail)) fragment0404176Acc00400 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0404176Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0404176_object_field_004"
  err.flush

noncomputable def fragment0404176Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0404176Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '3', '2', '4', '3', '1', '8', '1', '1', '7', '/', '2', '8', '8', '8', '5', '9', '3', '7', '5', '0', '0']), .str (String.ofList ['1', '4', '9', '1', '6', '1', '2', '2', '4', '1', '2', '3', '/', '1', '8', '4', '8', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '2', '7', '7', '6', '8', '8', '9', '5', '8', '0', '7', '/', '1', '6', '6', '3', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '0', '6', '8', '0', '0', '4', '9', '1', '1', '3', '/', '2', '7', '7', '3', '0', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '5', '7', '6', '8', '0', '4', '9', '1', '5', '5', '9', '/', '3', '3', '2', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '8', '6', '8', '0', '7', '4', '7', '3', '2', '1', '/', '1', '6', '6', '3', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '9', '7', '2', '1', '6', '2', '1', '7', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '1', '3', '8', '9', '2', '0', '6', '0', '2', '1', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '1', '3', '8', '8', '7', '6', '2', '3', '3', '3', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '1', '0', '0', '9', '4', '4', '1', '1', '5', '9', '/', '1', '6', '6', '3', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0404176Acc00600 : List (String × SourceJson) := (fragment0404176Field005Key00, fragment0404176Field005Value00) :: fragment0404176Acc00500
noncomputable def fragment0404176Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '4', '3', '1', '8', '1', '1', '7', '/', '2', '8', '8', '8', '5', '9', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '1', '6', '1', '2', '2', '4', '1', '2', '3', '/', '1', '8', '4', '8', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '2', '7', '7', '6', '8', '8', '9', '5', '8', '0', '7', '/', '1', '6', '6', '3', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '0', '6', '8', '0', '0', '4', '9', '1', '1', '3', '/', '2', '7', '7', '3', '0', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '7', '6', '8', '0', '4', '9', '1', '5', '5', '9', '/', '3', '3', '2', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '8', '6', '8', '0', '7', '4', '7', '3', '2', '1', '/', '1', '6', '6', '3', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '9', '7', '2', '1', '6', '2', '1', '7', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '1', '3', '8', '9', '2', '0', '6', '0', '2', '1', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '1', '3', '8', '8', '7', '6', '2', '3', '3', '3', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '1', '0', '0', '9', '4', '4', '1', '1', '5', '9', '/', '1', '6', '6', '3', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0404176_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0404176Field005Chars00 ++ tail)) fragment0404176Acc00500 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment0404176Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0404176_object_field_005"
  err.flush

noncomputable def fragment0404176Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0404176Field006Value00 : SourceJson := .str (String.ofList ['2', '0', '6', '2', '4', '6', '4', '8', '8', '5', '9', '7', '7', '2', '7', '6', '9', '8', '5', '1', '2', '1', '9', '2', '5', '0', '9', '5', '0', '6', '4', '0', '6', '3', '7', '2', '2', '5', '7', '4', '1', '0', '3', '6', '6', '2', '8', '6', '4', '/', '1', '1', '3', '6', '2', '2', '7', '8', '0', '6', '7', '9', '4', '3', '9', '2', '9', '6', '6', '2', '1', '1', '0', '4', '4', '1', '8', '0', '9', '2', '1', '8', '9', '0', '1', '6', '6', '5', '7', '9', '3', '1', '7', '3', '6', '5', '6', '7', '9', '1', '4', '1', '7', '0', '0', '7', '4', '4', '6', '2', '8', '9', '0', '6', '2', '5'])
noncomputable def fragment0404176Acc00700 : List (String × SourceJson) := (fragment0404176Field006Key00, fragment0404176Field006Value00) :: fragment0404176Acc00600
noncomputable def fragment0404176Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '0', '6', '2', '4', '6', '4', '8', '8', '5', '9', '7', '7', '2', '7', '6', '9', '8', '5', '1', '2', '1', '9', '2', '5', '0', '9', '5', '0', '6', '4', '0', '6', '3', '7', '2', '2', '5', '7', '4', '1', '0', '3', '6', '6', '2', '8', '6', '4', '/', '1', '1', '3', '6', '2', '2', '7', '8', '0', '6', '7', '9', '4', '3', '9', '2', '9', '6', '6', '2', '1', '1', '0', '4', '4', '1', '8', '0', '9', '2', '1', '8', '9', '0', '1', '6', '6', '5', '7', '9', '3', '1', '7', '3', '6', '5', '6', '7', '9', '1', '4', '1', '7', '0', '0', '7', '4', '4', '6', '2', '8', '9', '0', '6', '2', '5', '"', ',']

theorem object_fragment0404176_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0404176Field006Chars00 ++ tail)) fragment0404176Acc00600 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment0404176Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0404176_object_field_006"
  err.flush

noncomputable def fragment0404176Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0404176Field007Value00 : SourceJson := .str (String.ofList ['2', '1', '6', '8', '4', '1', '3', '9', '3', '0', '3', '9', '8', '0', '8', '2', '5', '2', '9', '6', '6', '4', '7', '1', '9', '0', '4', '5', '1', '3', '9', '8', '5', '6', '6', '1', '6', '8', '5', '6', '1', '7', '4', '4', '6', '6', '7', '8', '3', '2', '8', '1', '7', '3', '6', '7', '4', '9', '7', '0', '4', '9', '1', '2', '8', '0', '8', '6', '2', '1', '2', '7', '9', '3', '0', '7', '5', '4', '9', '4', '3', '8', '4', '7', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '6', '1', '8', '8', '3', '7', '4', '5', '9', '4', '5', '7', '7', '3', '2', '5', '0', '6', '6', '1', '5', '9', '6', '1', '4', '1', '2', '2', '4', '0', '3', '0', '6', '9', '7', '7', '5', '7', '0', '8', '9', '4', '0', '0', '8', '8', '4', '7', '7', '3', '5', '6', '9', '4', '5', '0', '0', '2', '1', '8', '7', '6', '0', '5', '7', '2', '1', '7', '4', '7', '9', '8', '6', '4', '3', '0', '9', '1', '1', '3', '0', '4', '4', '3', '5', '0', '7', '2', '1', '7', '8', '5', '5', '4', '1', '0', '4', '4', '0', '9', '6', '2', '1', '0', '9', '2', '4', '9', '1', '0', '1'])
noncomputable def fragment0404176Acc00800 : List (String × SourceJson) := (fragment0404176Field007Key00, fragment0404176Field007Value00) :: fragment0404176Acc00700
noncomputable def fragment0404176Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '6', '8', '4', '1', '3', '9', '3', '0', '3', '9', '8', '0', '8', '2', '5', '2', '9', '6', '6', '4', '7', '1', '9', '0', '4', '5', '1', '3', '9', '8', '5', '6', '6', '1', '6', '8', '5', '6', '1', '7', '4', '4', '6', '6', '7', '8', '3', '2', '8', '1', '7', '3', '6', '7', '4', '9', '7', '0', '4', '9', '1', '2', '8', '0', '8', '6', '2', '1', '2', '7', '9', '3', '0', '7', '5', '4', '9', '4', '3', '8', '4', '7', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '6', '1', '8', '8', '3', '7', '4', '5', '9', '4', '5', '7', '7', '3', '2', '5', '0', '6', '6', '1', '5', '9', '6', '1', '4', '1', '2', '2', '4', '0', '3', '0', '6', '9', '7', '7', '5', '7', '0', '8', '9', '4', '0', '0', '8', '8', '4', '7', '7', '3', '5', '6', '9', '4', '5', '0', '0', '2', '1', '8', '7', '6', '0', '5', '7', '2', '1', '7', '4', '7', '9', '8', '6', '4', '3', '0', '9', '1', '1', '3', '0', '4', '4', '3', '5', '0', '7', '2', '1', '7', '8', '5', '5', '4', '1', '0', '4', '4', '0', '9', '6', '2', '1', '0', '9', '2', '4', '9', '1', '0', '1', '"', ',']

theorem object_fragment0404176_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment0404176Field007Chars00 ++ tail)) fragment0404176Acc00700 =
      SourceJson.object (fuel + 213) (SourceJson.white tail) fragment0404176Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0404176_object_field_007"
  err.flush

noncomputable def fragment0404176Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0404176Field008Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '8', '1', '3', '8', '5', '6', '8', '5', '9', '5'])
noncomputable def fragment0404176Acc00900 : List (String × SourceJson) := (fragment0404176Field008Key00, fragment0404176Field008Value00) :: fragment0404176Acc00800
noncomputable def fragment0404176Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '3', '8', '1', '3', '8', '5', '6', '8', '5', '9', '5', '"', ',']

theorem object_fragment0404176_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0404176Field008Chars00 ++ tail)) fragment0404176Acc00800 =
      SourceJson.object (fuel + 212) (SourceJson.white tail) fragment0404176Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0404176_object_field_008"
  err.flush

noncomputable def fragment0404176Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0404176Field009Value00 : SourceJson := .str (String.ofList ['9', '7', '5', '0', '8', '9', '5', '9', '7', '5', '4', '6', '3'])
noncomputable def fragment0404176Acc01000 : List (String × SourceJson) := (fragment0404176Field009Key00, fragment0404176Field009Value00) :: fragment0404176Acc00900
noncomputable def fragment0404176Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '7', '5', '0', '8', '9', '5', '9', '7', '5', '4', '6', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0404176_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 212) (SourceJson.white (fragment0404176Field009Chars00 ++ tail)) fragment0404176Acc00900 =
      .ok (.obj (fragment0404176Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0404176_object_field_009"
  err.flush

noncomputable def fragment0404176Chars : List Char := '{' :: (fragment0404176Field000Chars00 ++ fragment0404176Field001Chars00 ++ fragment0404176Field002Chars00 ++ fragment0404176Field003Chars00 ++ fragment0404176Field004Chars00 ++ fragment0404176Field005Chars00 ++ fragment0404176Field006Chars00 ++ fragment0404176Field007Chars00 ++ fragment0404176Field008Chars00 ++ fragment0404176Field009Chars00)
noncomputable def fragment0404176Value : SourceJson := .obj (fragment0404176Acc01000.reverse)

theorem value_fragment0404176 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 222) (fragment0404176Chars ++ tail) =
      .ok (fragment0404176Value, tail) := by
  have hinput : fragment0404176Chars ++ tail = '{' :: (fragment0404176Field000Chars00 ++ (fragment0404176Field001Chars00 ++ (fragment0404176Field002Chars00 ++ (fragment0404176Field003Chars00 ++ (fragment0404176Field004Chars00 ++ (fragment0404176Field005Chars00 ++ (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0404176Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 222) (fragment0404176Chars ++ tail) =
        SourceJson.value (fuel + 222) ('{' :: (fragment0404176Field000Chars00 ++ (fragment0404176Field001Chars00 ++ (fragment0404176Field002Chars00 ++ (fragment0404176Field003Chars00 ++ (fragment0404176Field004Chars00 ++ (fragment0404176Field005Chars00 ++ (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 222)) hinput
    _ = SourceJson.object (fuel + 221) (SourceJson.white (fragment0404176Field000Chars00 ++ (fragment0404176Field001Chars00 ++ (fragment0404176Field002Chars00 ++ (fragment0404176Field003Chars00 ++ (fragment0404176Field004Chars00 ++ (fragment0404176Field005Chars00 ++ (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail)))))))))))) fragment0404176Acc00000 := by rfl
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment0404176Field001Chars00 ++ (fragment0404176Field002Chars00 ++ (fragment0404176Field003Chars00 ++ (fragment0404176Field004Chars00 ++ (fragment0404176Field005Chars00 ++ (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail))))))))))) fragment0404176Acc00100 := object_fragment0404176_field_000 fuel (fragment0404176Field001Chars00 ++ (fragment0404176Field002Chars00 ++ (fragment0404176Field003Chars00 ++ (fragment0404176Field004Chars00 ++ (fragment0404176Field005Chars00 ++ (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 219) (SourceJson.white (fragment0404176Field002Chars00 ++ (fragment0404176Field003Chars00 ++ (fragment0404176Field004Chars00 ++ (fragment0404176Field005Chars00 ++ (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail)))))))))) fragment0404176Acc00200 := object_fragment0404176_field_001 fuel (fragment0404176Field002Chars00 ++ (fragment0404176Field003Chars00 ++ (fragment0404176Field004Chars00 ++ (fragment0404176Field005Chars00 ++ (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0404176Field003Chars00 ++ (fragment0404176Field004Chars00 ++ (fragment0404176Field005Chars00 ++ (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail))))))))) fragment0404176Acc00300 := object_fragment0404176_field_002 fuel (fragment0404176Field003Chars00 ++ (fragment0404176Field004Chars00 ++ (fragment0404176Field005Chars00 ++ (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0404176Field004Chars00 ++ (fragment0404176Field005Chars00 ++ (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail)))))))) fragment0404176Acc00400 := object_fragment0404176_field_003 fuel (fragment0404176Field004Chars00 ++ (fragment0404176Field005Chars00 ++ (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0404176Field005Chars00 ++ (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail))))))) fragment0404176Acc00500 := object_fragment0404176_field_004 fuel (fragment0404176Field005Chars00 ++ (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail)))))) fragment0404176Acc00600 := object_fragment0404176_field_005 fuel (fragment0404176Field006Chars00 ++ (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail))))) fragment0404176Acc00700 := object_fragment0404176_field_006 fuel (fragment0404176Field007Chars00 ++ (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail)))) fragment0404176Acc00800 := object_fragment0404176_field_007 fuel (fragment0404176Field008Chars00 ++ (fragment0404176Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 212) (SourceJson.white (fragment0404176Field009Chars00 ++ (tail))) fragment0404176Acc00900 := object_fragment0404176_field_008 fuel (fragment0404176Field009Chars00 ++ (tail))
    _ = .ok (fragment0404176Value, tail) := object_fragment0404176_field_009 fuel (tail)

noncomputable def fragment0405738Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0405738Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0405738Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '5'])
noncomputable def fragment0405738Acc00100 : List (String × SourceJson) := (fragment0405738Field000Key00, fragment0405738Field000Value00) :: fragment0405738Acc00000
noncomputable def fragment0405738Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '5', ',']

theorem object_fragment0405738_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment0405738Field000Chars00 ++ tail)) fragment0405738Acc00000 =
      SourceJson.object (fuel + 221) (SourceJson.white tail) fragment0405738Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0405738_object_field_000"
  err.flush

noncomputable def fragment0405738Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0405738Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '5']), .number (String.ofList ['7']), .number (String.ofList ['0'])]
noncomputable def fragment0405738Acc00200 : List (String × SourceJson) := (fragment0405738Field001Key00, fragment0405738Field001Value00) :: fragment0405738Acc00100
noncomputable def fragment0405738Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0405738_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 221) (SourceJson.white (fragment0405738Field001Chars00 ++ tail)) fragment0405738Acc00100 =
      SourceJson.object (fuel + 220) (SourceJson.white tail) fragment0405738Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0405738_object_field_001"
  err.flush

noncomputable def fragment0405738Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0405738Field002Value00 : SourceJson := .str (String.ofList ['7', '4', '0', '2', '4', '6', '0', '4', '4', '5', '5', '9', '4', '2', '2', '4', '2', '1', '1', '3', '7', '5', '6', '8', '0', '5', '5', '4', '6', '0', '7', '1', '5', '3', '1', '8', '8', '5', '8', '7', '1', '/', '1', '2', '5', '2', '9', '8', '0', '3', '6', '2', '2', '2', '0', '7', '9', '7', '9', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0405738Acc00300 : List (String × SourceJson) := (fragment0405738Field002Key00, fragment0405738Field002Value00) :: fragment0405738Acc00200
noncomputable def fragment0405738Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '4', '0', '2', '4', '6', '0', '4', '4', '5', '5', '9', '4', '2', '2', '4', '2', '1', '1', '3', '7', '5', '6', '8', '0', '5', '5', '4', '6', '0', '7', '1', '5', '3', '1', '8', '8', '5', '8', '7', '1', '/', '1', '2', '5', '2', '9', '8', '0', '3', '6', '2', '2', '2', '0', '7', '9', '7', '9', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0405738_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment0405738Field002Chars00 ++ tail)) fragment0405738Acc00200 =
      SourceJson.object (fuel + 219) (SourceJson.white tail) fragment0405738Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0405738_object_field_002"
  err.flush

noncomputable def fragment0405738Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0405738Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0405738Acc00400 : List (String × SourceJson) := (fragment0405738Field003Key00, fragment0405738Field003Value00) :: fragment0405738Acc00300
noncomputable def fragment0405738Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0405738_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 219) (SourceJson.white (fragment0405738Field003Chars00 ++ tail)) fragment0405738Acc00300 =
      SourceJson.object (fuel + 218) (SourceJson.white tail) fragment0405738Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0405738_object_field_003"
  err.flush

noncomputable def fragment0405738Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0405738Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '6', '3', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0405738Acc00500 : List (String × SourceJson) := (fragment0405738Field004Key00, fragment0405738Field004Value00) :: fragment0405738Acc00400
noncomputable def fragment0405738Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '6', '3', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0405738_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0405738Field004Chars00 ++ tail)) fragment0405738Acc00400 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment0405738Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0405738_object_field_004"
  err.flush

noncomputable def fragment0405738Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0405738Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '5', '2', '4', '4', '1', '3', '0', '3', '9', '7', '/', '8', '3', '1', '9', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '1', '7', '0', '5', '2', '7', '7', '9', '3', '1', '/', '3', '3', '2', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '6', '1', '8', '1', '2', '4', '3', '5', '7', '9', '1', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '6', '1', '8', '6', '5', '9', '7', '0', '3', '/', '4', '4', '3', '6', '8', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '9', '4', '0', '4', '6', '1', '6', '7', '7', '1', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '3', '5', '2', '3', '9', '3', '1', '0', '3', '/', '2', '4', '9', '5', '7', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '2', '0', '6', '1', '1', '4', '6', '5', '1', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '3', '0', '1', '3', '8', '8', '6', '3', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '2', '9', '8', '0', '6', '0', '9', '7', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '9', '5', '7', '0', '1', '9', '2', '9', '8', '3', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0405738Acc00600 : List (String × SourceJson) := (fragment0405738Field005Key00, fragment0405738Field005Value00) :: fragment0405738Acc00500
noncomputable def fragment0405738Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '2', '4', '4', '1', '3', '0', '3', '9', '7', '/', '8', '3', '1', '9', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '1', '7', '0', '5', '2', '7', '7', '9', '3', '1', '/', '3', '3', '2', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '1', '8', '1', '2', '4', '3', '5', '7', '9', '1', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '6', '1', '8', '6', '5', '9', '7', '0', '3', '/', '4', '4', '3', '6', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '9', '4', '0', '4', '6', '1', '6', '7', '7', '1', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '3', '5', '2', '3', '9', '3', '1', '0', '3', '/', '2', '4', '9', '5', '7', '4', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '2', '0', '6', '1', '1', '4', '6', '5', '1', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '3', '0', '1', '3', '8', '8', '6', '3', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '2', '9', '8', '0', '6', '0', '9', '7', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '9', '5', '7', '0', '1', '9', '2', '9', '8', '3', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0405738_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0405738Field005Chars00 ++ tail)) fragment0405738Acc00500 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0405738Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0405738_object_field_005"
  err.flush

noncomputable def fragment0405738Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0405738Field006Value00 : SourceJson := .str (String.ofList ['6', '2', '1', '6', '2', '1', '8', '7', '1', '1', '7', '6', '0', '3', '1', '7', '2', '2', '7', '7', '8', '6', '9', '3', '8', '5', '6', '4', '9', '3', '1', '5', '4', '8', '1', '3', '3', '9', '6', '1', '9', '4', '4', '3', '2', '4', '/', '1', '0', '2', '1', '9', '0', '5', '9', '1', '3', '8', '0', '1', '0', '6', '5', '9', '2', '6', '5', '4', '1', '6', '0', '3', '7', '5', '0', '9', '3', '0', '8', '1', '7', '7', '0', '8', '5', '6', '6', '1', '3', '7', '9', '4', '4', '5', '2', '2', '4', '3', '9', '6', '5', '9', '3', '6', '5', '2', '3', '4', '3', '7', '5'])
noncomputable def fragment0405738Acc00700 : List (String × SourceJson) := (fragment0405738Field006Key00, fragment0405738Field006Value00) :: fragment0405738Acc00600
noncomputable def fragment0405738Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '2', '1', '6', '2', '1', '8', '7', '1', '1', '7', '6', '0', '3', '1', '7', '2', '2', '7', '7', '8', '6', '9', '3', '8', '5', '6', '4', '9', '3', '1', '5', '4', '8', '1', '3', '3', '9', '6', '1', '9', '4', '4', '3', '2', '4', '/', '1', '0', '2', '1', '9', '0', '5', '9', '1', '3', '8', '0', '1', '0', '6', '5', '9', '2', '6', '5', '4', '1', '6', '0', '3', '7', '5', '0', '9', '3', '0', '8', '1', '7', '7', '0', '8', '5', '6', '6', '1', '3', '7', '9', '4', '4', '5', '2', '2', '4', '3', '9', '6', '5', '9', '3', '6', '5', '2', '3', '4', '3', '7', '5', '"', ',']

theorem object_fragment0405738_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0405738Field006Chars00 ++ tail)) fragment0405738Acc00600 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment0405738Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0405738_object_field_006"
  err.flush

noncomputable def fragment0405738Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0405738Field007Value00 : SourceJson := .str (String.ofList ['4', '3', '6', '2', '0', '4', '0', '7', '9', '9', '3', '5', '7', '8', '8', '6', '5', '1', '7', '2', '4', '9', '1', '0', '7', '4', '4', '1', '7', '9', '8', '3', '1', '4', '6', '6', '5', '3', '8', '8', '7', '2', '2', '9', '2', '0', '2', '5', '8', '3', '4', '2', '3', '8', '4', '2', '6', '6', '1', '9', '4', '9', '3', '7', '0', '8', '5', '6', '0', '7', '0', '2', '6', '3', '4', '2', '8', '2', '1', '0', '9', '9', '5', '3', '7', '9', '8', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '/', '1', '0', '6', '3', '9', '4', '9', '1', '2', '9', '0', '2', '2', '2', '2', '7', '2', '0', '7', '8', '4', '8', '7', '4', '8', '3', '5', '7', '8', '8', '3', '7', '9', '0', '0', '3', '3', '7', '6', '9', '0', '6', '9', '7', '2', '9', '6', '5', '8', '3', '4', '0', '8', '2', '6', '7', '8', '3', '4', '5', '3', '2', '2', '4', '4', '4', '0', '9', '0', '2', '0', '3', '9', '0', '7', '1', '2', '8', '6', '3', '9', '7', '2', '1', '5', '6', '3', '9', '8', '5', '5', '8', '2', '6', '5', '9', '8', '2', '4', '5', '4', '6', '7', '4', '3', '1', '5', '5', '1', '4', '7', '8', '0', '9'])
noncomputable def fragment0405738Acc00800 : List (String × SourceJson) := (fragment0405738Field007Key00, fragment0405738Field007Value00) :: fragment0405738Acc00700
noncomputable def fragment0405738Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '3', '6', '2', '0', '4', '0', '7', '9', '9', '3', '5', '7', '8', '8', '6', '5', '1', '7', '2', '4', '9', '1', '0', '7', '4', '4', '1', '7', '9', '8', '3', '1', '4', '6', '6', '5', '3', '8', '8', '7', '2', '2', '9', '2', '0', '2', '5', '8', '3', '4', '2', '3', '8', '4', '2', '6', '6', '1', '9', '4', '9', '3', '7', '0', '8', '5', '6', '0', '7', '0', '2', '6', '3', '4', '2', '8', '2', '1', '0', '9', '9', '5', '3', '7', '9', '8', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '/', '1', '0', '6', '3', '9', '4', '9', '1', '2', '9', '0', '2', '2', '2', '2', '7', '2', '0', '7', '8', '4', '8', '7', '4', '8', '3', '5', '7', '8', '8', '3', '7', '9', '0', '0', '3', '3', '7', '6', '9', '0', '6', '9', '7', '2', '9', '6', '5', '8', '3', '4', '0', '8', '2', '6', '7', '8', '3', '4', '5', '3', '2', '2', '4', '4', '4', '0', '9', '0', '2', '0', '3', '9', '0', '7', '1', '2', '8', '6', '3', '9', '7', '2', '1', '5', '6', '3', '9', '8', '5', '5', '8', '2', '6', '5', '9', '8', '2', '4', '5', '4', '6', '7', '4', '3', '1', '5', '5', '1', '4', '7', '8', '0', '9', '"', ',']

theorem object_fragment0405738_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0405738Field007Chars00 ++ tail)) fragment0405738Acc00700 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment0405738Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0405738_object_field_007"
  err.flush

noncomputable def fragment0405738Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0405738Field008Value00 : SourceJson := .str (String.ofList ['4', '8', '1', '9', '4', '2', '2', '0', '1', '9', '8', '5'])
noncomputable def fragment0405738Acc00900 : List (String × SourceJson) := (fragment0405738Field008Key00, fragment0405738Field008Value00) :: fragment0405738Acc00800
noncomputable def fragment0405738Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '8', '1', '9', '4', '2', '2', '0', '1', '9', '8', '5', '"', ',']

theorem object_fragment0405738_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment0405738Field008Chars00 ++ tail)) fragment0405738Acc00800 =
      SourceJson.object (fuel + 213) (SourceJson.white tail) fragment0405738Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0405738_object_field_008"
  err.flush

noncomputable def fragment0405738Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0405738Field009Value00 : SourceJson := .str (String.ofList ['3', '2', '4', '8', '2', '4', '2', '4', '9', '5', '0', '4', '2'])
noncomputable def fragment0405738Acc01000 : List (String × SourceJson) := (fragment0405738Field009Key00, fragment0405738Field009Value00) :: fragment0405738Acc00900
noncomputable def fragment0405738Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '4', '8', '2', '4', '2', '4', '9', '5', '0', '4', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0405738_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0405738Field009Chars00 ++ tail)) fragment0405738Acc00900 =
      .ok (.obj (fragment0405738Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0405738_object_field_009"
  err.flush

noncomputable def fragment0405738Chars : List Char := '{' :: (fragment0405738Field000Chars00 ++ fragment0405738Field001Chars00 ++ fragment0405738Field002Chars00 ++ fragment0405738Field003Chars00 ++ fragment0405738Field004Chars00 ++ fragment0405738Field005Chars00 ++ fragment0405738Field006Chars00 ++ fragment0405738Field007Chars00 ++ fragment0405738Field008Chars00 ++ fragment0405738Field009Chars00)
noncomputable def fragment0405738Value : SourceJson := .obj (fragment0405738Acc01000.reverse)

theorem value_fragment0405738 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 223) (fragment0405738Chars ++ tail) =
      .ok (fragment0405738Value, tail) := by
  have hinput : fragment0405738Chars ++ tail = '{' :: (fragment0405738Field000Chars00 ++ (fragment0405738Field001Chars00 ++ (fragment0405738Field002Chars00 ++ (fragment0405738Field003Chars00 ++ (fragment0405738Field004Chars00 ++ (fragment0405738Field005Chars00 ++ (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0405738Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 223) (fragment0405738Chars ++ tail) =
        SourceJson.value (fuel + 223) ('{' :: (fragment0405738Field000Chars00 ++ (fragment0405738Field001Chars00 ++ (fragment0405738Field002Chars00 ++ (fragment0405738Field003Chars00 ++ (fragment0405738Field004Chars00 ++ (fragment0405738Field005Chars00 ++ (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 223)) hinput
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment0405738Field000Chars00 ++ (fragment0405738Field001Chars00 ++ (fragment0405738Field002Chars00 ++ (fragment0405738Field003Chars00 ++ (fragment0405738Field004Chars00 ++ (fragment0405738Field005Chars00 ++ (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail)))))))))))) fragment0405738Acc00000 := by rfl
    _ = SourceJson.object (fuel + 221) (SourceJson.white (fragment0405738Field001Chars00 ++ (fragment0405738Field002Chars00 ++ (fragment0405738Field003Chars00 ++ (fragment0405738Field004Chars00 ++ (fragment0405738Field005Chars00 ++ (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail))))))))))) fragment0405738Acc00100 := object_fragment0405738_field_000 fuel (fragment0405738Field001Chars00 ++ (fragment0405738Field002Chars00 ++ (fragment0405738Field003Chars00 ++ (fragment0405738Field004Chars00 ++ (fragment0405738Field005Chars00 ++ (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment0405738Field002Chars00 ++ (fragment0405738Field003Chars00 ++ (fragment0405738Field004Chars00 ++ (fragment0405738Field005Chars00 ++ (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail)))))))))) fragment0405738Acc00200 := object_fragment0405738_field_001 fuel (fragment0405738Field002Chars00 ++ (fragment0405738Field003Chars00 ++ (fragment0405738Field004Chars00 ++ (fragment0405738Field005Chars00 ++ (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 219) (SourceJson.white (fragment0405738Field003Chars00 ++ (fragment0405738Field004Chars00 ++ (fragment0405738Field005Chars00 ++ (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail))))))))) fragment0405738Acc00300 := object_fragment0405738_field_002 fuel (fragment0405738Field003Chars00 ++ (fragment0405738Field004Chars00 ++ (fragment0405738Field005Chars00 ++ (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0405738Field004Chars00 ++ (fragment0405738Field005Chars00 ++ (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail)))))))) fragment0405738Acc00400 := object_fragment0405738_field_003 fuel (fragment0405738Field004Chars00 ++ (fragment0405738Field005Chars00 ++ (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0405738Field005Chars00 ++ (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail))))))) fragment0405738Acc00500 := object_fragment0405738_field_004 fuel (fragment0405738Field005Chars00 ++ (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail)))))) fragment0405738Acc00600 := object_fragment0405738_field_005 fuel (fragment0405738Field006Chars00 ++ (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail))))) fragment0405738Acc00700 := object_fragment0405738_field_006 fuel (fragment0405738Field007Chars00 ++ (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail)))) fragment0405738Acc00800 := object_fragment0405738_field_007 fuel (fragment0405738Field008Chars00 ++ (fragment0405738Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0405738Field009Chars00 ++ (tail))) fragment0405738Acc00900 := object_fragment0405738_field_008 fuel (fragment0405738Field009Chars00 ++ (tail))
    _ = .ok (fragment0405738Value, tail) := object_fragment0405738_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0104_before_reader"
  err.flush

noncomputable def chunk0104LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0104SuffixChars00 : List Char := [',']
noncomputable def chunk0104Chars00 : List Char := chunk0104LeadChars00 ++ fragment0404176Chars ++ chunk0104SuffixChars00
noncomputable def chunk0104Push00 (acc : List SourceJson) : List SourceJson := fragment0404176Value :: acc

noncomputable def chunk0104AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0104_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 500)
      (SourceJson.white (chunk0104LeadChars00 ++ (fragment0404176Chars ++ rest))) acc =
      (SourceJson.value (fuel + 499) (fragment0404176Chars ++ rest)).bind
        (chunk0104AfterValue00 (fuel + 499) acc) := by rfl

theorem array_chunk0104 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 500) (SourceJson.white (chunk0104Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 499) (SourceJson.white tail) (chunk0104Push00 acc) := by
  have hinput : chunk0104Chars00 ++ tail = chunk0104LeadChars00 ++ (fragment0404176Chars ++ (chunk0104SuffixChars00 ++ tail)) := by
    simp only [chunk0104Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 500) (SourceJson.white (chunk0104Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 500)
          (SourceJson.white (chunk0104LeadChars00 ++ (fragment0404176Chars ++ (chunk0104SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 500) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 499) (fragment0404176Chars ++ (chunk0104SuffixChars00 ++ tail))).bind
        (chunk0104AfterValue00 (fuel + 499) acc) := array_chunk0104_head fuel (chunk0104SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0404176Value, chunk0104SuffixChars00 ++ tail)).bind
        (chunk0104AfterValue00 (fuel + 499) acc) :=
      congrArg (fun result => result.bind (chunk0104AfterValue00 (fuel + 499) acc))
        (value_fragment0404176 (fuel + 277) (chunk0104SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 499) (SourceJson.white tail) (chunk0104Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0104_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0105_before_reader"
  err.flush

noncomputable def chunk0105LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0105SuffixChars00 : List Char := [',']
noncomputable def chunk0105Chars00 : List Char := chunk0105LeadChars00 ++ fragment0405738Chars ++ chunk0105SuffixChars00
noncomputable def chunk0105Push00 (acc : List SourceJson) : List SourceJson := fragment0405738Value :: acc

noncomputable def chunk0105AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0105_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 499)
      (SourceJson.white (chunk0105LeadChars00 ++ (fragment0405738Chars ++ rest))) acc =
      (SourceJson.value (fuel + 498) (fragment0405738Chars ++ rest)).bind
        (chunk0105AfterValue00 (fuel + 498) acc) := by rfl

theorem array_chunk0105 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 499) (SourceJson.white (chunk0105Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 498) (SourceJson.white tail) (chunk0105Push00 acc) := by
  have hinput : chunk0105Chars00 ++ tail = chunk0105LeadChars00 ++ (fragment0405738Chars ++ (chunk0105SuffixChars00 ++ tail)) := by
    simp only [chunk0105Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 499) (SourceJson.white (chunk0105Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 499)
          (SourceJson.white (chunk0105LeadChars00 ++ (fragment0405738Chars ++ (chunk0105SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 499) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 498) (fragment0405738Chars ++ (chunk0105SuffixChars00 ++ tail))).bind
        (chunk0105AfterValue00 (fuel + 498) acc) := array_chunk0105_head fuel (chunk0105SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0405738Value, chunk0105SuffixChars00 ++ tail)).bind
        (chunk0105AfterValue00 (fuel + 498) acc) :=
      congrArg (fun result => result.bind (chunk0105AfterValue00 (fuel + 498) acc))
        (value_fragment0405738 (fuel + 275) (chunk0105SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 498) (SourceJson.white tail) (chunk0105Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0105_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0104Chars00 ++ chunk0105Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0105Push00 (chunk0104Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 500) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 498) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0104Chars00 ++ (chunk0105Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 500) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 500) (SourceJson.white (chunk0104Chars00 ++ (chunk0105Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 500) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 499) (SourceJson.white (chunk0105Chars00 ++ (tail))) (chunk0104Push00 (acc)) := array_chunk0104 fuel (chunk0105Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 498) (SourceJson.white tail) (blockPush acc) := array_chunk0105 fuel (tail) (chunk0104Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 404170).take 3122 = blockChars := by rfl

theorem block_original_split : sourceRest 404170 = blockChars ++ sourceRest 407292 := by
  calc
    sourceRest 404170 = (sourceRest 404170).take 3122 ++ (sourceRest 404170).drop 3122 :=
      (List.take_append_drop 3122 (sourceRest 404170)).symm
    _ = blockChars ++ (sourceRest 404170).drop 3122 :=
      congrArg (fun part => part ++ (sourceRest 404170).drop 3122) block_original_prefix
    _ = blockChars ++ sourceRest 407292 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 404170 3122)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 500) (SourceJson.white (sourceRest 404170)) acc =
      SourceJson.array (fuel + 498) (SourceJson.white (sourceRest 407292)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 500) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 407292) acc)

#print axioms object_fragment0404176_field_000
#print axioms object_fragment0404176_field_001
#print axioms object_fragment0404176_field_002
#print axioms object_fragment0404176_field_003
#print axioms object_fragment0404176_field_004
#print axioms object_fragment0404176_field_005
#print axioms object_fragment0404176_field_006
#print axioms object_fragment0404176_field_007
#print axioms object_fragment0404176_field_008
#print axioms object_fragment0404176_field_009
#print axioms value_fragment0404176
#print axioms object_fragment0405738_field_000
#print axioms object_fragment0405738_field_001
#print axioms object_fragment0405738_field_002
#print axioms object_fragment0405738_field_003
#print axioms object_fragment0405738_field_004
#print axioms object_fragment0405738_field_005
#print axioms object_fragment0405738_field_006
#print axioms object_fragment0405738_field_007
#print axioms object_fragment0405738_field_008
#print axioms object_fragment0405738_field_009
#print axioms value_fragment0405738
#print axioms array_chunk0104_head
#print axioms array_chunk0104
#print axioms array_chunk0105_head
#print axioms array_chunk0105
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock053

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
