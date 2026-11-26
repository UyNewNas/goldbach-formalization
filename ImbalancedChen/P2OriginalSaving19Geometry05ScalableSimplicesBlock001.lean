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

namespace SimplicesBlock001

noncomputable def fragment0117888Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0117888Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0117888Field000Value00 : SourceJson := .number (String.ofList ['8'])
noncomputable def fragment0117888Acc00100 : List (String × SourceJson) := (fragment0117888Field000Key00, fragment0117888Field000Value00) :: fragment0117888Acc00000
noncomputable def fragment0117888Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', ',']

theorem object_fragment0117888_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0117888Field000Chars00 ++ tail)) fragment0117888Acc00000 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment0117888Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117888_object_field_000"
  err.flush

noncomputable def fragment0117888Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0117888Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '1']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0117888Acc00200 : List (String × SourceJson) := (fragment0117888Field001Key00, fragment0117888Field001Value00) :: fragment0117888Acc00100
noncomputable def fragment0117888Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0117888_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0117888Field001Chars00 ++ tail)) fragment0117888Acc00100 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0117888Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117888_object_field_001"
  err.flush

noncomputable def fragment0117888Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0117888Field002Value00 : SourceJson := .str (String.ofList ['5', '2', '1', '0', '8', '9', '8', '1', '6', '4', '7', '8', '4', '5', '0', '5', '4', '2', '8', '6', '2', '3', '5', '4', '9', '2', '1', '4', '1', '7', '7', '4', '6', '6', '2', '4', '3', '/', '2', '2', '1', '2', '1', '7', '6', '8', '1', '6', '7', '8', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0117888Acc00300 : List (String × SourceJson) := (fragment0117888Field002Key00, fragment0117888Field002Value00) :: fragment0117888Acc00200
noncomputable def fragment0117888Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '2', '1', '0', '8', '9', '8', '1', '6', '4', '7', '8', '4', '5', '0', '5', '4', '2', '8', '6', '2', '3', '5', '4', '9', '2', '1', '4', '1', '7', '7', '4', '6', '6', '2', '4', '3', '/', '2', '2', '1', '2', '1', '7', '6', '8', '1', '6', '7', '8', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0117888_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0117888Field002Chars00 ++ tail)) fragment0117888Acc00200 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment0117888Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117888_object_field_002"
  err.flush

noncomputable def fragment0117888Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0117888Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0117888Acc00400 : List (String × SourceJson) := (fragment0117888Field003Key00, fragment0117888Field003Value00) :: fragment0117888Acc00300
noncomputable def fragment0117888Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0117888_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0117888Field003Chars00 ++ tail)) fragment0117888Acc00300 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment0117888Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117888_object_field_003"
  err.flush

noncomputable def fragment0117888Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0117888Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0117888Acc00500 : List (String × SourceJson) := (fragment0117888Field004Key00, fragment0117888Field004Value00) :: fragment0117888Acc00400
noncomputable def fragment0117888Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0117888_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment0117888Field004Chars00 ++ tail)) fragment0117888Acc00400 =
      SourceJson.object (fuel + 213) (SourceJson.white tail) fragment0117888Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117888_object_field_004"
  err.flush

noncomputable def fragment0117888Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0117888Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '8', '0', '4', '5', '3', '9', '5', '7', '0', '9', '/', '4', '0', '8', '3', '1', '8', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '3', '7', '5', '5', '2', '0', '1', '9', '0', '3', '/', '1', '3', '0', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '9', '5', '1', '1', '7', '8', '7', '6', '6', '7', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '6', '5', '0', '3', '4', '2', '4', '1', '2', '0', '3', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '6', '4', '0', '4', '9', '5', '7', '3', '9', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '4', '8', '2', '7', '4', '4', '6', '7', '1', '7', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '9', '0', '3', '3', '3', '9', '7', '9', '1', '/', '3', '2', '6', '6', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '9', '8', '9', '7', '6', '3', '4', '6', '4', '7', '/', '4', '3', '5', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '9', '7', '8', '2', '0', '8', '0', '5', '9', '/', '1', '4', '5', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '2', '2', '3', '3', '8', '9', '8', '4', '9', '/', '3', '2', '6', '6', '5', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0117888Acc00600 : List (String × SourceJson) := (fragment0117888Field005Key00, fragment0117888Field005Value00) :: fragment0117888Acc00500
noncomputable def fragment0117888Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '0', '4', '5', '3', '9', '5', '7', '0', '9', '/', '4', '0', '8', '3', '1', '8', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '3', '7', '5', '5', '2', '0', '1', '9', '0', '3', '/', '1', '3', '0', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '9', '5', '1', '1', '7', '8', '7', '6', '6', '7', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '6', '5', '0', '3', '4', '2', '4', '1', '2', '0', '3', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '6', '4', '0', '4', '9', '5', '7', '3', '9', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '4', '8', '2', '7', '4', '4', '6', '7', '1', '7', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '9', '0', '3', '3', '3', '9', '7', '9', '1', '/', '3', '2', '6', '6', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '8', '9', '7', '6', '3', '4', '6', '4', '7', '/', '4', '3', '5', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '9', '7', '8', '2', '0', '8', '0', '5', '9', '/', '1', '4', '5', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '2', '2', '3', '3', '8', '9', '8', '4', '9', '/', '3', '2', '6', '6', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0117888_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0117888Field005Chars00 ++ tail)) fragment0117888Acc00500 =
      SourceJson.object (fuel + 212) (SourceJson.white tail) fragment0117888Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117888_object_field_005"
  err.flush

noncomputable def fragment0117888Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0117888Field006Value00 : SourceJson := .str (String.ofList ['6', '2', '1', '5', '1', '9', '9', '3', '0', '5', '2', '6', '3', '5', '7', '2', '9', '6', '3', '9', '7', '8', '0', '1', '0', '0', '5', '7', '4', '5', '2', '4', '4', '7', '6', '5', '5', '1', '6', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '/', '8', '4', '7', '6', '1', '5', '7', '7', '5', '4', '3', '3', '9', '3', '2', '1', '5', '1', '7', '2', '0', '5', '5', '4', '3', '2', '3', '3', '3', '8', '2', '3', '4', '3', '3', '1', '3', '7', '7', '0', '7', '6', '3', '2', '3', '5', '9', '4', '9', '1', '7', '0', '6', '6', '2', '2', '7', '6', '6', '1', '6', '6', '0', '2', '4', '1'])
noncomputable def fragment0117888Acc00700 : List (String × SourceJson) := (fragment0117888Field006Key00, fragment0117888Field006Value00) :: fragment0117888Acc00600
noncomputable def fragment0117888Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '2', '1', '5', '1', '9', '9', '3', '0', '5', '2', '6', '3', '5', '7', '2', '9', '6', '3', '9', '7', '8', '0', '1', '0', '0', '5', '7', '4', '5', '2', '4', '4', '7', '6', '5', '5', '1', '6', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '/', '8', '4', '7', '6', '1', '5', '7', '7', '5', '4', '3', '3', '9', '3', '2', '1', '5', '1', '7', '2', '0', '5', '5', '4', '3', '2', '3', '3', '3', '8', '2', '3', '4', '3', '3', '1', '3', '7', '7', '0', '7', '6', '3', '2', '3', '5', '9', '4', '9', '1', '7', '0', '6', '6', '2', '2', '7', '6', '6', '1', '6', '6', '0', '2', '4', '1', '"', ',']

theorem object_fragment0117888_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 212) (SourceJson.white (fragment0117888Field006Chars00 ++ tail)) fragment0117888Acc00600 =
      SourceJson.object (fuel + 211) (SourceJson.white tail) fragment0117888Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117888_object_field_006"
  err.flush

noncomputable def fragment0117888Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0117888Field007Value00 : SourceJson := .str (String.ofList ['4', '2', '4', '6', '0', '6', '3', '1', '0', '4', '1', '7', '0', '4', '7', '8', '7', '4', '6', '6', '0', '8', '1', '2', '2', '5', '5', '0', '0', '7', '0', '2', '4', '2', '9', '7', '6', '8', '3', '4', '7', '8', '0', '6', '1', '5', '9', '6', '9', '3', '7', '4', '6', '5', '8', '7', '5', '5', '3', '8', '3', '3', '7', '1', '0', '5', '3', '9', '6', '6', '5', '9', '1', '4', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '0', '4', '5', '2', '3', '4', '3', '7', '5', '7', '7', '0', '5', '5', '9', '3', '5', '6', '3', '8', '7', '3', '4', '1', '4', '6', '6', '3', '5', '0', '0', '8', '6', '8', '5', '2', '8', '7', '6', '7', '3', '4', '2', '6', '2', '6', '8', '6', '5', '0', '8', '6', '9', '3', '3', '7', '2', '8', '0', '9', '8', '1', '7', '7', '3', '8', '4', '7', '1', '3', '4', '7', '5', '7', '9', '4', '0', '1', '2', '8', '8', '8', '2', '7', '9', '1', '8', '2', '7', '7', '2', '6', '7', '1', '4', '3', '7', '5', '4', '5', '5', '8', '3', '8', '5', '3', '4', '1', '7', '7'])
noncomputable def fragment0117888Acc00800 : List (String × SourceJson) := (fragment0117888Field007Key00, fragment0117888Field007Value00) :: fragment0117888Acc00700
noncomputable def fragment0117888Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '2', '4', '6', '0', '6', '3', '1', '0', '4', '1', '7', '0', '4', '7', '8', '7', '4', '6', '6', '0', '8', '1', '2', '2', '5', '5', '0', '0', '7', '0', '2', '4', '2', '9', '7', '6', '8', '3', '4', '7', '8', '0', '6', '1', '5', '9', '6', '9', '3', '7', '4', '6', '5', '8', '7', '5', '5', '3', '8', '3', '3', '7', '1', '0', '5', '3', '9', '6', '6', '5', '9', '1', '4', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '0', '4', '5', '2', '3', '4', '3', '7', '5', '7', '7', '0', '5', '5', '9', '3', '5', '6', '3', '8', '7', '3', '4', '1', '4', '6', '6', '3', '5', '0', '0', '8', '6', '8', '5', '2', '8', '7', '6', '7', '3', '4', '2', '6', '2', '6', '8', '6', '5', '0', '8', '6', '9', '3', '3', '7', '2', '8', '0', '9', '8', '1', '7', '7', '3', '8', '4', '7', '1', '3', '4', '7', '5', '7', '9', '4', '0', '1', '2', '8', '8', '8', '2', '7', '9', '1', '8', '2', '7', '7', '2', '6', '7', '1', '4', '3', '7', '5', '4', '5', '5', '8', '3', '8', '5', '3', '4', '1', '7', '7', '"', ',']

theorem object_fragment0117888_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 211) (SourceJson.white (fragment0117888Field007Chars00 ++ tail)) fragment0117888Acc00700 =
      SourceJson.object (fuel + 210) (SourceJson.white tail) fragment0117888Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117888_object_field_007"
  err.flush

noncomputable def fragment0117888Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0117888Field008Value00 : SourceJson := .str (String.ofList ['5', '8', '0', '9', '4', '5', '7', '9', '5', '1', '2', '0'])
noncomputable def fragment0117888Acc00900 : List (String × SourceJson) := (fragment0117888Field008Key00, fragment0117888Field008Value00) :: fragment0117888Acc00800
noncomputable def fragment0117888Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '8', '0', '9', '4', '5', '7', '9', '5', '1', '2', '0', '"', ',']

theorem object_fragment0117888_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 210) (SourceJson.white (fragment0117888Field008Chars00 ++ tail)) fragment0117888Acc00800 =
      SourceJson.object (fuel + 209) (SourceJson.white tail) fragment0117888Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117888_object_field_008"
  err.flush

noncomputable def fragment0117888Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0117888Field009Value00 : SourceJson := .str (String.ofList ['2', '3', '9', '5', '1', '7', '3', '8', '2', '6', '6', '7', '0'])
noncomputable def fragment0117888Acc01000 : List (String × SourceJson) := (fragment0117888Field009Key00, fragment0117888Field009Value00) :: fragment0117888Acc00900
noncomputable def fragment0117888Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '9', '5', '1', '7', '3', '8', '2', '6', '6', '7', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0117888_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 209) (SourceJson.white (fragment0117888Field009Chars00 ++ tail)) fragment0117888Acc00900 =
      .ok (.obj (fragment0117888Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117888_object_field_009"
  err.flush

noncomputable def fragment0117888Chars : List Char := '{' :: (fragment0117888Field000Chars00 ++ fragment0117888Field001Chars00 ++ fragment0117888Field002Chars00 ++ fragment0117888Field003Chars00 ++ fragment0117888Field004Chars00 ++ fragment0117888Field005Chars00 ++ fragment0117888Field006Chars00 ++ fragment0117888Field007Chars00 ++ fragment0117888Field008Chars00 ++ fragment0117888Field009Chars00)
noncomputable def fragment0117888Value : SourceJson := .obj (fragment0117888Acc01000.reverse)

theorem value_fragment0117888 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 219) (fragment0117888Chars ++ tail) =
      .ok (fragment0117888Value, tail) := by
  have hinput : fragment0117888Chars ++ tail = '{' :: (fragment0117888Field000Chars00 ++ (fragment0117888Field001Chars00 ++ (fragment0117888Field002Chars00 ++ (fragment0117888Field003Chars00 ++ (fragment0117888Field004Chars00 ++ (fragment0117888Field005Chars00 ++ (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0117888Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 219) (fragment0117888Chars ++ tail) =
        SourceJson.value (fuel + 219) ('{' :: (fragment0117888Field000Chars00 ++ (fragment0117888Field001Chars00 ++ (fragment0117888Field002Chars00 ++ (fragment0117888Field003Chars00 ++ (fragment0117888Field004Chars00 ++ (fragment0117888Field005Chars00 ++ (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 219)) hinput
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0117888Field000Chars00 ++ (fragment0117888Field001Chars00 ++ (fragment0117888Field002Chars00 ++ (fragment0117888Field003Chars00 ++ (fragment0117888Field004Chars00 ++ (fragment0117888Field005Chars00 ++ (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail)))))))))))) fragment0117888Acc00000 := by rfl
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0117888Field001Chars00 ++ (fragment0117888Field002Chars00 ++ (fragment0117888Field003Chars00 ++ (fragment0117888Field004Chars00 ++ (fragment0117888Field005Chars00 ++ (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail))))))))))) fragment0117888Acc00100 := object_fragment0117888_field_000 fuel (fragment0117888Field001Chars00 ++ (fragment0117888Field002Chars00 ++ (fragment0117888Field003Chars00 ++ (fragment0117888Field004Chars00 ++ (fragment0117888Field005Chars00 ++ (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0117888Field002Chars00 ++ (fragment0117888Field003Chars00 ++ (fragment0117888Field004Chars00 ++ (fragment0117888Field005Chars00 ++ (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail)))))))))) fragment0117888Acc00200 := object_fragment0117888_field_001 fuel (fragment0117888Field002Chars00 ++ (fragment0117888Field003Chars00 ++ (fragment0117888Field004Chars00 ++ (fragment0117888Field005Chars00 ++ (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0117888Field003Chars00 ++ (fragment0117888Field004Chars00 ++ (fragment0117888Field005Chars00 ++ (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail))))))))) fragment0117888Acc00300 := object_fragment0117888_field_002 fuel (fragment0117888Field003Chars00 ++ (fragment0117888Field004Chars00 ++ (fragment0117888Field005Chars00 ++ (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment0117888Field004Chars00 ++ (fragment0117888Field005Chars00 ++ (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail)))))))) fragment0117888Acc00400 := object_fragment0117888_field_003 fuel (fragment0117888Field004Chars00 ++ (fragment0117888Field005Chars00 ++ (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0117888Field005Chars00 ++ (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail))))))) fragment0117888Acc00500 := object_fragment0117888_field_004 fuel (fragment0117888Field005Chars00 ++ (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 212) (SourceJson.white (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail)))))) fragment0117888Acc00600 := object_fragment0117888_field_005 fuel (fragment0117888Field006Chars00 ++ (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 211) (SourceJson.white (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail))))) fragment0117888Acc00700 := object_fragment0117888_field_006 fuel (fragment0117888Field007Chars00 ++ (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 210) (SourceJson.white (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail)))) fragment0117888Acc00800 := object_fragment0117888_field_007 fuel (fragment0117888Field008Chars00 ++ (fragment0117888Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 209) (SourceJson.white (fragment0117888Field009Chars00 ++ (tail))) fragment0117888Acc00900 := object_fragment0117888_field_008 fuel (fragment0117888Field009Chars00 ++ (tail))
    _ = .ok (fragment0117888Value, tail) := object_fragment0117888_field_009 fuel (tail)

noncomputable def fragment0119450Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0119450Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0119450Field000Value00 : SourceJson := .number (String.ofList ['9'])
noncomputable def fragment0119450Acc00100 : List (String × SourceJson) := (fragment0119450Field000Key00, fragment0119450Field000Value00) :: fragment0119450Acc00000
noncomputable def fragment0119450Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', ',']

theorem object_fragment0119450_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 376) (SourceJson.white (fragment0119450Field000Chars00 ++ tail)) fragment0119450Acc00000 =
      SourceJson.object (fuel + 375) (SourceJson.white tail) fragment0119450Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0119450_object_field_000"
  err.flush

noncomputable def fragment0119450Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0119450Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '1']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0119450Acc00200 : List (String × SourceJson) := (fragment0119450Field001Key00, fragment0119450Field001Value00) :: fragment0119450Acc00100
noncomputable def fragment0119450Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0119450_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 375) (SourceJson.white (fragment0119450Field001Chars00 ++ tail)) fragment0119450Acc00100 =
      SourceJson.object (fuel + 374) (SourceJson.white tail) fragment0119450Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0119450_object_field_001"
  err.flush

noncomputable def fragment0119450Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0119450Field002Value00 : SourceJson := .str (String.ofList ['5', '6', '9', '9', '7', '6', '7', '3', '1', '8', '5', '6', '0', '2', '9', '7', '7', '7', '9', '6', '6', '4', '2', '5', '9', '5', '2', '6', '4', '0', '0', '5', '6', '2', '1', '9', '2', '0', '9', '8', '7', '3', '/', '9', '4', '3', '8', '6', '2', '1', '0', '8', '4', '9', '4', '2', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0119450Acc00300 : List (String × SourceJson) := (fragment0119450Field002Key00, fragment0119450Field002Value00) :: fragment0119450Acc00200
noncomputable def fragment0119450Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '6', '9', '9', '7', '6', '7', '3', '1', '8', '5', '6', '0', '2', '9', '7', '7', '7', '9', '6', '6', '4', '2', '5', '9', '5', '2', '6', '4', '0', '0', '5', '6', '2', '1', '9', '2', '0', '9', '8', '7', '3', '/', '9', '4', '3', '8', '6', '2', '1', '0', '8', '4', '9', '4', '2', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0119450_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 374) (SourceJson.white (fragment0119450Field002Chars00 ++ tail)) fragment0119450Acc00200 =
      SourceJson.object (fuel + 373) (SourceJson.white tail) fragment0119450Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0119450_object_field_002"
  err.flush

noncomputable def fragment0119450Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0119450Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '2', '4', '1', '6', '9', '/', '1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0119450Acc00400 : List (String × SourceJson) := (fragment0119450Field003Key00, fragment0119450Field003Value00) :: fragment0119450Acc00300
noncomputable def fragment0119450Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '8', '2', '4', '1', '6', '9', '/', '1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0119450_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 373) (SourceJson.white (fragment0119450Field003Chars00 ++ tail)) fragment0119450Acc00300 =
      SourceJson.object (fuel + 372) (SourceJson.white tail) fragment0119450Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0119450_object_field_003"
  err.flush

noncomputable def fragment0119450Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0119450Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0119450Acc00500 : List (String × SourceJson) := (fragment0119450Field004Key00, fragment0119450Field004Value00) :: fragment0119450Acc00400
noncomputable def fragment0119450Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0119450_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 372) (SourceJson.white (fragment0119450Field004Chars00 ++ tail)) fragment0119450Acc00400 =
      SourceJson.object (fuel + 371) (SourceJson.white tail) fragment0119450Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0119450_object_field_004"
  err.flush

noncomputable def fragment0119450Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0119450Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '0', '8', '5', '6', '2', '0', '9', '1', '2', '1', '7', '1', '5', '2', '5', '9', '7', '4', '5', '7', '/', '2', '2', '6', '2', '8', '9', '2', '1', '1', '1', '8', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '7', '0', '3', '4', '5', '8', '8', '9', '7', '6', '9', '6', '2', '6', '2', '1', '1', '/', '7', '0', '7', '1', '5', '3', '7', '8', '4', '9', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '8', '9', '6', '7', '6', '1', '3', '9', '2', '0', '1', '3', '5', '5', '6', '7', '/', '1', '5', '0', '8', '5', '9', '4', '7', '4', '1', '2', '0', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '5', '0', '4', '7', '1', '4', '2', '8', '3', '5', '4', '5', '4', '3', '4', '4', '9', '/', '9', '4', '2', '8', '7', '1', '7', '1', '3', '2', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '7', '6', '7', '9', '4', '7', '4', '7', '8', '8', '8', '7', '3', '7', '2', '9', '/', '3', '9', '2', '8', '6', '3', '2', '1', '3', '8', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '1', '3', '6', '2', '5', '8', '9', '3', '6', '6', '7', '5', '2', '5', '4', '4', '1', '/', '1', '8', '8', '5', '7', '4', '3', '4', '2', '6', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '8', '9', '0', '1', '7', '8', '0', '5', '0', '6', '7', '3', '6', '3', '5', '9', '3', '1', '/', '3', '7', '7', '1', '4', '8', '6', '8', '5', '3', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '8', '5', '8', '3', '9', '2', '7', '6', '8', '8', '9', '6', '9', '7', '1', '7', '1', '7', '/', '1', '1', '3', '1', '4', '4', '6', '0', '5', '5', '9', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '1', '8', '2', '4', '9', '3', '1', '5', '8', '8', '8', '1', '9', '2', '7', '1', '9', '7', '/', '1', '1', '3', '1', '4', '4', '6', '0', '5', '5', '9', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '1', '9', '1', '8', '8', '0', '6', '2', '6', '8', '6', '5', '1', '2', '8', '1', '/', '1', '5', '7', '1', '4', '5', '2', '8', '5', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0119450Acc00600 : List (String × SourceJson) := (fragment0119450Field005Key00, fragment0119450Field005Value00) :: fragment0119450Acc00500
noncomputable def fragment0119450Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '5', '6', '2', '0', '9', '1', '2', '1', '7', '1', '5', '2', '5', '9', '7', '4', '5', '7', '/', '2', '2', '6', '2', '8', '9', '2', '1', '1', '1', '8', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '7', '0', '3', '4', '5', '8', '8', '9', '7', '6', '9', '6', '2', '6', '2', '1', '1', '/', '7', '0', '7', '1', '5', '3', '7', '8', '4', '9', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '8', '9', '6', '7', '6', '1', '3', '9', '2', '0', '1', '3', '5', '5', '6', '7', '/', '1', '5', '0', '8', '5', '9', '4', '7', '4', '1', '2', '0', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '5', '0', '4', '7', '1', '4', '2', '8', '3', '5', '4', '5', '4', '3', '4', '4', '9', '/', '9', '4', '2', '8', '7', '1', '7', '1', '3', '2', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '7', '6', '7', '9', '4', '7', '4', '7', '8', '8', '8', '7', '3', '7', '2', '9', '/', '3', '9', '2', '8', '6', '3', '2', '1', '3', '8', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '3', '6', '2', '5', '8', '9', '3', '6', '6', '7', '5', '2', '5', '4', '4', '1', '/', '1', '8', '8', '5', '7', '4', '3', '4', '2', '6', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '9', '0', '1', '7', '8', '0', '5', '0', '6', '7', '3', '6', '3', '5', '9', '3', '1', '/', '3', '7', '7', '1', '4', '8', '6', '8', '5', '3', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '8', '5', '8', '3', '9', '2', '7', '6', '8', '8', '9', '6', '9', '7', '1', '7', '1', '7', '/', '1', '1', '3', '1', '4', '4', '6', '0', '5', '5', '9', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '1', '8', '2', '4', '9', '3', '1', '5', '8', '8', '8', '1', '9', '2', '7', '1', '9', '7', '/', '1', '1', '3', '1', '4', '4', '6', '0', '5', '5', '9', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '1', '9', '1', '8', '8', '0', '6', '2', '6', '8', '6', '5', '1', '2', '8', '1', '/', '1', '5', '7', '1', '4', '5', '2', '8', '5', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0119450_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 371) (SourceJson.white (fragment0119450Field005Chars00 ++ tail)) fragment0119450Acc00500 =
      SourceJson.object (fuel + 370) (SourceJson.white tail) fragment0119450Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0119450_object_field_005"
  err.flush

noncomputable def fragment0119450Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0119450Field006Value00 : SourceJson := .str (String.ofList ['4', '3', '8', '1', '7', '6', '4', '5', '3', '9', '5', '4', '3', '5', '7', '2', '4', '3', '3', '0', '5', '4', '7', '3', '7', '8', '1', '0', '6', '2', '6', '3', '9', '5', '3', '7', '3', '7', '4', '1', '9', '8', '2', '8', '2', '7', '0', '8', '5', '9', '3', '7', '5', '/', '1', '1', '3', '0', '1', '4', '7', '0', '8', '8', '5', '7', '9', '2', '9', '6', '5', '0', '5', '1', '5', '6', '8', '0', '9', '1', '5', '7', '1', '9', '0', '4', '8', '6', '6', '1', '2', '5', '9', '3', '1', '0', '0', '6', '7', '2', '4', '0', '8', '6', '8', '1', '0', '6', '7', '2', '8', '9', '9', '9', '6', '3', '5', '2', '8', '1', '2'])
noncomputable def fragment0119450Acc00700 : List (String × SourceJson) := (fragment0119450Field006Key00, fragment0119450Field006Value00) :: fragment0119450Acc00600
noncomputable def fragment0119450Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '3', '8', '1', '7', '6', '4', '5', '3', '9', '5', '4', '3', '5', '7', '2', '4', '3', '3', '0', '5', '4', '7', '3', '7', '8', '1', '0', '6', '2', '6', '3', '9', '5', '3', '7', '3', '7', '4', '1', '9', '8', '2', '8', '2', '7', '0', '8', '5', '9', '3', '7', '5', '/', '1', '1', '3', '0', '1', '4', '7', '0', '8', '8', '5', '7', '9', '2', '9', '6', '5', '0', '5', '1', '5', '6', '8', '0', '9', '1', '5', '7', '1', '9', '0', '4', '8', '6', '6', '1', '2', '5', '9', '3', '1', '0', '0', '6', '7', '2', '4', '0', '8', '6', '8', '1', '0', '6', '7', '2', '8', '9', '9', '9', '6', '3', '5', '2', '8', '1', '2', '"', ',']

theorem object_fragment0119450_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 370) (SourceJson.white (fragment0119450Field006Chars00 ++ tail)) fragment0119450Acc00600 =
      SourceJson.object (fuel + 369) (SourceJson.white tail) fragment0119450Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0119450_object_field_006"
  err.flush

noncomputable def fragment0119450Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0119450Field007Value00 : SourceJson := .str (String.ofList ['5', '1', '2', '4', '2', '6', '4', '3', '7', '5', '7', '4', '4', '1', '1', '3', '8', '1', '1', '9', '8', '7', '1', '0', '5', '1', '6', '6', '2', '9', '8', '8', '2', '8', '0', '9', '7', '0', '4', '0', '7', '4', '2', '5', '9', '8', '4', '6', '7', '8', '8', '0', '5', '7', '1', '1', '9', '6', '7', '7', '8', '7', '0', '9', '9', '5', '2', '3', '6', '6', '6', '1', '5', '9', '8', '8', '0', '9', '1', '2', '6', '5', '4', '1', '2', '1', '2', '7', '8', '9', '1', '5', '1', '3', '1', '9', '6', '8', '8', '5', '6', '5', '4', '6', '8', '2', '2', '1', '6', '8', '1', '5', '1', '1', '3', '4', '8', '3', '2', '0', '3', '0', '1', '9', '3', '9', '1', '6', '5', '5', '1', '0', '1', '4', '1', '0', '2', '2', '3', '0', '4', '2', '0', '9', '5', '9', '4', '1', '3', '9', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '7', '8', '7', '7', '6', '0', '0', '4', '3', '0', '4', '9', '2', '1', '2', '7', '9', '3', '8', '3', '9', '8', '1', '2', '2', '7', '2', '6', '2', '6', '5', '6', '7', '7', '8', '2', '2', '9', '4', '8', '8', '9', '5', '8', '1', '7', '4', '9', '7', '9', '1', '9', '2', '8', '3', '8', '8', '3', '9', '1', '6', '9', '7', '8', '8', '7', '0', '9', '2', '8', '7', '7', '4', '7', '7', '9', '2', '4', '5', '0', '0', '5', '1', '7', '3', '5', '5', '5', '7', '3', '1', '6', '4', '6', '9', '1', '0', '0', '5', '5', '9', '9', '3', '3', '1', '1', '9', '8', '9', '3', '1', '6', '4', '4', '8', '2', '6', '0', '4', '8', '7', '7', '3', '8', '8', '4', '9', '3', '1', '5', '2', '9', '8', '6', '4', '1', '7', '0', '2', '9', '5', '7', '3', '3', '4', '0', '9', '7', '0', '8', '1', '0', '1', '1', '3', '7', '5', '9', '4', '6', '1', '1', '8', '8', '1', '6', '4', '2', '8', '8', '7', '1', '8', '7', '9', '7', '7', '6', '3', '9', '3', '0', '4', '8', '1', '3', '3'])
noncomputable def fragment0119450Acc00800 : List (String × SourceJson) := (fragment0119450Field007Key00, fragment0119450Field007Value00) :: fragment0119450Acc00700
noncomputable def fragment0119450Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '1', '2', '4', '2', '6', '4', '3', '7', '5', '7', '4', '4', '1', '1', '3', '8', '1', '1', '9', '8', '7', '1', '0', '5', '1', '6', '6', '2', '9', '8', '8', '2', '8', '0', '9', '7', '0', '4', '0', '7', '4', '2', '5', '9', '8', '4', '6', '7', '8', '8', '0', '5', '7', '1', '1', '9', '6', '7', '7', '8', '7', '0', '9', '9', '5', '2', '3', '6', '6', '6', '1', '5', '9', '8', '8', '0', '9', '1', '2', '6', '5', '4', '1', '2', '1', '2', '7', '8', '9', '1', '5', '1', '3', '1', '9', '6', '8', '8', '5', '6', '5', '4', '6', '8', '2', '2', '1', '6', '8', '1', '5', '1', '1', '3', '4', '8', '3', '2', '0', '3', '0', '1', '9', '3', '9', '1', '6', '5', '5', '1', '0', '1', '4', '1', '0', '2', '2', '3', '0', '4', '2', '0', '9', '5', '9', '4', '1', '3', '9', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '7', '8', '7', '7', '6', '0', '0', '4', '3', '0', '4', '9', '2', '1', '2', '7', '9', '3', '8', '3', '9', '8', '1', '2', '2', '7', '2', '6', '2', '6', '5', '6', '7', '7', '8', '2', '2', '9', '4', '8', '8', '9', '5', '8', '1', '7', '4', '9', '7', '9', '1', '9', '2', '8', '3', '8', '8', '3', '9', '1', '6', '9', '7', '8', '8', '7', '0', '9', '2', '8', '7', '7', '4', '7', '7', '9', '2', '4', '5', '0', '0', '5', '1', '7', '3', '5', '5', '5', '7', '3', '1', '6', '4', '6', '9', '1', '0', '0', '5', '5', '9', '9', '3', '3', '1', '1', '9', '8', '9', '3', '1', '6', '4', '4', '8', '2', '6', '0', '4', '8', '7', '7', '3', '8', '8', '4', '9', '3', '1', '5', '2', '9', '8', '6', '4', '1', '7', '0', '2', '9', '5', '7', '3', '3', '4', '0', '9', '7', '0', '8', '1', '0', '1', '1', '3', '7', '5', '9', '4', '6', '1', '1', '8', '8', '1', '6', '4', '2', '8', '8', '7', '1', '8', '7', '9', '7', '7', '6', '3', '9', '3', '0', '4', '8', '1', '3', '3', '"', ',']

theorem object_fragment0119450_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 369) (SourceJson.white (fragment0119450Field007Chars00 ++ tail)) fragment0119450Acc00700 =
      SourceJson.object (fuel + 368) (SourceJson.white tail) fragment0119450Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0119450_object_field_007"
  err.flush

noncomputable def fragment0119450Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0119450Field008Value00 : SourceJson := .str (String.ofList ['3', '0', '7', '1', '8', '0', '5', '0', '4', '6', '8', '5', '1', '1', '2', '4'])
noncomputable def fragment0119450Acc00900 : List (String × SourceJson) := (fragment0119450Field008Key00, fragment0119450Field008Value00) :: fragment0119450Acc00800
noncomputable def fragment0119450Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '0', '7', '1', '8', '0', '5', '0', '4', '6', '8', '5', '1', '1', '2', '4', '"', ',']

theorem object_fragment0119450_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 368) (SourceJson.white (fragment0119450Field008Chars00 ++ tail)) fragment0119450Acc00800 =
      SourceJson.object (fuel + 367) (SourceJson.white tail) fragment0119450Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0119450_object_field_008"
  err.flush

noncomputable def fragment0119450Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0119450Field009Value00 : SourceJson := .str (String.ofList ['1', '2', '7', '7', '1', '7', '7', '2', '8', '5', '1', '4', '9', '0', '4', '8', '4'])
noncomputable def fragment0119450Acc01000 : List (String × SourceJson) := (fragment0119450Field009Key00, fragment0119450Field009Value00) :: fragment0119450Acc00900
noncomputable def fragment0119450Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '7', '7', '1', '7', '7', '2', '8', '5', '1', '4', '9', '0', '4', '8', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0119450_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 367) (SourceJson.white (fragment0119450Field009Chars00 ++ tail)) fragment0119450Acc00900 =
      .ok (.obj (fragment0119450Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0119450_object_field_009"
  err.flush

noncomputable def fragment0119450Chars : List Char := '{' :: (fragment0119450Field000Chars00 ++ fragment0119450Field001Chars00 ++ fragment0119450Field002Chars00 ++ fragment0119450Field003Chars00 ++ fragment0119450Field004Chars00 ++ fragment0119450Field005Chars00 ++ fragment0119450Field006Chars00 ++ fragment0119450Field007Chars00 ++ fragment0119450Field008Chars00 ++ fragment0119450Field009Chars00)
noncomputable def fragment0119450Value : SourceJson := .obj (fragment0119450Acc01000.reverse)

theorem value_fragment0119450 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 377) (fragment0119450Chars ++ tail) =
      .ok (fragment0119450Value, tail) := by
  have hinput : fragment0119450Chars ++ tail = '{' :: (fragment0119450Field000Chars00 ++ (fragment0119450Field001Chars00 ++ (fragment0119450Field002Chars00 ++ (fragment0119450Field003Chars00 ++ (fragment0119450Field004Chars00 ++ (fragment0119450Field005Chars00 ++ (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0119450Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 377) (fragment0119450Chars ++ tail) =
        SourceJson.value (fuel + 377) ('{' :: (fragment0119450Field000Chars00 ++ (fragment0119450Field001Chars00 ++ (fragment0119450Field002Chars00 ++ (fragment0119450Field003Chars00 ++ (fragment0119450Field004Chars00 ++ (fragment0119450Field005Chars00 ++ (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 377)) hinput
    _ = SourceJson.object (fuel + 376) (SourceJson.white (fragment0119450Field000Chars00 ++ (fragment0119450Field001Chars00 ++ (fragment0119450Field002Chars00 ++ (fragment0119450Field003Chars00 ++ (fragment0119450Field004Chars00 ++ (fragment0119450Field005Chars00 ++ (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail)))))))))))) fragment0119450Acc00000 := by rfl
    _ = SourceJson.object (fuel + 375) (SourceJson.white (fragment0119450Field001Chars00 ++ (fragment0119450Field002Chars00 ++ (fragment0119450Field003Chars00 ++ (fragment0119450Field004Chars00 ++ (fragment0119450Field005Chars00 ++ (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail))))))))))) fragment0119450Acc00100 := object_fragment0119450_field_000 fuel (fragment0119450Field001Chars00 ++ (fragment0119450Field002Chars00 ++ (fragment0119450Field003Chars00 ++ (fragment0119450Field004Chars00 ++ (fragment0119450Field005Chars00 ++ (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 374) (SourceJson.white (fragment0119450Field002Chars00 ++ (fragment0119450Field003Chars00 ++ (fragment0119450Field004Chars00 ++ (fragment0119450Field005Chars00 ++ (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail)))))))))) fragment0119450Acc00200 := object_fragment0119450_field_001 fuel (fragment0119450Field002Chars00 ++ (fragment0119450Field003Chars00 ++ (fragment0119450Field004Chars00 ++ (fragment0119450Field005Chars00 ++ (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 373) (SourceJson.white (fragment0119450Field003Chars00 ++ (fragment0119450Field004Chars00 ++ (fragment0119450Field005Chars00 ++ (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail))))))))) fragment0119450Acc00300 := object_fragment0119450_field_002 fuel (fragment0119450Field003Chars00 ++ (fragment0119450Field004Chars00 ++ (fragment0119450Field005Chars00 ++ (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 372) (SourceJson.white (fragment0119450Field004Chars00 ++ (fragment0119450Field005Chars00 ++ (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail)))))))) fragment0119450Acc00400 := object_fragment0119450_field_003 fuel (fragment0119450Field004Chars00 ++ (fragment0119450Field005Chars00 ++ (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 371) (SourceJson.white (fragment0119450Field005Chars00 ++ (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail))))))) fragment0119450Acc00500 := object_fragment0119450_field_004 fuel (fragment0119450Field005Chars00 ++ (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 370) (SourceJson.white (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail)))))) fragment0119450Acc00600 := object_fragment0119450_field_005 fuel (fragment0119450Field006Chars00 ++ (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 369) (SourceJson.white (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail))))) fragment0119450Acc00700 := object_fragment0119450_field_006 fuel (fragment0119450Field007Chars00 ++ (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 368) (SourceJson.white (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail)))) fragment0119450Acc00800 := object_fragment0119450_field_007 fuel (fragment0119450Field008Chars00 ++ (fragment0119450Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 367) (SourceJson.white (fragment0119450Field009Chars00 ++ (tail))) fragment0119450Acc00900 := object_fragment0119450_field_008 fuel (fragment0119450Field009Chars00 ++ (tail))
    _ = .ok (fragment0119450Value, tail) := object_fragment0119450_field_009 fuel (tail)

noncomputable def fragment0121338Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0121338Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0121338Field000Value00 : SourceJson := .number (String.ofList ['1', '0'])
noncomputable def fragment0121338Acc00100 : List (String × SourceJson) := (fragment0121338Field000Key00, fragment0121338Field000Value00) :: fragment0121338Acc00000
noncomputable def fragment0121338Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', ',']

theorem object_fragment0121338_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0121338Field000Chars00 ++ tail)) fragment0121338Acc00000 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0121338Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121338_object_field_000"
  err.flush

noncomputable def fragment0121338Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0121338Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '1']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0121338Acc00200 : List (String × SourceJson) := (fragment0121338Field001Key00, fragment0121338Field001Value00) :: fragment0121338Acc00100
noncomputable def fragment0121338Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0121338_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0121338Field001Chars00 ++ tail)) fragment0121338Acc00100 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0121338Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121338_object_field_001"
  err.flush

noncomputable def fragment0121338Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0121338Field002Value00 : SourceJson := .str (String.ofList ['4', '0', '7', '0', '4', '3', '1', '1', '0', '6', '2', '5', '8', '7', '3', '7', '4', '4', '1', '2', '4', '2', '9', '6', '3', '9', '5', '5', '4', '5', '8', '8', '1', '3', '4', '8', '1', '3', '9', '1', '3', '/', '2', '6', '2', '7', '3', '4', '7', '2', '5', '5', '7', '8', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0121338Acc00300 : List (String × SourceJson) := (fragment0121338Field002Key00, fragment0121338Field002Value00) :: fragment0121338Acc00200
noncomputable def fragment0121338Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '0', '7', '0', '4', '3', '1', '1', '0', '6', '2', '5', '8', '7', '3', '7', '4', '4', '1', '2', '4', '2', '9', '6', '3', '9', '5', '5', '4', '5', '8', '8', '1', '3', '4', '8', '1', '3', '9', '1', '3', '/', '2', '6', '2', '7', '3', '4', '7', '2', '5', '5', '7', '8', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0121338_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0121338Field002Chars00 ++ tail)) fragment0121338Acc00200 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0121338Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121338_object_field_002"
  err.flush

noncomputable def fragment0121338Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0121338Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0121338Acc00400 : List (String × SourceJson) := (fragment0121338Field003Key00, fragment0121338Field003Value00) :: fragment0121338Acc00300
noncomputable def fragment0121338Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0121338_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0121338Field003Chars00 ++ tail)) fragment0121338Acc00300 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0121338Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121338_object_field_003"
  err.flush

noncomputable def fragment0121338Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0121338Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0121338Acc00500 : List (String × SourceJson) := (fragment0121338Field004Key00, fragment0121338Field004Value00) :: fragment0121338Acc00400
noncomputable def fragment0121338Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0121338_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0121338Field004Chars00 ++ tail)) fragment0121338Acc00400 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0121338Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121338_object_field_004"
  err.flush

noncomputable def fragment0121338Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0121338Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '0', '0', '3', '1', '4', '4', '3', '9', '0', '7', '5', '9', '7', '/', '6', '5', '1', '7', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '3', '2', '1', '0', '7', '2', '8', '6', '4', '3', '/', '1', '0', '1', '8', '3', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '7', '7', '4', '9', '6', '3', '4', '5', '6', '7', '9', '/', '2', '1', '7', '2', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '6', '7', '7', '5', '6', '6', '7', '5', '7', '0', '9', '/', '2', '7', '1', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '1', '3', '0', '4', '7', '5', '1', '7', '7', '/', '5', '6', '5', '7', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '7', '7', '3', '4', '8', '1', '8', '3', '7', '3', '/', '5', '4', '3', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '8', '3', '0', '3', '3', '6', '5', '2', '6', '7', '1', '/', '1', '0', '8', '6', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '4', '3', '8', '2', '9', '5', '6', '0', '4', '1', '7', '/', '3', '2', '5', '8', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '2', '6', '9', '8', '6', '9', '9', '8', '4', '9', '7', '/', '3', '2', '5', '8', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '7', '0', '0', '0', '8', '2', '7', '4', '3', '1', '/', '4', '5', '2', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0121338Acc00600 : List (String × SourceJson) := (fragment0121338Field005Key00, fragment0121338Field005Value00) :: fragment0121338Acc00500
noncomputable def fragment0121338Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '0', '3', '1', '4', '4', '3', '9', '0', '7', '5', '9', '7', '/', '6', '5', '1', '7', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '3', '2', '1', '0', '7', '2', '8', '6', '4', '3', '/', '1', '0', '1', '8', '3', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '7', '7', '4', '9', '6', '3', '4', '5', '6', '7', '9', '/', '2', '1', '7', '2', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '6', '7', '7', '5', '6', '6', '7', '5', '7', '0', '9', '/', '2', '7', '1', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '1', '3', '0', '4', '7', '5', '1', '7', '7', '/', '5', '6', '5', '7', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '7', '7', '3', '4', '8', '1', '8', '3', '7', '3', '/', '5', '4', '3', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '8', '3', '0', '3', '3', '6', '5', '2', '6', '7', '1', '/', '1', '0', '8', '6', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '4', '3', '8', '2', '9', '5', '6', '0', '4', '1', '7', '/', '3', '2', '5', '8', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '2', '6', '9', '8', '6', '9', '9', '8', '4', '9', '7', '/', '3', '2', '5', '8', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '7', '0', '0', '0', '8', '2', '7', '4', '3', '1', '/', '4', '5', '2', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0121338_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0121338Field005Chars00 ++ tail)) fragment0121338Acc00500 =
      SourceJson.object (fuel + 240) (SourceJson.white tail) fragment0121338Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121338_object_field_005"
  err.flush

noncomputable def fragment0121338Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0121338Field006Value00 : SourceJson := .str (String.ofList ['3', '6', '3', '7', '1', '2', '8', '8', '3', '6', '0', '5', '6', '1', '0', '0', '3', '5', '2', '4', '0', '9', '9', '6', '4', '0', '2', '1', '0', '3', '9', '3', '1', '7', '2', '7', '0', '5', '9', '6', '1', '0', '5', '4', '0', '6', '2', '5', '0', '0', '/', '7', '0', '9', '7', '9', '0', '4', '4', '0', '5', '2', '1', '1', '9', '6', '3', '1', '6', '6', '9', '5', '6', '3', '0', '7', '2', '1', '5', '6', '1', '0', '7', '2', '5', '5', '1', '3', '9', '8', '7', '0', '9', '9', '5', '4', '4', '6', '8', '1', '7', '1', '9', '7', '4', '2', '8', '9', '8', '2', '5', '6', '4', '7'])
noncomputable def fragment0121338Acc00700 : List (String × SourceJson) := (fragment0121338Field006Key00, fragment0121338Field006Value00) :: fragment0121338Acc00600
noncomputable def fragment0121338Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '6', '3', '7', '1', '2', '8', '8', '3', '6', '0', '5', '6', '1', '0', '0', '3', '5', '2', '4', '0', '9', '9', '6', '4', '0', '2', '1', '0', '3', '9', '3', '1', '7', '2', '7', '0', '5', '9', '6', '1', '0', '5', '4', '0', '6', '2', '5', '0', '0', '/', '7', '0', '9', '7', '9', '0', '4', '4', '0', '5', '2', '1', '1', '9', '6', '3', '1', '6', '6', '9', '5', '6', '3', '0', '7', '2', '1', '5', '6', '1', '0', '7', '2', '5', '5', '1', '3', '9', '8', '7', '0', '9', '9', '5', '4', '4', '6', '8', '1', '7', '1', '9', '7', '4', '2', '8', '9', '8', '2', '5', '6', '4', '7', '"', ',']

theorem object_fragment0121338_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 240) (SourceJson.white (fragment0121338Field006Chars00 ++ tail)) fragment0121338Acc00600 =
      SourceJson.object (fuel + 239) (SourceJson.white tail) fragment0121338Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121338_object_field_006"
  err.flush

noncomputable def fragment0121338Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0121338Field007Value00 : SourceJson := .str (String.ofList ['3', '3', '2', '6', '4', '4', '1', '2', '1', '4', '9', '8', '9', '2', '5', '5', '0', '7', '8', '4', '2', '2', '2', '4', '2', '6', '8', '8', '3', '4', '1', '4', '9', '1', '3', '0', '4', '4', '9', '3', '8', '7', '1', '5', '9', '6', '1', '4', '5', '8', '0', '3', '0', '3', '3', '5', '0', '5', '7', '8', '9', '0', '9', '8', '6', '4', '1', '9', '9', '4', '6', '9', '0', '7', '2', '5', '8', '3', '8', '8', '1', '1', '9', '0', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '6', '9', '2', '3', '0', '0', '7', '2', '5', '9', '6', '1', '6', '4', '7', '7', '3', '2', '8', '4', '2', '7', '0', '3', '4', '5', '7', '8', '2', '1', '2', '1', '6', '5', '5', '4', '2', '2', '5', '8', '1', '9', '6', '7', '7', '9', '1', '9', '0', '3', '2', '4', '1', '4', '2', '4', '8', '2', '4', '2', '1', '3', '7', '2', '1', '8', '0', '1', '3', '0', '8', '9', '1', '9', '5', '8', '3', '0', '0', '5', '7', '8', '1', '5', '4', '3', '8', '0', '0', '2', '6', '5', '5', '4', '7', '7', '9', '4', '4', '3', '5', '7', '2', '6', '6', '3', '2', '1', '8', '6', '3', '1', '7', '5', '9', '3', '2', '9', '8', '3', '4', '7'])
noncomputable def fragment0121338Acc00800 : List (String × SourceJson) := (fragment0121338Field007Key00, fragment0121338Field007Value00) :: fragment0121338Acc00700
noncomputable def fragment0121338Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '3', '2', '6', '4', '4', '1', '2', '1', '4', '9', '8', '9', '2', '5', '5', '0', '7', '8', '4', '2', '2', '2', '4', '2', '6', '8', '8', '3', '4', '1', '4', '9', '1', '3', '0', '4', '4', '9', '3', '8', '7', '1', '5', '9', '6', '1', '4', '5', '8', '0', '3', '0', '3', '3', '5', '0', '5', '7', '8', '9', '0', '9', '8', '6', '4', '1', '9', '9', '4', '6', '9', '0', '7', '2', '5', '8', '3', '8', '8', '1', '1', '9', '0', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '6', '9', '2', '3', '0', '0', '7', '2', '5', '9', '6', '1', '6', '4', '7', '7', '3', '2', '8', '4', '2', '7', '0', '3', '4', '5', '7', '8', '2', '1', '2', '1', '6', '5', '5', '4', '2', '2', '5', '8', '1', '9', '6', '7', '7', '9', '1', '9', '0', '3', '2', '4', '1', '4', '2', '4', '8', '2', '4', '2', '1', '3', '7', '2', '1', '8', '0', '1', '3', '0', '8', '9', '1', '9', '5', '8', '3', '0', '0', '5', '7', '8', '1', '5', '4', '3', '8', '0', '0', '2', '6', '5', '5', '4', '7', '7', '9', '4', '4', '3', '5', '7', '2', '6', '6', '3', '2', '1', '8', '6', '3', '1', '7', '5', '9', '3', '2', '9', '8', '3', '4', '7', '"', ',']

theorem object_fragment0121338_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0121338Field007Chars00 ++ tail)) fragment0121338Acc00700 =
      SourceJson.object (fuel + 238) (SourceJson.white tail) fragment0121338Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121338_object_field_007"
  err.flush

noncomputable def fragment0121338Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0121338Field008Value00 : SourceJson := .str (String.ofList ['4', '0', '5', '9', '8', '3', '2', '5', '6', '5', '4', '6', '4', '9', '9', '6'])
noncomputable def fragment0121338Acc00900 : List (String × SourceJson) := (fragment0121338Field008Key00, fragment0121338Field008Value00) :: fragment0121338Acc00800
noncomputable def fragment0121338Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '5', '9', '8', '3', '2', '5', '6', '5', '4', '6', '4', '9', '9', '6', '"', ',']

theorem object_fragment0121338_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0121338Field008Chars00 ++ tail)) fragment0121338Acc00800 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment0121338Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121338_object_field_008"
  err.flush

noncomputable def fragment0121338Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0121338Field009Value00 : SourceJson := .str (String.ofList ['1', '6', '7', '9', '4', '7', '2', '1', '8', '0', '5', '1', '5', '2', '3', '1', '6'])
noncomputable def fragment0121338Acc01000 : List (String × SourceJson) := (fragment0121338Field009Key00, fragment0121338Field009Value00) :: fragment0121338Acc00900
noncomputable def fragment0121338Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '7', '9', '4', '7', '2', '1', '8', '0', '5', '1', '5', '2', '3', '1', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0121338_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0121338Field009Chars00 ++ tail)) fragment0121338Acc00900 =
      .ok (.obj (fragment0121338Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121338_object_field_009"
  err.flush

noncomputable def fragment0121338Chars : List Char := '{' :: (fragment0121338Field000Chars00 ++ fragment0121338Field001Chars00 ++ fragment0121338Field002Chars00 ++ fragment0121338Field003Chars00 ++ fragment0121338Field004Chars00 ++ fragment0121338Field005Chars00 ++ fragment0121338Field006Chars00 ++ fragment0121338Field007Chars00 ++ fragment0121338Field008Chars00 ++ fragment0121338Field009Chars00)
noncomputable def fragment0121338Value : SourceJson := .obj (fragment0121338Acc01000.reverse)

theorem value_fragment0121338 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 247) (fragment0121338Chars ++ tail) =
      .ok (fragment0121338Value, tail) := by
  have hinput : fragment0121338Chars ++ tail = '{' :: (fragment0121338Field000Chars00 ++ (fragment0121338Field001Chars00 ++ (fragment0121338Field002Chars00 ++ (fragment0121338Field003Chars00 ++ (fragment0121338Field004Chars00 ++ (fragment0121338Field005Chars00 ++ (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0121338Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 247) (fragment0121338Chars ++ tail) =
        SourceJson.value (fuel + 247) ('{' :: (fragment0121338Field000Chars00 ++ (fragment0121338Field001Chars00 ++ (fragment0121338Field002Chars00 ++ (fragment0121338Field003Chars00 ++ (fragment0121338Field004Chars00 ++ (fragment0121338Field005Chars00 ++ (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 247)) hinput
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0121338Field000Chars00 ++ (fragment0121338Field001Chars00 ++ (fragment0121338Field002Chars00 ++ (fragment0121338Field003Chars00 ++ (fragment0121338Field004Chars00 ++ (fragment0121338Field005Chars00 ++ (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail)))))))))))) fragment0121338Acc00000 := by rfl
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0121338Field001Chars00 ++ (fragment0121338Field002Chars00 ++ (fragment0121338Field003Chars00 ++ (fragment0121338Field004Chars00 ++ (fragment0121338Field005Chars00 ++ (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail))))))))))) fragment0121338Acc00100 := object_fragment0121338_field_000 fuel (fragment0121338Field001Chars00 ++ (fragment0121338Field002Chars00 ++ (fragment0121338Field003Chars00 ++ (fragment0121338Field004Chars00 ++ (fragment0121338Field005Chars00 ++ (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0121338Field002Chars00 ++ (fragment0121338Field003Chars00 ++ (fragment0121338Field004Chars00 ++ (fragment0121338Field005Chars00 ++ (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail)))))))))) fragment0121338Acc00200 := object_fragment0121338_field_001 fuel (fragment0121338Field002Chars00 ++ (fragment0121338Field003Chars00 ++ (fragment0121338Field004Chars00 ++ (fragment0121338Field005Chars00 ++ (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0121338Field003Chars00 ++ (fragment0121338Field004Chars00 ++ (fragment0121338Field005Chars00 ++ (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail))))))))) fragment0121338Acc00300 := object_fragment0121338_field_002 fuel (fragment0121338Field003Chars00 ++ (fragment0121338Field004Chars00 ++ (fragment0121338Field005Chars00 ++ (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0121338Field004Chars00 ++ (fragment0121338Field005Chars00 ++ (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail)))))))) fragment0121338Acc00400 := object_fragment0121338_field_003 fuel (fragment0121338Field004Chars00 ++ (fragment0121338Field005Chars00 ++ (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0121338Field005Chars00 ++ (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail))))))) fragment0121338Acc00500 := object_fragment0121338_field_004 fuel (fragment0121338Field005Chars00 ++ (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 240) (SourceJson.white (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail)))))) fragment0121338Acc00600 := object_fragment0121338_field_005 fuel (fragment0121338Field006Chars00 ++ (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail))))) fragment0121338Acc00700 := object_fragment0121338_field_006 fuel (fragment0121338Field007Chars00 ++ (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail)))) fragment0121338Acc00800 := object_fragment0121338_field_007 fuel (fragment0121338Field008Chars00 ++ (fragment0121338Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0121338Field009Chars00 ++ (tail))) fragment0121338Acc00900 := object_fragment0121338_field_008 fuel (fragment0121338Field009Chars00 ++ (tail))
    _ = .ok (fragment0121338Value, tail) := object_fragment0121338_field_009 fuel (tail)

noncomputable def fragment0122954Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0122954Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0122954Field000Value00 : SourceJson := .number (String.ofList ['1', '1'])
noncomputable def fragment0122954Acc00100 : List (String × SourceJson) := (fragment0122954Field000Key00, fragment0122954Field000Value00) :: fragment0122954Acc00000
noncomputable def fragment0122954Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', ',']

theorem object_fragment0122954_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0122954Field000Chars00 ++ tail)) fragment0122954Acc00000 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0122954Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122954_object_field_000"
  err.flush

noncomputable def fragment0122954Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0122954Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '1']), .number (String.ofList ['9']), .number (String.ofList ['8']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0122954Acc00200 : List (String × SourceJson) := (fragment0122954Field001Key00, fragment0122954Field001Value00) :: fragment0122954Acc00100
noncomputable def fragment0122954Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0122954_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0122954Field001Chars00 ++ tail)) fragment0122954Acc00100 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0122954Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122954_object_field_001"
  err.flush

noncomputable def fragment0122954Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0122954Field002Value00 : SourceJson := .str (String.ofList ['5', '2', '1', '0', '6', '4', '3', '9', '8', '4', '7', '0', '4', '3', '7', '3', '9', '9', '1', '0', '0', '5', '0', '2', '3', '1', '8', '3', '8', '0', '7', '0', '0', '2', '0', '0', '3', '/', '2', '2', '1', '2', '1', '7', '6', '8', '1', '6', '7', '8', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0122954Acc00300 : List (String × SourceJson) := (fragment0122954Field002Key00, fragment0122954Field002Value00) :: fragment0122954Acc00200
noncomputable def fragment0122954Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '2', '1', '0', '6', '4', '3', '9', '8', '4', '7', '0', '4', '3', '7', '3', '9', '9', '1', '0', '0', '5', '0', '2', '3', '1', '8', '3', '8', '0', '7', '0', '0', '2', '0', '0', '3', '/', '2', '2', '1', '2', '1', '7', '6', '8', '1', '6', '7', '8', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0122954_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0122954Field002Chars00 ++ tail)) fragment0122954Acc00200 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0122954Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122954_object_field_002"
  err.flush

noncomputable def fragment0122954Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0122954Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0122954Acc00400 : List (String × SourceJson) := (fragment0122954Field003Key00, fragment0122954Field003Value00) :: fragment0122954Acc00300
noncomputable def fragment0122954Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0122954_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0122954Field003Chars00 ++ tail)) fragment0122954Acc00300 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0122954Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122954_object_field_003"
  err.flush

noncomputable def fragment0122954Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0122954Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0122954Acc00500 : List (String × SourceJson) := (fragment0122954Field004Key00, fragment0122954Field004Value00) :: fragment0122954Acc00400
noncomputable def fragment0122954Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0122954_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0122954Field004Chars00 ++ tail)) fragment0122954Acc00400 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0122954Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122954_object_field_004"
  err.flush

noncomputable def fragment0122954Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0122954Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '3', '9', '9', '1', '9', '3', '3', '0', '0', '8', '5', '1', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '1', '1', '7', '9', '8', '3', '7', '9', '2', '8', '1', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '1', '4', '0', '4', '6', '9', '2', '2', '1', '7', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '1', '8', '1', '6', '2', '8', '9', '7', '9', '9', '1', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '4', '0', '9', '0', '4', '3', '3', '0', '3', '7', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '7', '2', '7', '3', '7', '7', '6', '5', '5', '1', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '2', '7', '1', '3', '1', '0', '5', '8', '3', '4', '3', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '1', '2', '9', '1', '3', '9', '2', '2', '9', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '3', '5', '0', '9', '8', '4', '5', '1', '5', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '6', '9', '6', '9', '2', '7', '0', '3', '2', '0', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0122954Acc00600 : List (String × SourceJson) := (fragment0122954Field005Key00, fragment0122954Field005Value00) :: fragment0122954Acc00500
noncomputable def fragment0122954Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '9', '1', '9', '3', '3', '0', '0', '8', '5', '1', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '1', '1', '7', '9', '8', '3', '7', '9', '2', '8', '1', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '1', '4', '0', '4', '6', '9', '2', '2', '1', '7', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '1', '8', '1', '6', '2', '8', '9', '7', '9', '9', '1', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '4', '0', '9', '0', '4', '3', '3', '0', '3', '7', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '7', '2', '7', '3', '7', '7', '6', '5', '5', '1', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '7', '1', '3', '1', '0', '5', '8', '3', '4', '3', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '1', '2', '9', '1', '3', '9', '2', '2', '9', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '3', '5', '0', '9', '8', '4', '5', '1', '5', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '6', '9', '6', '9', '2', '7', '0', '3', '2', '0', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0122954_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0122954Field005Chars00 ++ tail)) fragment0122954Acc00500 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0122954Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122954_object_field_005"
  err.flush

noncomputable def fragment0122954Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0122954Field006Value00 : SourceJson := .str (String.ofList ['6', '2', '1', '4', '8', '9', '6', '1', '3', '6', '8', '2', '5', '5', '2', '4', '9', '9', '4', '2', '6', '7', '7', '7', '6', '7', '6', '1', '1', '3', '4', '1', '1', '0', '7', '7', '8', '1', '3', '0', '9', '2', '0', '0', '0', '0', '0', '0', '0', '/', '8', '4', '7', '6', '1', '0', '0', '2', '1', '9', '9', '7', '3', '8', '8', '6', '2', '7', '1', '7', '1', '0', '3', '7', '6', '3', '3', '8', '8', '2', '6', '1', '3', '3', '5', '9', '7', '0', '1', '0', '9', '7', '7', '0', '9', '4', '4', '0', '4', '3', '2', '4', '8', '4', '0', '7', '3', '3', '0', '2', '4', '8', '8', '2', '4', '1'])
noncomputable def fragment0122954Acc00700 : List (String × SourceJson) := (fragment0122954Field006Key00, fragment0122954Field006Value00) :: fragment0122954Acc00600
noncomputable def fragment0122954Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '2', '1', '4', '8', '9', '6', '1', '3', '6', '8', '2', '5', '5', '2', '4', '9', '9', '4', '2', '6', '7', '7', '7', '6', '7', '6', '1', '1', '3', '4', '1', '1', '0', '7', '7', '8', '1', '3', '0', '9', '2', '0', '0', '0', '0', '0', '0', '0', '/', '8', '4', '7', '6', '1', '0', '0', '2', '1', '9', '9', '7', '3', '8', '8', '6', '2', '7', '1', '7', '1', '0', '3', '7', '6', '3', '3', '8', '8', '2', '6', '1', '3', '3', '5', '9', '7', '0', '1', '0', '9', '7', '7', '0', '9', '4', '4', '0', '4', '3', '2', '4', '8', '4', '0', '7', '3', '3', '0', '2', '4', '8', '8', '2', '4', '1', '"', ',']

theorem object_fragment0122954_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0122954Field006Chars00 ++ tail)) fragment0122954Acc00600 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0122954Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122954_object_field_006"
  err.flush

noncomputable def fragment0122954Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0122954Field007Value00 : SourceJson := .str (String.ofList ['2', '1', '8', '1', '7', '5', '2', '9', '2', '2', '1', '5', '2', '1', '9', '8', '4', '5', '2', '2', '8', '3', '9', '8', '7', '5', '6', '6', '0', '9', '0', '8', '4', '5', '4', '0', '9', '6', '8', '9', '1', '9', '3', '8', '2', '9', '3', '8', '8', '9', '3', '6', '3', '1', '7', '7', '2', '1', '3', '1', '8', '4', '3', '1', '2', '8', '5', '9', '4', '4', '1', '1', '0', '6', '8', '1', '1', '6', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '3', '3', '4', '0', '3', '7', '3', '9', '1', '0', '8', '0', '0', '4', '2', '2', '0', '8', '1', '8', '4', '4', '6', '1', '2', '1', '3', '1', '7', '0', '5', '5', '0', '5', '8', '9', '4', '3', '0', '4', '7', '2', '1', '2', '0', '8', '3', '3', '0', '4', '9', '4', '7', '6', '7', '4', '7', '0', '0', '3', '3', '6', '0', '0', '6', '5', '0', '2', '9', '9', '0', '8', '5', '8', '2', '8', '9', '9', '7', '4', '9', '5', '9', '4', '5', '3', '9', '6', '5', '3', '5', '9', '7', '6', '8', '5', '0', '6', '8', '1', '2', '5', '8', '5', '6', '6', '6', '6', '6', '7', '2', '5', '8', '3', '4', '5', '1', '5', '6', '7'])
noncomputable def fragment0122954Acc00800 : List (String × SourceJson) := (fragment0122954Field007Key00, fragment0122954Field007Value00) :: fragment0122954Acc00700
noncomputable def fragment0122954Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '8', '1', '7', '5', '2', '9', '2', '2', '1', '5', '2', '1', '9', '8', '4', '5', '2', '2', '8', '3', '9', '8', '7', '5', '6', '6', '0', '9', '0', '8', '4', '5', '4', '0', '9', '6', '8', '9', '1', '9', '3', '8', '2', '9', '3', '8', '8', '9', '3', '6', '3', '1', '7', '7', '2', '1', '3', '1', '8', '4', '3', '1', '2', '8', '5', '9', '4', '4', '1', '1', '0', '6', '8', '1', '1', '6', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '3', '3', '4', '0', '3', '7', '3', '9', '1', '0', '8', '0', '0', '4', '2', '2', '0', '8', '1', '8', '4', '4', '6', '1', '2', '1', '3', '1', '7', '0', '5', '5', '0', '5', '8', '9', '4', '3', '0', '4', '7', '2', '1', '2', '0', '8', '3', '3', '0', '4', '9', '4', '7', '6', '7', '4', '7', '0', '0', '3', '3', '6', '0', '0', '6', '5', '0', '2', '9', '9', '0', '8', '5', '8', '2', '8', '9', '9', '7', '4', '9', '5', '9', '4', '5', '3', '9', '6', '5', '3', '5', '9', '7', '6', '8', '5', '0', '6', '8', '1', '2', '5', '8', '5', '6', '6', '6', '6', '6', '7', '2', '5', '8', '3', '4', '5', '1', '5', '6', '7', '"', ',']

theorem object_fragment0122954_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0122954Field007Chars00 ++ tail)) fragment0122954Acc00700 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0122954Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122954_object_field_007"
  err.flush

noncomputable def fragment0122954Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0122954Field008Value00 : SourceJson := .str (String.ofList ['5', '8', '0', '9', '2', '1', '4', '0', '0', '5', '9', '5'])
noncomputable def fragment0122954Acc00900 : List (String × SourceJson) := (fragment0122954Field008Key00, fragment0122954Field008Value00) :: fragment0122954Acc00800
noncomputable def fragment0122954Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '8', '0', '9', '2', '1', '4', '0', '0', '5', '9', '5', '"', ',']

theorem object_fragment0122954_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0122954Field008Chars00 ++ tail)) fragment0122954Acc00800 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0122954Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122954_object_field_008"
  err.flush

noncomputable def fragment0122954Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0122954Field009Value00 : SourceJson := .str (String.ofList ['2', '3', '5', '6', '9', '0', '4', '7', '4', '2', '4', '3', '3'])
noncomputable def fragment0122954Acc01000 : List (String × SourceJson) := (fragment0122954Field009Key00, fragment0122954Field009Value00) :: fragment0122954Acc00900
noncomputable def fragment0122954Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '5', '6', '9', '0', '4', '7', '4', '2', '4', '3', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0122954_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0122954Field009Chars00 ++ tail)) fragment0122954Acc00900 =
      .ok (.obj (fragment0122954Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122954_object_field_009"
  err.flush

noncomputable def fragment0122954Chars : List Char := '{' :: (fragment0122954Field000Chars00 ++ fragment0122954Field001Chars00 ++ fragment0122954Field002Chars00 ++ fragment0122954Field003Chars00 ++ fragment0122954Field004Chars00 ++ fragment0122954Field005Chars00 ++ fragment0122954Field006Chars00 ++ fragment0122954Field007Chars00 ++ fragment0122954Field008Chars00 ++ fragment0122954Field009Chars00)
noncomputable def fragment0122954Value : SourceJson := .obj (fragment0122954Acc01000.reverse)

theorem value_fragment0122954 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 238) (fragment0122954Chars ++ tail) =
      .ok (fragment0122954Value, tail) := by
  have hinput : fragment0122954Chars ++ tail = '{' :: (fragment0122954Field000Chars00 ++ (fragment0122954Field001Chars00 ++ (fragment0122954Field002Chars00 ++ (fragment0122954Field003Chars00 ++ (fragment0122954Field004Chars00 ++ (fragment0122954Field005Chars00 ++ (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0122954Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 238) (fragment0122954Chars ++ tail) =
        SourceJson.value (fuel + 238) ('{' :: (fragment0122954Field000Chars00 ++ (fragment0122954Field001Chars00 ++ (fragment0122954Field002Chars00 ++ (fragment0122954Field003Chars00 ++ (fragment0122954Field004Chars00 ++ (fragment0122954Field005Chars00 ++ (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 238)) hinput
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0122954Field000Chars00 ++ (fragment0122954Field001Chars00 ++ (fragment0122954Field002Chars00 ++ (fragment0122954Field003Chars00 ++ (fragment0122954Field004Chars00 ++ (fragment0122954Field005Chars00 ++ (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail)))))))))))) fragment0122954Acc00000 := by rfl
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0122954Field001Chars00 ++ (fragment0122954Field002Chars00 ++ (fragment0122954Field003Chars00 ++ (fragment0122954Field004Chars00 ++ (fragment0122954Field005Chars00 ++ (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail))))))))))) fragment0122954Acc00100 := object_fragment0122954_field_000 fuel (fragment0122954Field001Chars00 ++ (fragment0122954Field002Chars00 ++ (fragment0122954Field003Chars00 ++ (fragment0122954Field004Chars00 ++ (fragment0122954Field005Chars00 ++ (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0122954Field002Chars00 ++ (fragment0122954Field003Chars00 ++ (fragment0122954Field004Chars00 ++ (fragment0122954Field005Chars00 ++ (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail)))))))))) fragment0122954Acc00200 := object_fragment0122954_field_001 fuel (fragment0122954Field002Chars00 ++ (fragment0122954Field003Chars00 ++ (fragment0122954Field004Chars00 ++ (fragment0122954Field005Chars00 ++ (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0122954Field003Chars00 ++ (fragment0122954Field004Chars00 ++ (fragment0122954Field005Chars00 ++ (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail))))))))) fragment0122954Acc00300 := object_fragment0122954_field_002 fuel (fragment0122954Field003Chars00 ++ (fragment0122954Field004Chars00 ++ (fragment0122954Field005Chars00 ++ (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0122954Field004Chars00 ++ (fragment0122954Field005Chars00 ++ (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail)))))))) fragment0122954Acc00400 := object_fragment0122954_field_003 fuel (fragment0122954Field004Chars00 ++ (fragment0122954Field005Chars00 ++ (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0122954Field005Chars00 ++ (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail))))))) fragment0122954Acc00500 := object_fragment0122954_field_004 fuel (fragment0122954Field005Chars00 ++ (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail)))))) fragment0122954Acc00600 := object_fragment0122954_field_005 fuel (fragment0122954Field006Chars00 ++ (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail))))) fragment0122954Acc00700 := object_fragment0122954_field_006 fuel (fragment0122954Field007Chars00 ++ (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail)))) fragment0122954Acc00800 := object_fragment0122954_field_007 fuel (fragment0122954Field008Chars00 ++ (fragment0122954Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0122954Field009Chars00 ++ (tail))) fragment0122954Acc00900 := object_fragment0122954_field_008 fuel (fragment0122954Field009Chars00 ++ (tail))
    _ = .ok (fragment0122954Value, tail) := object_fragment0122954_field_009 fuel (tail)

noncomputable def fragment0124549Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0124549Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0124549Field000Value00 : SourceJson := .number (String.ofList ['1', '2'])
noncomputable def fragment0124549Acc00100 : List (String × SourceJson) := (fragment0124549Field000Key00, fragment0124549Field000Value00) :: fragment0124549Acc00000
noncomputable def fragment0124549Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', ',']

theorem object_fragment0124549_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0124549Field000Chars00 ++ tail)) fragment0124549Acc00000 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0124549Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124549_object_field_000"
  err.flush

noncomputable def fragment0124549Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0124549Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0124549Acc00200 : List (String × SourceJson) := (fragment0124549Field001Key00, fragment0124549Field001Value00) :: fragment0124549Acc00100
noncomputable def fragment0124549Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0124549_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0124549Field001Chars00 ++ tail)) fragment0124549Acc00100 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0124549Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124549_object_field_001"
  err.flush

noncomputable def fragment0124549Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0124549Field002Value00 : SourceJson := .str (String.ofList ['1', '7', '0', '9', '2', '2', '1', '4', '9', '0', '0', '3', '2', '6', '0', '2', '9', '0', '4', '5', '6', '1', '3', '8', '8', '3', '8', '8', '5', '1', '4', '9', '6', '1', '7', '3', '6', '5', '4', '6', '0', '1', '1', '/', '7', '0', '7', '8', '9', '6', '5', '8', '1', '3', '7', '0', '6', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0124549Acc00300 : List (String × SourceJson) := (fragment0124549Field002Key00, fragment0124549Field002Value00) :: fragment0124549Acc00200
noncomputable def fragment0124549Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '7', '0', '9', '2', '2', '1', '4', '9', '0', '0', '3', '2', '6', '0', '2', '9', '0', '4', '5', '6', '1', '3', '8', '8', '3', '8', '8', '5', '1', '4', '9', '6', '1', '7', '3', '6', '5', '4', '6', '0', '1', '1', '/', '7', '0', '7', '8', '9', '6', '5', '8', '1', '3', '7', '0', '6', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0124549_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0124549Field002Chars00 ++ tail)) fragment0124549Acc00200 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0124549Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124549_object_field_002"
  err.flush

noncomputable def fragment0124549Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0124549Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0124549Acc00400 : List (String × SourceJson) := (fragment0124549Field003Key00, fragment0124549Field003Value00) :: fragment0124549Acc00300
noncomputable def fragment0124549Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0124549_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0124549Field003Chars00 ++ tail)) fragment0124549Acc00300 =
      SourceJson.object (fuel + 240) (SourceJson.white tail) fragment0124549Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124549_object_field_003"
  err.flush

noncomputable def fragment0124549Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0124549Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0124549Acc00500 : List (String × SourceJson) := (fragment0124549Field004Key00, fragment0124549Field004Value00) :: fragment0124549Acc00400
noncomputable def fragment0124549Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0124549_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 240) (SourceJson.white (fragment0124549Field004Chars00 ++ tail)) fragment0124549Acc00400 =
      SourceJson.object (fuel + 239) (SourceJson.white tail) fragment0124549Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124549_object_field_004"
  err.flush

noncomputable def fragment0124549Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0124549Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '8', '3', '4', '1', '0', '4', '4', '7', '4', '9', '0', '7', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '5', '9', '3', '1', '4', '6', '3', '1', '7', '6', '7', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '1', '4', '0', '4', '6', '9', '2', '2', '1', '7', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '8', '4', '6', '9', '3', '2', '1', '7', '1', '9', '/', '1', '3', '0', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '4', '0', '9', '0', '4', '3', '3', '0', '3', '7', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '7', '2', '7', '3', '7', '7', '6', '5', '5', '1', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '2', '7', '1', '3', '1', '0', '5', '8', '3', '4', '3', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '1', '2', '9', '1', '3', '9', '2', '2', '9', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '5', '1', '3', '0', '1', '8', '1', '7', '1', '0', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '6', '7', '1', '0', '1', '7', '5', '2', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0124549Acc00600 : List (String × SourceJson) := (fragment0124549Field005Key00, fragment0124549Field005Value00) :: fragment0124549Acc00500
noncomputable def fragment0124549Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '3', '4', '1', '0', '4', '4', '7', '4', '9', '0', '7', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '5', '9', '3', '1', '4', '6', '3', '1', '7', '6', '7', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '1', '4', '0', '4', '6', '9', '2', '2', '1', '7', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '8', '4', '6', '9', '3', '2', '1', '7', '1', '9', '/', '1', '3', '0', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '4', '0', '9', '0', '4', '3', '3', '0', '3', '7', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '7', '2', '7', '3', '7', '7', '6', '5', '5', '1', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '7', '1', '3', '1', '0', '5', '8', '3', '4', '3', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '1', '2', '9', '1', '3', '9', '2', '2', '9', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '1', '3', '0', '1', '8', '1', '7', '1', '0', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '6', '7', '1', '0', '1', '7', '5', '2', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0124549_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0124549Field005Chars00 ++ tail)) fragment0124549Acc00500 =
      SourceJson.object (fuel + 238) (SourceJson.white tail) fragment0124549Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124549_object_field_005"
  err.flush

noncomputable def fragment0124549Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0124549Field006Value00 : SourceJson := .str (String.ofList ['7', '0', '0', '7', '8', '2', '9', '4', '7', '4', '4', '0', '2', '2', '9', '7', '3', '1', '6', '2', '3', '7', '9', '9', '9', '4', '1', '0', '2', '6', '6', '1', '9', '9', '5', '5', '6', '8', '6', '0', '3', '5', '1', '9', '2', '5', '1', '3', '7', '5', '0', '0', '0', '0', '/', '9', '3', '2', '3', '7', '1', '0', '2', '4', '1', '9', '7', '1', '2', '7', '4', '8', '9', '8', '8', '8', '1', '4', '1', '3', '9', '7', '2', '7', '0', '8', '7', '4', '6', '9', '5', '6', '7', '1', '2', '0', '7', '4', '8', '0', '3', '8', '4', '4', '7', '5', '7', '3', '2', '4', '8', '0', '6', '3', '2', '7', '3', '7', '0', '6', '5', '1'])
noncomputable def fragment0124549Acc00700 : List (String × SourceJson) := (fragment0124549Field006Key00, fragment0124549Field006Value00) :: fragment0124549Acc00600
noncomputable def fragment0124549Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '0', '0', '7', '8', '2', '9', '4', '7', '4', '4', '0', '2', '2', '9', '7', '3', '1', '6', '2', '3', '7', '9', '9', '9', '4', '1', '0', '2', '6', '6', '1', '9', '9', '5', '5', '6', '8', '6', '0', '3', '5', '1', '9', '2', '5', '1', '3', '7', '5', '0', '0', '0', '0', '/', '9', '3', '2', '3', '7', '1', '0', '2', '4', '1', '9', '7', '1', '2', '7', '4', '8', '9', '8', '8', '8', '1', '4', '1', '3', '9', '7', '2', '7', '0', '8', '7', '4', '6', '9', '5', '6', '7', '1', '2', '0', '7', '4', '8', '0', '3', '8', '4', '4', '7', '5', '7', '3', '2', '4', '8', '0', '6', '3', '2', '7', '3', '7', '0', '6', '5', '1', '"', ',']

theorem object_fragment0124549_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0124549Field006Chars00 ++ tail)) fragment0124549Acc00600 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment0124549Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124549_object_field_006"
  err.flush

noncomputable def fragment0124549Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0124549Field007Value00 : SourceJson := .str (String.ofList ['9', '8', '4', '0', '4', '5', '5', '6', '3', '8', '9', '1', '3', '4', '3', '6', '3', '1', '7', '3', '9', '3', '3', '9', '5', '9', '1', '6', '4', '0', '5', '0', '6', '6', '7', '0', '8', '5', '1', '6', '7', '5', '8', '6', '6', '6', '8', '8', '6', '3', '8', '3', '9', '5', '7', '9', '3', '7', '0', '7', '2', '3', '6', '7', '4', '2', '5', '8', '1', '1', '5', '7', '5', '0', '3', '1', '0', '8', '1', '5', '5', '5', '9', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '6', '8', '5', '5', '7', '7', '7', '3', '6', '7', '8', '0', '4', '4', '9', '8', '3', '6', '6', '3', '4', '6', '4', '0', '3', '3', '6', '4', '2', '4', '7', '0', '5', '9', '6', '5', '8', '2', '3', '3', '1', '1', '6', '7', '2', '9', '7', '2', '9', '7', '3', '0', '5', '4', '8', '8', '9', '3', '3', '4', '7', '7', '3', '6', '4', '7', '3', '7', '3', '9', '0', '4', '1', '8', '8', '9', '0', '7', '3', '2', '8', '6', '5', '7', '3', '5', '3', '7', '1', '1', '2', '7', '8', '1', '7', '0', '1', '6', '0', '3', '8', '8', '6', '4', '7', '8', '6', '8', '5', '2', '9', '3', '7', '2', '4', '6', '3', '4', '6', '1', '3'])
noncomputable def fragment0124549Acc00800 : List (String × SourceJson) := (fragment0124549Field007Key00, fragment0124549Field007Value00) :: fragment0124549Acc00700
noncomputable def fragment0124549Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '8', '4', '0', '4', '5', '5', '6', '3', '8', '9', '1', '3', '4', '3', '6', '3', '1', '7', '3', '9', '3', '3', '9', '5', '9', '1', '6', '4', '0', '5', '0', '6', '6', '7', '0', '8', '5', '1', '6', '7', '5', '8', '6', '6', '6', '8', '8', '6', '3', '8', '3', '9', '5', '7', '9', '3', '7', '0', '7', '2', '3', '6', '7', '4', '2', '5', '8', '1', '1', '5', '7', '5', '0', '3', '1', '0', '8', '1', '5', '5', '5', '9', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '6', '8', '5', '5', '7', '7', '7', '3', '6', '7', '8', '0', '4', '4', '9', '8', '3', '6', '6', '3', '4', '6', '4', '0', '3', '3', '6', '4', '2', '4', '7', '0', '5', '9', '6', '5', '8', '2', '3', '3', '1', '1', '6', '7', '2', '9', '7', '2', '9', '7', '3', '0', '5', '4', '8', '8', '9', '3', '3', '4', '7', '7', '3', '6', '4', '7', '3', '7', '3', '9', '0', '4', '1', '8', '8', '9', '0', '7', '3', '2', '8', '6', '5', '7', '3', '5', '3', '7', '1', '1', '2', '7', '8', '1', '7', '0', '1', '6', '0', '3', '8', '8', '6', '4', '7', '8', '6', '8', '5', '2', '9', '3', '7', '2', '4', '6', '3', '4', '6', '1', '3', '"', ',']

theorem object_fragment0124549_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0124549Field007Chars00 ++ tail)) fragment0124549Acc00700 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0124549Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124549_object_field_007"
  err.flush

noncomputable def fragment0124549Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0124549Field008Value00 : SourceJson := .str (String.ofList ['5', '9', '5', '4', '8', '9', '8', '1', '9', '0', '3', '2', '3', '9', '5', '6'])
noncomputable def fragment0124549Acc00900 : List (String × SourceJson) := (fragment0124549Field008Key00, fragment0124549Field008Value00) :: fragment0124549Acc00800
noncomputable def fragment0124549Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '5', '4', '8', '9', '8', '1', '9', '0', '3', '2', '3', '9', '5', '6', '"', ',']

theorem object_fragment0124549_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0124549Field008Chars00 ++ tail)) fragment0124549Acc00800 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0124549Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124549_object_field_008"
  err.flush

noncomputable def fragment0124549Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0124549Field009Value00 : SourceJson := .str (String.ofList ['2', '4', '6', '0', '5', '5', '5', '4', '7', '7', '4', '8', '2', '2', '3', '4', '0'])
noncomputable def fragment0124549Acc01000 : List (String × SourceJson) := (fragment0124549Field009Key00, fragment0124549Field009Value00) :: fragment0124549Acc00900
noncomputable def fragment0124549Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '6', '0', '5', '5', '5', '4', '7', '7', '4', '8', '2', '2', '3', '4', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0124549_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0124549Field009Chars00 ++ tail)) fragment0124549Acc00900 =
      .ok (.obj (fragment0124549Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124549_object_field_009"
  err.flush

noncomputable def fragment0124549Chars : List Char := '{' :: (fragment0124549Field000Chars00 ++ fragment0124549Field001Chars00 ++ fragment0124549Field002Chars00 ++ fragment0124549Field003Chars00 ++ fragment0124549Field004Chars00 ++ fragment0124549Field005Chars00 ++ fragment0124549Field006Chars00 ++ fragment0124549Field007Chars00 ++ fragment0124549Field008Chars00 ++ fragment0124549Field009Chars00)
noncomputable def fragment0124549Value : SourceJson := .obj (fragment0124549Acc01000.reverse)

theorem value_fragment0124549 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 245) (fragment0124549Chars ++ tail) =
      .ok (fragment0124549Value, tail) := by
  have hinput : fragment0124549Chars ++ tail = '{' :: (fragment0124549Field000Chars00 ++ (fragment0124549Field001Chars00 ++ (fragment0124549Field002Chars00 ++ (fragment0124549Field003Chars00 ++ (fragment0124549Field004Chars00 ++ (fragment0124549Field005Chars00 ++ (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0124549Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 245) (fragment0124549Chars ++ tail) =
        SourceJson.value (fuel + 245) ('{' :: (fragment0124549Field000Chars00 ++ (fragment0124549Field001Chars00 ++ (fragment0124549Field002Chars00 ++ (fragment0124549Field003Chars00 ++ (fragment0124549Field004Chars00 ++ (fragment0124549Field005Chars00 ++ (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 245)) hinput
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0124549Field000Chars00 ++ (fragment0124549Field001Chars00 ++ (fragment0124549Field002Chars00 ++ (fragment0124549Field003Chars00 ++ (fragment0124549Field004Chars00 ++ (fragment0124549Field005Chars00 ++ (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail)))))))))))) fragment0124549Acc00000 := by rfl
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0124549Field001Chars00 ++ (fragment0124549Field002Chars00 ++ (fragment0124549Field003Chars00 ++ (fragment0124549Field004Chars00 ++ (fragment0124549Field005Chars00 ++ (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail))))))))))) fragment0124549Acc00100 := object_fragment0124549_field_000 fuel (fragment0124549Field001Chars00 ++ (fragment0124549Field002Chars00 ++ (fragment0124549Field003Chars00 ++ (fragment0124549Field004Chars00 ++ (fragment0124549Field005Chars00 ++ (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0124549Field002Chars00 ++ (fragment0124549Field003Chars00 ++ (fragment0124549Field004Chars00 ++ (fragment0124549Field005Chars00 ++ (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail)))))))))) fragment0124549Acc00200 := object_fragment0124549_field_001 fuel (fragment0124549Field002Chars00 ++ (fragment0124549Field003Chars00 ++ (fragment0124549Field004Chars00 ++ (fragment0124549Field005Chars00 ++ (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0124549Field003Chars00 ++ (fragment0124549Field004Chars00 ++ (fragment0124549Field005Chars00 ++ (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail))))))))) fragment0124549Acc00300 := object_fragment0124549_field_002 fuel (fragment0124549Field003Chars00 ++ (fragment0124549Field004Chars00 ++ (fragment0124549Field005Chars00 ++ (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 240) (SourceJson.white (fragment0124549Field004Chars00 ++ (fragment0124549Field005Chars00 ++ (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail)))))))) fragment0124549Acc00400 := object_fragment0124549_field_003 fuel (fragment0124549Field004Chars00 ++ (fragment0124549Field005Chars00 ++ (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0124549Field005Chars00 ++ (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail))))))) fragment0124549Acc00500 := object_fragment0124549_field_004 fuel (fragment0124549Field005Chars00 ++ (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail)))))) fragment0124549Acc00600 := object_fragment0124549_field_005 fuel (fragment0124549Field006Chars00 ++ (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail))))) fragment0124549Acc00700 := object_fragment0124549_field_006 fuel (fragment0124549Field007Chars00 ++ (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail)))) fragment0124549Acc00800 := object_fragment0124549_field_007 fuel (fragment0124549Field008Chars00 ++ (fragment0124549Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0124549Field009Chars00 ++ (tail))) fragment0124549Acc00900 := object_fragment0124549_field_008 fuel (fragment0124549Field009Chars00 ++ (tail))
    _ = .ok (fragment0124549Value, tail) := object_fragment0124549_field_009 fuel (tail)

noncomputable def fragment0126175Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0126175Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0126175Field000Value00 : SourceJson := .number (String.ofList ['1', '3'])
noncomputable def fragment0126175Acc00100 : List (String × SourceJson) := (fragment0126175Field000Key00, fragment0126175Field000Value00) :: fragment0126175Acc00000
noncomputable def fragment0126175Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', ',']

theorem object_fragment0126175_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0126175Field000Chars00 ++ tail)) fragment0126175Acc00000 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0126175Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126175_object_field_000"
  err.flush

noncomputable def fragment0126175Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0126175Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0126175Acc00200 : List (String × SourceJson) := (fragment0126175Field001Key00, fragment0126175Field001Value00) :: fragment0126175Acc00100
noncomputable def fragment0126175Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0126175_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0126175Field001Chars00 ++ tail)) fragment0126175Acc00100 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0126175Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126175_object_field_001"
  err.flush

noncomputable def fragment0126175Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0126175Field002Value00 : SourceJson := .str (String.ofList ['2', '0', '4', '7', '0', '6', '5', '1', '2', '9', '2', '4', '2', '7', '8', '5', '5', '8', '1', '8', '2', '8', '7', '2', '1', '0', '5', '1', '0', '8', '5', '8', '1', '5', '0', '9', '/', '1', '3', '2', '5', '0', '0', '1', '7', '3', '9', '2', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0126175Acc00300 : List (String × SourceJson) := (fragment0126175Field002Key00, fragment0126175Field002Value00) :: fragment0126175Acc00200
noncomputable def fragment0126175Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '0', '4', '7', '0', '6', '5', '1', '2', '9', '2', '4', '2', '7', '8', '5', '5', '8', '1', '8', '2', '8', '7', '2', '1', '0', '5', '1', '0', '8', '5', '8', '1', '5', '0', '9', '/', '1', '3', '2', '5', '0', '0', '1', '7', '3', '9', '2', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0126175_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0126175Field002Chars00 ++ tail)) fragment0126175Acc00200 =
      SourceJson.object (fuel + 260) (SourceJson.white tail) fragment0126175Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126175_object_field_002"
  err.flush

noncomputable def fragment0126175Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0126175Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0126175Acc00400 : List (String × SourceJson) := (fragment0126175Field003Key00, fragment0126175Field003Value00) :: fragment0126175Acc00300
noncomputable def fragment0126175Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0126175_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0126175Field003Chars00 ++ tail)) fragment0126175Acc00300 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0126175Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126175_object_field_003"
  err.flush

noncomputable def fragment0126175Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0126175Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0126175Acc00500 : List (String × SourceJson) := (fragment0126175Field004Key00, fragment0126175Field004Value00) :: fragment0126175Acc00400
noncomputable def fragment0126175Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0126175_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0126175Field004Chars00 ++ tail)) fragment0126175Acc00400 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0126175Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126175_object_field_004"
  err.flush

noncomputable def fragment0126175Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0126175Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '5', '0', '6', '9', '0', '3', '1', '7', '0', '7', '8', '4', '3', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '3', '5', '8', '9', '4', '8', '5', '1', '1', '7', '3', '3', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '4', '5', '5', '7', '5', '6', '9', '2', '5', '6', '7', '/', '4', '8', '0', '8', '3', '6', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '0', '6', '1', '0', '5', '1', '4', '0', '2', '2', '3', '3', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '2', '3', '3', '1', '0', '8', '0', '0', '6', '1', '3', '9', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '9', '3', '1', '7', '2', '6', '3', '1', '8', '8', '2', '9', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '9', '1', '3', '0', '1', '8', '6', '4', '0', '0', '9', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '1', '5', '3', '4', '8', '8', '1', '4', '6', '1', '0', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '4', '1', '8', '0', '0', '0', '4', '1', '9', '0', '0', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '8', '7', '0', '2', '0', '6', '1', '5', '4', '1', '5', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0126175Acc00600 : List (String × SourceJson) := (fragment0126175Field005Key00, fragment0126175Field005Value00) :: fragment0126175Acc00500
noncomputable def fragment0126175Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '0', '6', '9', '0', '3', '1', '7', '0', '7', '8', '4', '3', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '3', '5', '8', '9', '4', '8', '5', '1', '1', '7', '3', '3', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '4', '5', '5', '7', '5', '6', '9', '2', '5', '6', '7', '/', '4', '8', '0', '8', '3', '6', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '0', '6', '1', '0', '5', '1', '4', '0', '2', '2', '3', '3', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '3', '3', '1', '0', '8', '0', '0', '6', '1', '3', '9', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '3', '1', '7', '2', '6', '3', '1', '8', '8', '2', '9', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '9', '1', '3', '0', '1', '8', '6', '4', '0', '0', '9', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '1', '5', '3', '4', '8', '8', '1', '4', '6', '1', '0', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '4', '1', '8', '0', '0', '0', '4', '1', '9', '0', '0', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '8', '7', '0', '2', '0', '6', '1', '5', '4', '1', '5', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0126175_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0126175Field005Chars00 ++ tail)) fragment0126175Acc00500 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0126175Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126175_object_field_005"
  err.flush

noncomputable def fragment0126175Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0126175Field006Value00 : SourceJson := .str (String.ofList ['1', '2', '5', '0', '0', '9', '8', '1', '0', '0', '5', '1', '5', '8', '6', '4', '0', '4', '2', '8', '2', '2', '5', '6', '7', '2', '5', '3', '6', '0', '1', '1', '8', '3', '9', '9', '5', '9', '6', '9', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '/', '2', '2', '9', '6', '1', '9', '0', '8', '6', '2', '7', '8', '7', '5', '1', '5', '9', '5', '6', '6', '2', '2', '2', '0', '0', '6', '2', '3', '5', '9', '3', '9', '5', '8', '8', '9', '2', '7', '3', '6', '2', '1', '4', '1', '9', '6', '3', '3', '7', '2', '2', '9', '3', '2', '8', '4', '6', '7', '2', '6', '6', '0', '0', '7', '9', '3', '7', '1'])
noncomputable def fragment0126175Acc00700 : List (String × SourceJson) := (fragment0126175Field006Key00, fragment0126175Field006Value00) :: fragment0126175Acc00600
noncomputable def fragment0126175Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '5', '0', '0', '9', '8', '1', '0', '0', '5', '1', '5', '8', '6', '4', '0', '4', '2', '8', '2', '2', '5', '6', '7', '2', '5', '3', '6', '0', '1', '1', '8', '3', '9', '9', '5', '9', '6', '9', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '/', '2', '2', '9', '6', '1', '9', '0', '8', '6', '2', '7', '8', '7', '5', '1', '5', '9', '5', '6', '6', '2', '2', '2', '0', '0', '6', '2', '3', '5', '9', '3', '9', '5', '8', '8', '9', '2', '7', '3', '6', '2', '1', '4', '1', '9', '6', '3', '3', '7', '2', '2', '9', '3', '2', '8', '4', '6', '7', '2', '6', '6', '0', '0', '7', '9', '3', '7', '1', '"', ',']

theorem object_fragment0126175_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0126175Field006Chars00 ++ tail)) fragment0126175Acc00600 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0126175Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126175_object_field_006"
  err.flush

noncomputable def fragment0126175Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0126175Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '8', '5', '6', '5', '2', '9', '0', '4', '9', '3', '1', '2', '1', '4', '6', '6', '4', '8', '6', '7', '9', '3', '0', '6', '9', '7', '2', '5', '5', '2', '2', '9', '1', '8', '9', '2', '4', '1', '2', '3', '0', '7', '5', '9', '1', '1', '1', '3', '9', '8', '8', '4', '3', '6', '5', '0', '0', '4', '2', '2', '5', '8', '8', '7', '6', '7', '9', '2', '2', '2', '1', '9', '6', '5', '8', '3', '1', '8', '1', '7', '6', '9', '0', '6', '1', '7', '8', '9', '8', '5', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '5', '4', '2', '2', '0', '3', '8', '0', '6', '6', '4', '3', '7', '8', '4', '2', '6', '3', '7', '7', '6', '0', '6', '3', '4', '5', '0', '4', '2', '5', '7', '3', '3', '7', '0', '7', '2', '1', '0', '3', '6', '1', '5', '6', '6', '3', '3', '2', '6', '8', '6', '4', '9', '6', '1', '9', '9', '1', '5', '6', '7', '3', '6', '8', '0', '0', '3', '3', '8', '2', '1', '8', '3', '2', '3', '5', '0', '3', '5', '3', '5', '4', '8', '0', '9', '6', '5', '8', '5', '3', '2', '1', '8', '8', '2', '9', '2', '7', '5', '6', '4', '1', '3', '1', '1', '3', '0', '6', '6', '0', '6', '9', '8', '2', '5', '2', '3', '5', '9', '6', '7', '2', '5', '6', '9', '1', '6', '6', '4', '1', '6', '7', '3'])
noncomputable def fragment0126175Acc00800 : List (String × SourceJson) := (fragment0126175Field007Key00, fragment0126175Field007Value00) :: fragment0126175Acc00700
noncomputable def fragment0126175Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '8', '5', '6', '5', '2', '9', '0', '4', '9', '3', '1', '2', '1', '4', '6', '6', '4', '8', '6', '7', '9', '3', '0', '6', '9', '7', '2', '5', '5', '2', '2', '9', '1', '8', '9', '2', '4', '1', '2', '3', '0', '7', '5', '9', '1', '1', '1', '3', '9', '8', '8', '4', '3', '6', '5', '0', '0', '4', '2', '2', '5', '8', '8', '7', '6', '7', '9', '2', '2', '2', '1', '9', '6', '5', '8', '3', '1', '8', '1', '7', '6', '9', '0', '6', '1', '7', '8', '9', '8', '5', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '5', '4', '2', '2', '0', '3', '8', '0', '6', '6', '4', '3', '7', '8', '4', '2', '6', '3', '7', '7', '6', '0', '6', '3', '4', '5', '0', '4', '2', '5', '7', '3', '3', '7', '0', '7', '2', '1', '0', '3', '6', '1', '5', '6', '6', '3', '3', '2', '6', '8', '6', '4', '9', '6', '1', '9', '9', '1', '5', '6', '7', '3', '6', '8', '0', '0', '3', '3', '8', '2', '1', '8', '3', '2', '3', '5', '0', '3', '5', '3', '5', '4', '8', '0', '9', '6', '5', '8', '5', '3', '2', '1', '8', '8', '2', '9', '2', '7', '5', '6', '4', '1', '3', '1', '1', '3', '0', '6', '6', '0', '6', '9', '8', '2', '5', '2', '3', '5', '9', '6', '7', '2', '5', '6', '9', '1', '6', '6', '4', '1', '6', '7', '3', '"', ',']

theorem object_fragment0126175_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0126175Field007Chars00 ++ tail)) fragment0126175Acc00700 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0126175Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126175_object_field_007"
  err.flush

noncomputable def fragment0126175Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0126175Field008Value00 : SourceJson := .str (String.ofList ['4', '3', '1', '3', '3', '5', '9', '8', '8', '0', '9', '9'])
noncomputable def fragment0126175Acc00900 : List (String × SourceJson) := (fragment0126175Field008Key00, fragment0126175Field008Value00) :: fragment0126175Acc00800
noncomputable def fragment0126175Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '3', '1', '3', '3', '5', '9', '8', '8', '0', '9', '9', '"', ',']

theorem object_fragment0126175_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0126175Field008Chars00 ++ tail)) fragment0126175Acc00800 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0126175Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126175_object_field_008"
  err.flush

noncomputable def fragment0126175Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0126175Field009Value00 : SourceJson := .str (String.ofList ['1', '6', '9', '4', '9', '4', '1', '2', '9', '6', '1', '8', '2'])
noncomputable def fragment0126175Acc01000 : List (String × SourceJson) := (fragment0126175Field009Key00, fragment0126175Field009Value00) :: fragment0126175Acc00900
noncomputable def fragment0126175Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '9', '4', '9', '4', '1', '2', '9', '6', '1', '8', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0126175_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0126175Field009Chars00 ++ tail)) fragment0126175Acc00900 =
      .ok (.obj (fragment0126175Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126175_object_field_009"
  err.flush

noncomputable def fragment0126175Chars : List Char := '{' :: (fragment0126175Field000Chars00 ++ fragment0126175Field001Chars00 ++ fragment0126175Field002Chars00 ++ fragment0126175Field003Chars00 ++ fragment0126175Field004Chars00 ++ fragment0126175Field005Chars00 ++ fragment0126175Field006Chars00 ++ fragment0126175Field007Chars00 ++ fragment0126175Field008Chars00 ++ fragment0126175Field009Chars00)
noncomputable def fragment0126175Value : SourceJson := .obj (fragment0126175Acc01000.reverse)

theorem value_fragment0126175 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 264) (fragment0126175Chars ++ tail) =
      .ok (fragment0126175Value, tail) := by
  have hinput : fragment0126175Chars ++ tail = '{' :: (fragment0126175Field000Chars00 ++ (fragment0126175Field001Chars00 ++ (fragment0126175Field002Chars00 ++ (fragment0126175Field003Chars00 ++ (fragment0126175Field004Chars00 ++ (fragment0126175Field005Chars00 ++ (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0126175Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 264) (fragment0126175Chars ++ tail) =
        SourceJson.value (fuel + 264) ('{' :: (fragment0126175Field000Chars00 ++ (fragment0126175Field001Chars00 ++ (fragment0126175Field002Chars00 ++ (fragment0126175Field003Chars00 ++ (fragment0126175Field004Chars00 ++ (fragment0126175Field005Chars00 ++ (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 264)) hinput
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0126175Field000Chars00 ++ (fragment0126175Field001Chars00 ++ (fragment0126175Field002Chars00 ++ (fragment0126175Field003Chars00 ++ (fragment0126175Field004Chars00 ++ (fragment0126175Field005Chars00 ++ (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail)))))))))))) fragment0126175Acc00000 := by rfl
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0126175Field001Chars00 ++ (fragment0126175Field002Chars00 ++ (fragment0126175Field003Chars00 ++ (fragment0126175Field004Chars00 ++ (fragment0126175Field005Chars00 ++ (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail))))))))))) fragment0126175Acc00100 := object_fragment0126175_field_000 fuel (fragment0126175Field001Chars00 ++ (fragment0126175Field002Chars00 ++ (fragment0126175Field003Chars00 ++ (fragment0126175Field004Chars00 ++ (fragment0126175Field005Chars00 ++ (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0126175Field002Chars00 ++ (fragment0126175Field003Chars00 ++ (fragment0126175Field004Chars00 ++ (fragment0126175Field005Chars00 ++ (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail)))))))))) fragment0126175Acc00200 := object_fragment0126175_field_001 fuel (fragment0126175Field002Chars00 ++ (fragment0126175Field003Chars00 ++ (fragment0126175Field004Chars00 ++ (fragment0126175Field005Chars00 ++ (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0126175Field003Chars00 ++ (fragment0126175Field004Chars00 ++ (fragment0126175Field005Chars00 ++ (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail))))))))) fragment0126175Acc00300 := object_fragment0126175_field_002 fuel (fragment0126175Field003Chars00 ++ (fragment0126175Field004Chars00 ++ (fragment0126175Field005Chars00 ++ (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0126175Field004Chars00 ++ (fragment0126175Field005Chars00 ++ (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail)))))))) fragment0126175Acc00400 := object_fragment0126175_field_003 fuel (fragment0126175Field004Chars00 ++ (fragment0126175Field005Chars00 ++ (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0126175Field005Chars00 ++ (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail))))))) fragment0126175Acc00500 := object_fragment0126175_field_004 fuel (fragment0126175Field005Chars00 ++ (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail)))))) fragment0126175Acc00600 := object_fragment0126175_field_005 fuel (fragment0126175Field006Chars00 ++ (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail))))) fragment0126175Acc00700 := object_fragment0126175_field_006 fuel (fragment0126175Field007Chars00 ++ (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail)))) fragment0126175Acc00800 := object_fragment0126175_field_007 fuel (fragment0126175Field008Chars00 ++ (fragment0126175Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0126175Field009Chars00 ++ (tail))) fragment0126175Acc00900 := object_fragment0126175_field_008 fuel (fragment0126175Field009Chars00 ++ (tail))
    _ = .ok (fragment0126175Value, tail) := object_fragment0126175_field_009 fuel (tail)

noncomputable def fragment0127827Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0127827Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0127827Field000Value00 : SourceJson := .number (String.ofList ['1', '4'])
noncomputable def fragment0127827Acc00100 : List (String × SourceJson) := (fragment0127827Field000Key00, fragment0127827Field000Value00) :: fragment0127827Acc00000
noncomputable def fragment0127827Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '4', ',']

theorem object_fragment0127827_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0127827Field000Chars00 ++ tail)) fragment0127827Acc00000 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0127827Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0127827_object_field_000"
  err.flush

noncomputable def fragment0127827Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0127827Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0127827Acc00200 : List (String × SourceJson) := (fragment0127827Field001Key00, fragment0127827Field001Value00) :: fragment0127827Acc00100
noncomputable def fragment0127827Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0127827_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0127827Field001Chars00 ++ tail)) fragment0127827Acc00100 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0127827Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0127827_object_field_001"
  err.flush

noncomputable def fragment0127827Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0127827Field002Value00 : SourceJson := .str (String.ofList ['2', '0', '4', '7', '1', '1', '5', '0', '5', '7', '5', '0', '8', '3', '5', '1', '6', '6', '9', '3', '8', '5', '3', '2', '7', '9', '8', '1', '4', '5', '6', '1', '7', '5', '8', '1', '/', '1', '3', '2', '5', '0', '0', '1', '7', '3', '9', '2', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0127827Acc00300 : List (String × SourceJson) := (fragment0127827Field002Key00, fragment0127827Field002Value00) :: fragment0127827Acc00200
noncomputable def fragment0127827Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '0', '4', '7', '1', '1', '5', '0', '5', '7', '5', '0', '8', '3', '5', '1', '6', '6', '9', '3', '8', '5', '3', '2', '7', '9', '8', '1', '4', '5', '6', '1', '7', '5', '8', '1', '/', '1', '3', '2', '5', '0', '0', '1', '7', '3', '9', '2', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0127827_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0127827Field002Chars00 ++ tail)) fragment0127827Acc00200 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0127827Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0127827_object_field_002"
  err.flush

noncomputable def fragment0127827Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0127827Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0127827Acc00400 : List (String × SourceJson) := (fragment0127827Field003Key00, fragment0127827Field003Value00) :: fragment0127827Acc00300
noncomputable def fragment0127827Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0127827_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0127827Field003Chars00 ++ tail)) fragment0127827Acc00300 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0127827Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0127827_object_field_003"
  err.flush

noncomputable def fragment0127827Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0127827Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0127827Acc00500 : List (String × SourceJson) := (fragment0127827Field004Key00, fragment0127827Field004Value00) :: fragment0127827Acc00400
noncomputable def fragment0127827Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0127827_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0127827Field004Chars00 ++ tail)) fragment0127827Acc00400 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0127827Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0127827_object_field_004"
  err.flush

noncomputable def fragment0127827Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0127827Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '3', '9', '1', '3', '9', '3', '7', '0', '1', '5', '4', '5', '7', '/', '1', '5', '0', '2', '6', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '9', '7', '2', '8', '3', '2', '4', '3', '2', '8', '5', '9', '/', '3', '0', '0', '5', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '8', '3', '4', '9', '6', '4', '4', '3', '2', '1', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '2', '7', '3', '9', '6', '4', '2', '1', '1', '9', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '6', '7', '7', '5', '3', '9', '7', '1', '7', '0', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '9', '2', '6', '1', '1', '8', '9', '5', '2', '3', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '0', '6', '7', '0', '0', '6', '0', '2', '1', '7', '7', '/', '3', '0', '0', '5', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '1', '9', '6', '9', '3', '7', '7', '7', '5', '1', '/', '6', '2', '6', '0', '8', '8', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '4', '4', '6', '7', '7', '1', '7', '2', '2', '3', '/', '5', '0', '0', '8', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '2', '8', '8', '9', '1', '3', '6', '0', '7', '3', '/', '3', '0', '0', '5', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0127827Acc00600 : List (String × SourceJson) := (fragment0127827Field005Key00, fragment0127827Field005Value00) :: fragment0127827Acc00500
noncomputable def fragment0127827Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '1', '3', '9', '3', '7', '0', '1', '5', '4', '5', '7', '/', '1', '5', '0', '2', '6', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '9', '7', '2', '8', '3', '2', '4', '3', '2', '8', '5', '9', '/', '3', '0', '0', '5', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '8', '3', '4', '9', '6', '4', '4', '3', '2', '1', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '2', '7', '3', '9', '6', '4', '2', '1', '1', '9', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '6', '7', '7', '5', '3', '9', '7', '1', '7', '0', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '9', '2', '6', '1', '1', '8', '9', '5', '2', '3', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '0', '6', '7', '0', '0', '6', '0', '2', '1', '7', '7', '/', '3', '0', '0', '5', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '1', '9', '6', '9', '3', '7', '7', '7', '5', '1', '/', '6', '2', '6', '0', '8', '8', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '4', '4', '6', '7', '7', '1', '7', '2', '2', '3', '/', '5', '0', '0', '8', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '2', '8', '8', '9', '1', '3', '6', '0', '7', '3', '/', '3', '0', '0', '5', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0127827_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0127827Field005Chars00 ++ tail)) fragment0127827Acc00500 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0127827Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0127827_object_field_005"
  err.flush

noncomputable def fragment0127827Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0127827Field006Value00 : SourceJson := .str (String.ofList ['1', '2', '5', '0', '1', '2', '8', '5', '9', '0', '6', '2', '0', '4', '7', '9', '9', '6', '4', '4', '5', '7', '9', '9', '6', '9', '6', '4', '2', '9', '7', '2', '7', '5', '8', '0', '5', '0', '5', '5', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '/', '2', '2', '9', '6', '1', '9', '0', '8', '6', '2', '7', '8', '7', '5', '1', '5', '9', '5', '6', '6', '2', '2', '2', '0', '0', '6', '2', '3', '5', '9', '3', '9', '5', '8', '8', '9', '2', '7', '3', '6', '2', '1', '4', '1', '9', '6', '3', '3', '7', '2', '2', '9', '3', '2', '8', '4', '6', '7', '2', '6', '6', '0', '0', '7', '9', '3', '7', '1'])
noncomputable def fragment0127827Acc00700 : List (String × SourceJson) := (fragment0127827Field006Key00, fragment0127827Field006Value00) :: fragment0127827Acc00600
noncomputable def fragment0127827Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '5', '0', '1', '2', '8', '5', '9', '0', '6', '2', '0', '4', '7', '9', '9', '6', '4', '4', '5', '7', '9', '9', '6', '9', '6', '4', '2', '9', '7', '2', '7', '5', '8', '0', '5', '0', '5', '5', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '/', '2', '2', '9', '6', '1', '9', '0', '8', '6', '2', '7', '8', '7', '5', '1', '5', '9', '5', '6', '6', '2', '2', '2', '0', '0', '6', '2', '3', '5', '9', '3', '9', '5', '8', '8', '9', '2', '7', '3', '6', '2', '1', '4', '1', '9', '6', '3', '3', '7', '2', '2', '9', '3', '2', '8', '4', '6', '7', '2', '6', '6', '0', '0', '7', '9', '3', '7', '1', '"', ',']

theorem object_fragment0127827_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0127827Field006Chars00 ++ tail)) fragment0127827Acc00600 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0127827Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0127827_object_field_006"
  err.flush

noncomputable def fragment0127827Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0127827Field007Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '7', '4', '8', '1', '7', '0', '0', '5', '6', '0', '5', '7', '4', '1', '5', '4', '1', '0', '1', '1', '0', '7', '5', '5', '9', '0', '1', '2', '1', '8', '7', '6', '8', '4', '5', '0', '7', '5', '7', '0', '4', '1', '1', '7', '9', '6', '9', '7', '0', '1', '7', '8', '5', '1', '5', '5', '6', '8', '8', '0', '5', '1', '0', '3', '3', '3', '1', '8', '3', '4', '1', '2', '8', '3', '3', '9', '2', '8', '0', '5', '5', '7', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '5', '8', '4', '5', '6', '6', '0', '3', '8', '8', '4', '5', '3', '6', '9', '9', '7', '3', '1', '4', '5', '2', '0', '9', '4', '8', '7', '6', '3', '5', '8', '3', '5', '5', '9', '7', '6', '1', '3', '3', '9', '8', '0', '9', '0', '2', '3', '3', '8', '6', '8', '7', '8', '0', '4', '0', '7', '0', '3', '2', '8', '8', '0', '6', '2', '0', '6', '0', '4', '0', '7', '2', '2', '6', '8', '9', '3', '7', '1', '7', '8', '4', '4', '9', '3', '9', '6', '8', '5', '2', '5', '5', '7', '7', '9', '5', '5', '2', '2', '1', '0', '6', '5', '4', '3', '6', '2', '2', '6', '1', '2', '0', '5', '4', '7', '7', '8', '5', '3', '5', '2', '7', '0', '7', '7', '1'])
noncomputable def fragment0127827Acc00800 : List (String × SourceJson) := (fragment0127827Field007Key00, fragment0127827Field007Value00) :: fragment0127827Acc00700
noncomputable def fragment0127827Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '2', '7', '4', '8', '1', '7', '0', '0', '5', '6', '0', '5', '7', '4', '1', '5', '4', '1', '0', '1', '1', '0', '7', '5', '5', '9', '0', '1', '2', '1', '8', '7', '6', '8', '4', '5', '0', '7', '5', '7', '0', '4', '1', '1', '7', '9', '6', '9', '7', '0', '1', '7', '8', '5', '1', '5', '5', '6', '8', '8', '0', '5', '1', '0', '3', '3', '3', '1', '8', '3', '4', '1', '2', '8', '3', '3', '9', '2', '8', '0', '5', '5', '7', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '5', '8', '4', '5', '6', '6', '0', '3', '8', '8', '4', '5', '3', '6', '9', '9', '7', '3', '1', '4', '5', '2', '0', '9', '4', '8', '7', '6', '3', '5', '8', '3', '5', '5', '9', '7', '6', '1', '3', '3', '9', '8', '0', '9', '0', '2', '3', '3', '8', '6', '8', '7', '8', '0', '4', '0', '7', '0', '3', '2', '8', '8', '0', '6', '2', '0', '6', '0', '4', '0', '7', '2', '2', '6', '8', '9', '3', '7', '1', '7', '8', '4', '4', '9', '3', '9', '6', '8', '5', '2', '5', '5', '7', '7', '9', '5', '5', '2', '2', '1', '0', '6', '5', '4', '3', '6', '2', '2', '6', '1', '2', '0', '5', '4', '7', '7', '8', '5', '3', '5', '2', '7', '0', '7', '7', '1', '"', ',']

theorem object_fragment0127827_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0127827Field007Chars00 ++ tail)) fragment0127827Acc00700 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0127827Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0127827_object_field_007"
  err.flush

noncomputable def fragment0127827Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0127827Field008Value00 : SourceJson := .str (String.ofList ['4', '3', '1', '3', '4', '6', '5', '0', '8', '4', '5', '6'])
noncomputable def fragment0127827Acc00900 : List (String × SourceJson) := (fragment0127827Field008Key00, fragment0127827Field008Value00) :: fragment0127827Acc00800
noncomputable def fragment0127827Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '3', '1', '3', '4', '6', '5', '0', '8', '4', '5', '6', '"', ',']

theorem object_fragment0127827_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0127827Field008Chars00 ++ tail)) fragment0127827Acc00800 =
      SourceJson.object (fuel + 240) (SourceJson.white tail) fragment0127827Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0127827_object_field_008"
  err.flush

noncomputable def fragment0127827Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0127827Field009Value00 : SourceJson := .str (String.ofList ['1', '6', '8', '6', '6', '0', '8', '4', '6', '1', '1', '4', '6'])
noncomputable def fragment0127827Acc01000 : List (String × SourceJson) := (fragment0127827Field009Key00, fragment0127827Field009Value00) :: fragment0127827Acc00900
noncomputable def fragment0127827Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '8', '6', '6', '0', '8', '4', '6', '1', '1', '4', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0127827_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 240) (SourceJson.white (fragment0127827Field009Chars00 ++ tail)) fragment0127827Acc00900 =
      .ok (.obj (fragment0127827Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0127827_object_field_009"
  err.flush

noncomputable def fragment0127827Chars : List Char := '{' :: (fragment0127827Field000Chars00 ++ fragment0127827Field001Chars00 ++ fragment0127827Field002Chars00 ++ fragment0127827Field003Chars00 ++ fragment0127827Field004Chars00 ++ fragment0127827Field005Chars00 ++ fragment0127827Field006Chars00 ++ fragment0127827Field007Chars00 ++ fragment0127827Field008Chars00 ++ fragment0127827Field009Chars00)
noncomputable def fragment0127827Value : SourceJson := .obj (fragment0127827Acc01000.reverse)

theorem value_fragment0127827 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 250) (fragment0127827Chars ++ tail) =
      .ok (fragment0127827Value, tail) := by
  have hinput : fragment0127827Chars ++ tail = '{' :: (fragment0127827Field000Chars00 ++ (fragment0127827Field001Chars00 ++ (fragment0127827Field002Chars00 ++ (fragment0127827Field003Chars00 ++ (fragment0127827Field004Chars00 ++ (fragment0127827Field005Chars00 ++ (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0127827Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 250) (fragment0127827Chars ++ tail) =
        SourceJson.value (fuel + 250) ('{' :: (fragment0127827Field000Chars00 ++ (fragment0127827Field001Chars00 ++ (fragment0127827Field002Chars00 ++ (fragment0127827Field003Chars00 ++ (fragment0127827Field004Chars00 ++ (fragment0127827Field005Chars00 ++ (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 250)) hinput
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0127827Field000Chars00 ++ (fragment0127827Field001Chars00 ++ (fragment0127827Field002Chars00 ++ (fragment0127827Field003Chars00 ++ (fragment0127827Field004Chars00 ++ (fragment0127827Field005Chars00 ++ (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail)))))))))))) fragment0127827Acc00000 := by rfl
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0127827Field001Chars00 ++ (fragment0127827Field002Chars00 ++ (fragment0127827Field003Chars00 ++ (fragment0127827Field004Chars00 ++ (fragment0127827Field005Chars00 ++ (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail))))))))))) fragment0127827Acc00100 := object_fragment0127827_field_000 fuel (fragment0127827Field001Chars00 ++ (fragment0127827Field002Chars00 ++ (fragment0127827Field003Chars00 ++ (fragment0127827Field004Chars00 ++ (fragment0127827Field005Chars00 ++ (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0127827Field002Chars00 ++ (fragment0127827Field003Chars00 ++ (fragment0127827Field004Chars00 ++ (fragment0127827Field005Chars00 ++ (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail)))))))))) fragment0127827Acc00200 := object_fragment0127827_field_001 fuel (fragment0127827Field002Chars00 ++ (fragment0127827Field003Chars00 ++ (fragment0127827Field004Chars00 ++ (fragment0127827Field005Chars00 ++ (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0127827Field003Chars00 ++ (fragment0127827Field004Chars00 ++ (fragment0127827Field005Chars00 ++ (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail))))))))) fragment0127827Acc00300 := object_fragment0127827_field_002 fuel (fragment0127827Field003Chars00 ++ (fragment0127827Field004Chars00 ++ (fragment0127827Field005Chars00 ++ (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0127827Field004Chars00 ++ (fragment0127827Field005Chars00 ++ (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail)))))))) fragment0127827Acc00400 := object_fragment0127827_field_003 fuel (fragment0127827Field004Chars00 ++ (fragment0127827Field005Chars00 ++ (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0127827Field005Chars00 ++ (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail))))))) fragment0127827Acc00500 := object_fragment0127827_field_004 fuel (fragment0127827Field005Chars00 ++ (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail)))))) fragment0127827Acc00600 := object_fragment0127827_field_005 fuel (fragment0127827Field006Chars00 ++ (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail))))) fragment0127827Acc00700 := object_fragment0127827_field_006 fuel (fragment0127827Field007Chars00 ++ (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail)))) fragment0127827Acc00800 := object_fragment0127827_field_007 fuel (fragment0127827Field008Chars00 ++ (fragment0127827Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 240) (SourceJson.white (fragment0127827Field009Chars00 ++ (tail))) fragment0127827Acc00900 := object_fragment0127827_field_008 fuel (fragment0127827Field009Chars00 ++ (tail))
    _ = .ok (fragment0127827Value, tail) := object_fragment0127827_field_009 fuel (tail)

noncomputable def fragment0129454Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0129454Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0129454Field000Value00 : SourceJson := .number (String.ofList ['1', '5'])
noncomputable def fragment0129454Acc00100 : List (String × SourceJson) := (fragment0129454Field000Key00, fragment0129454Field000Value00) :: fragment0129454Acc00000
noncomputable def fragment0129454Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '5', ',']

theorem object_fragment0129454_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0129454Field000Chars00 ++ tail)) fragment0129454Acc00000 =
      SourceJson.object (fuel + 399) (SourceJson.white tail) fragment0129454Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0129454_object_field_000"
  err.flush

noncomputable def fragment0129454Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0129454Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0129454Acc00200 : List (String × SourceJson) := (fragment0129454Field001Key00, fragment0129454Field001Value00) :: fragment0129454Acc00100
noncomputable def fragment0129454Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0129454_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 399) (SourceJson.white (fragment0129454Field001Chars00 ++ tail)) fragment0129454Acc00100 =
      SourceJson.object (fuel + 398) (SourceJson.white tail) fragment0129454Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0129454_object_field_001"
  err.flush

noncomputable def fragment0129454Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0129454Field002Value00 : SourceJson := .str (String.ofList ['2', '2', '3', '9', '1', '6', '8', '5', '9', '1', '1', '2', '1', '6', '2', '5', '9', '6', '9', '1', '4', '5', '3', '4', '0', '5', '9', '8', '5', '0', '9', '0', '1', '4', '6', '3', '5', '3', '7', '9', '1', '/', '5', '6', '5', '3', '3', '4', '0', '7', '5', '4', '0', '0', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0129454Acc00300 : List (String × SourceJson) := (fragment0129454Field002Key00, fragment0129454Field002Value00) :: fragment0129454Acc00200
noncomputable def fragment0129454Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '2', '3', '9', '1', '6', '8', '5', '9', '1', '1', '2', '1', '6', '2', '5', '9', '6', '9', '1', '4', '5', '3', '4', '0', '5', '9', '8', '5', '0', '9', '0', '1', '4', '6', '3', '5', '3', '7', '9', '1', '/', '5', '6', '5', '3', '3', '4', '0', '7', '5', '4', '0', '0', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0129454_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 398) (SourceJson.white (fragment0129454Field002Chars00 ++ tail)) fragment0129454Acc00200 =
      SourceJson.object (fuel + 397) (SourceJson.white tail) fragment0129454Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0129454_object_field_002"
  err.flush

noncomputable def fragment0129454Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0129454Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '2', '4', '1', '6', '9', '/', '1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0129454Acc00400 : List (String × SourceJson) := (fragment0129454Field003Key00, fragment0129454Field003Value00) :: fragment0129454Acc00300
noncomputable def fragment0129454Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '8', '2', '4', '1', '6', '9', '/', '1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0129454_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 397) (SourceJson.white (fragment0129454Field003Chars00 ++ tail)) fragment0129454Acc00300 =
      SourceJson.object (fuel + 396) (SourceJson.white tail) fragment0129454Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0129454_object_field_003"
  err.flush

noncomputable def fragment0129454Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0129454Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0129454Acc00500 : List (String × SourceJson) := (fragment0129454Field004Key00, fragment0129454Field004Value00) :: fragment0129454Acc00400
noncomputable def fragment0129454Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0129454_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 396) (SourceJson.white (fragment0129454Field004Chars00 ++ tail)) fragment0129454Acc00400 =
      SourceJson.object (fuel + 395) (SourceJson.white tail) fragment0129454Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0129454_object_field_004"
  err.flush

noncomputable def fragment0129454Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0129454Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '7', '6', '6', '8', '7', '3', '7', '6', '0', '4', '1', '5', '6', '5', '4', '0', '0', '0', '8', '7', '1', '/', '5', '2', '0', '4', '6', '5', '1', '8', '5', '7', '1', '5', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '0', '8', '9', '3', '7', '8', '7', '0', '7', '6', '8', '1', '0', '8', '0', '4', '7', '9', '/', '8', '1', '3', '2', '2', '6', '8', '5', '2', '6', '7', '9', '8', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '7', '6', '7', '5', '6', '6', '1', '8', '7', '6', '3', '9', '7', '0', '1', '1', '5', '9', '7', '/', '1', '7', '3', '4', '8', '8', '3', '9', '5', '2', '3', '8', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '4', '5', '8', '4', '6', '4', '1', '3', '2', '3', '8', '9', '8', '0', '8', '6', '6', '7', '7', '/', '2', '1', '6', '8', '6', '0', '4', '9', '4', '0', '4', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '7', '5', '4', '1', '3', '2', '3', '9', '1', '6', '9', '5', '5', '7', '7', '2', '5', '3', '/', '3', '6', '1', '4', '3', '4', '1', '5', '6', '7', '4', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '0', '5', '4', '5', '9', '7', '9', '7', '0', '9', '1', '5', '4', '5', '9', '5', '9', '/', '8', '6', '7', '4', '4', '1', '9', '7', '6', '1', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '7', '6', '1', '3', '1', '2', '9', '4', '7', '6', '5', '4', '0', '0', '7', '2', '9', '3', '3', '/', '8', '6', '7', '4', '4', '1', '9', '7', '6', '1', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '7', '9', '1', '6', '0', '1', '3', '6', '6', '1', '7', '7', '6', '9', '6', '8', '9', '0', '5', '1', '/', '2', '6', '0', '2', '3', '2', '5', '9', '2', '8', '5', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '9', '4', '7', '5', '8', '2', '0', '2', '4', '3', '1', '3', '0', '2', '1', '4', '5', '3', '1', '/', '2', '6', '0', '2', '3', '2', '5', '9', '2', '8', '5', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '3', '1', '4', '3', '4', '9', '5', '4', '7', '2', '5', '8', '8', '3', '2', '7', '1', '/', '2', '7', '1', '0', '7', '5', '6', '1', '7', '5', '5', '9', '9', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0129454Acc00600 : List (String × SourceJson) := (fragment0129454Field005Key00, fragment0129454Field005Value00) :: fragment0129454Acc00500
noncomputable def fragment0129454Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '6', '6', '8', '7', '3', '7', '6', '0', '4', '1', '5', '6', '5', '4', '0', '0', '0', '8', '7', '1', '/', '5', '2', '0', '4', '6', '5', '1', '8', '5', '7', '1', '5', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '0', '8', '9', '3', '7', '8', '7', '0', '7', '6', '8', '1', '0', '8', '0', '4', '7', '9', '/', '8', '1', '3', '2', '2', '6', '8', '5', '2', '6', '7', '9', '8', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '6', '7', '5', '6', '6', '1', '8', '7', '6', '3', '9', '7', '0', '1', '1', '5', '9', '7', '/', '1', '7', '3', '4', '8', '8', '3', '9', '5', '2', '3', '8', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '4', '5', '8', '4', '6', '4', '1', '3', '2', '3', '8', '9', '8', '0', '8', '6', '6', '7', '7', '/', '2', '1', '6', '8', '6', '0', '4', '9', '4', '0', '4', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '7', '5', '4', '1', '3', '2', '3', '9', '1', '6', '9', '5', '5', '7', '7', '2', '5', '3', '/', '3', '6', '1', '4', '3', '4', '1', '5', '6', '7', '4', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '0', '5', '4', '5', '9', '7', '9', '7', '0', '9', '1', '5', '4', '5', '9', '5', '9', '/', '8', '6', '7', '4', '4', '1', '9', '7', '6', '1', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '7', '6', '1', '3', '1', '2', '9', '4', '7', '6', '5', '4', '0', '0', '7', '2', '9', '3', '3', '/', '8', '6', '7', '4', '4', '1', '9', '7', '6', '1', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '9', '1', '6', '0', '1', '3', '6', '6', '1', '7', '7', '6', '9', '6', '8', '9', '0', '5', '1', '/', '2', '6', '0', '2', '3', '2', '5', '9', '2', '8', '5', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '9', '4', '7', '5', '8', '2', '0', '2', '4', '3', '1', '3', '0', '2', '1', '4', '5', '3', '1', '/', '2', '6', '0', '2', '3', '2', '5', '9', '2', '8', '5', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '5', '3', '1', '4', '3', '4', '9', '5', '4', '7', '2', '5', '8', '8', '3', '2', '7', '1', '/', '2', '7', '1', '0', '7', '5', '6', '1', '7', '5', '5', '9', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0129454_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 395) (SourceJson.white (fragment0129454Field005Chars00 ++ tail)) fragment0129454Acc00500 =
      SourceJson.object (fuel + 394) (SourceJson.white tail) fragment0129454Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0129454_object_field_005"
  err.flush

noncomputable def fragment0129454Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0129454Field006Value00 : SourceJson := .str (String.ofList ['2', '2', '0', '3', '3', '7', '6', '2', '9', '5', '4', '3', '5', '6', '7', '0', '8', '2', '2', '2', '5', '6', '1', '7', '7', '4', '7', '2', '8', '0', '2', '0', '6', '5', '6', '7', '6', '0', '7', '4', '2', '5', '0', '6', '7', '8', '9', '0', '0', '0', '0', '0', '0', '0', '/', '7', '6', '5', '3', '8', '9', '5', '6', '0', '0', '6', '0', '5', '2', '1', '2', '0', '1', '2', '6', '5', '8', '2', '6', '0', '7', '7', '6', '6', '9', '7', '8', '6', '7', '6', '2', '6', '5', '3', '1', '1', '6', '5', '9', '0', '4', '7', '0', '3', '7', '6', '6', '5', '9', '0', '3', '0', '1', '3', '7', '3', '4', '5', '4', '8', '0', '1'])
noncomputable def fragment0129454Acc00700 : List (String × SourceJson) := (fragment0129454Field006Key00, fragment0129454Field006Value00) :: fragment0129454Acc00600
noncomputable def fragment0129454Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '2', '0', '3', '3', '7', '6', '2', '9', '5', '4', '3', '5', '6', '7', '0', '8', '2', '2', '2', '5', '6', '1', '7', '7', '4', '7', '2', '8', '0', '2', '0', '6', '5', '6', '7', '6', '0', '7', '4', '2', '5', '0', '6', '7', '8', '9', '0', '0', '0', '0', '0', '0', '0', '/', '7', '6', '5', '3', '8', '9', '5', '6', '0', '0', '6', '0', '5', '2', '1', '2', '0', '1', '2', '6', '5', '8', '2', '6', '0', '7', '7', '6', '6', '9', '7', '8', '6', '7', '6', '2', '6', '5', '3', '1', '1', '6', '5', '9', '0', '4', '7', '0', '3', '7', '6', '6', '5', '9', '0', '3', '0', '1', '3', '7', '3', '4', '5', '4', '8', '0', '1', '"', ',']

theorem object_fragment0129454_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 394) (SourceJson.white (fragment0129454Field006Chars00 ++ tail)) fragment0129454Acc00600 =
      SourceJson.object (fuel + 393) (SourceJson.white tail) fragment0129454Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0129454_object_field_006"
  err.flush

noncomputable def fragment0129454Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0129454Field007Value00 : SourceJson := .str (String.ofList ['2', '1', '0', '9', '5', '9', '4', '6', '1', '3', '8', '0', '6', '6', '1', '1', '2', '3', '5', '0', '8', '2', '4', '2', '2', '6', '0', '0', '9', '2', '0', '4', '7', '6', '7', '6', '8', '5', '9', '8', '2', '3', '2', '8', '3', '4', '8', '3', '0', '4', '7', '3', '8', '6', '2', '9', '3', '9', '2', '0', '1', '2', '1', '3', '0', '9', '0', '9', '3', '5', '7', '0', '7', '4', '6', '7', '8', '7', '9', '8', '3', '9', '9', '7', '7', '5', '0', '5', '9', '7', '8', '8', '5', '6', '7', '1', '3', '4', '5', '2', '4', '1', '2', '2', '0', '3', '0', '0', '2', '1', '3', '9', '8', '2', '9', '3', '3', '5', '6', '1', '6', '1', '4', '2', '7', '3', '4', '4', '0', '1', '1', '9', '4', '8', '6', '6', '3', '4', '8', '8', '3', '6', '4', '9', '6', '2', '3', '8', '6', '6', '1', '3', '8', '3', '4', '4', '3', '8', '6', '4', '4', '0', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '5', '7', '4', '0', '4', '9', '2', '8', '5', '4', '5', '6', '5', '5', '8', '0', '1', '0', '9', '5', '7', '9', '0', '2', '6', '5', '0', '5', '5', '9', '8', '0', '4', '4', '4', '8', '0', '2', '7', '4', '2', '2', '8', '4', '7', '9', '1', '9', '4', '8', '7', '9', '8', '3', '9', '1', '3', '9', '8', '3', '9', '7', '7', '5', '5', '4', '9', '3', '7', '0', '6', '8', '9', '0', '4', '6', '0', '0', '2', '8', '1', '9', '1', '9', '1', '9', '9', '8', '5', '0', '1', '6', '7', '2', '3', '0', '7', '9', '9', '1', '0', '7', '5', '0', '1', '6', '1', '2', '3', '6', '3', '2', '1', '2', '1', '6', '9', '9', '1', '3', '7', '5', '3', '7', '5', '2', '1', '0', '7', '4', '2', '6', '5', '8', '1', '4', '1', '7', '6', '3', '3', '3', '3', '8', '5', '9', '6', '1', '5', '0', '4', '9', '5', '0', '5', '8', '5', '9', '6', '0', '0', '9', '5', '2', '9', '1', '3', '0', '3', '0', '2', '4', '1', '4', '1', '7', '8', '7', '3', '8', '7', '1', '8', '5', '2', '1', '2', '6', '9', '5', '2', '0', '9', '2', '9', '0', '0', '1', '7'])
noncomputable def fragment0129454Acc00800 : List (String × SourceJson) := (fragment0129454Field007Key00, fragment0129454Field007Value00) :: fragment0129454Acc00700
noncomputable def fragment0129454Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '0', '9', '5', '9', '4', '6', '1', '3', '8', '0', '6', '6', '1', '1', '2', '3', '5', '0', '8', '2', '4', '2', '2', '6', '0', '0', '9', '2', '0', '4', '7', '6', '7', '6', '8', '5', '9', '8', '2', '3', '2', '8', '3', '4', '8', '3', '0', '4', '7', '3', '8', '6', '2', '9', '3', '9', '2', '0', '1', '2', '1', '3', '0', '9', '0', '9', '3', '5', '7', '0', '7', '4', '6', '7', '8', '7', '9', '8', '3', '9', '9', '7', '7', '5', '0', '5', '9', '7', '8', '8', '5', '6', '7', '1', '3', '4', '5', '2', '4', '1', '2', '2', '0', '3', '0', '0', '2', '1', '3', '9', '8', '2', '9', '3', '3', '5', '6', '1', '6', '1', '4', '2', '7', '3', '4', '4', '0', '1', '1', '9', '4', '8', '6', '6', '3', '4', '8', '8', '3', '6', '4', '9', '6', '2', '3', '8', '6', '6', '1', '3', '8', '3', '4', '4', '3', '8', '6', '4', '4', '0', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '5', '7', '4', '0', '4', '9', '2', '8', '5', '4', '5', '6', '5', '5', '8', '0', '1', '0', '9', '5', '7', '9', '0', '2', '6', '5', '0', '5', '5', '9', '8', '0', '4', '4', '4', '8', '0', '2', '7', '4', '2', '2', '8', '4', '7', '9', '1', '9', '4', '8', '7', '9', '8', '3', '9', '1', '3', '9', '8', '3', '9', '7', '7', '5', '5', '4', '9', '3', '7', '0', '6', '8', '9', '0', '4', '6', '0', '0', '2', '8', '1', '9', '1', '9', '1', '9', '9', '8', '5', '0', '1', '6', '7', '2', '3', '0', '7', '9', '9', '1', '0', '7', '5', '0', '1', '6', '1', '2', '3', '6', '3', '2', '1', '2', '1', '6', '9', '9', '1', '3', '7', '5', '3', '7', '5', '2', '1', '0', '7', '4', '2', '6', '5', '8', '1', '4', '1', '7', '6', '3', '3', '3', '3', '8', '5', '9', '6', '1', '5', '0', '4', '9', '5', '0', '5', '8', '5', '9', '6', '0', '0', '9', '5', '2', '9', '1', '3', '0', '3', '0', '2', '4', '1', '4', '1', '7', '8', '7', '3', '8', '7', '1', '8', '5', '2', '1', '2', '6', '9', '5', '2', '0', '9', '2', '9', '0', '0', '1', '7', '"', ',']

theorem object_fragment0129454_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 393) (SourceJson.white (fragment0129454Field007Chars00 ++ tail)) fragment0129454Acc00700 =
      SourceJson.object (fuel + 392) (SourceJson.white tail) fragment0129454Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0129454_object_field_007"
  err.flush

noncomputable def fragment0129454Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0129454Field008Value00 : SourceJson := .str (String.ofList ['2', '2', '8', '0', '7', '9', '2', '2', '1', '7', '7', '7', '0', '1', '4', '3'])
noncomputable def fragment0129454Acc00900 : List (String × SourceJson) := (fragment0129454Field008Key00, fragment0129454Field008Value00) :: fragment0129454Acc00800
noncomputable def fragment0129454Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '8', '0', '7', '9', '2', '2', '1', '7', '7', '7', '0', '1', '4', '3', '"', ',']

theorem object_fragment0129454_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 392) (SourceJson.white (fragment0129454Field008Chars00 ++ tail)) fragment0129454Acc00800 =
      SourceJson.object (fuel + 391) (SourceJson.white tail) fragment0129454Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0129454_object_field_008"
  err.flush

noncomputable def fragment0129454Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0129454Field009Value00 : SourceJson := .str (String.ofList ['8', '9', '9', '8', '5', '3', '8', '8', '9', '3', '3', '3', '4', '1', '8', '7'])
noncomputable def fragment0129454Acc01000 : List (String × SourceJson) := (fragment0129454Field009Key00, fragment0129454Field009Value00) :: fragment0129454Acc00900
noncomputable def fragment0129454Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '9', '9', '8', '5', '3', '8', '8', '9', '3', '3', '3', '4', '1', '8', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0129454_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 391) (SourceJson.white (fragment0129454Field009Chars00 ++ tail)) fragment0129454Acc00900 =
      .ok (.obj (fragment0129454Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0129454_object_field_009"
  err.flush

noncomputable def fragment0129454Chars : List Char := '{' :: (fragment0129454Field000Chars00 ++ fragment0129454Field001Chars00 ++ fragment0129454Field002Chars00 ++ fragment0129454Field003Chars00 ++ fragment0129454Field004Chars00 ++ fragment0129454Field005Chars00 ++ fragment0129454Field006Chars00 ++ fragment0129454Field007Chars00 ++ fragment0129454Field008Chars00 ++ fragment0129454Field009Chars00)
noncomputable def fragment0129454Value : SourceJson := .obj (fragment0129454Acc01000.reverse)

theorem value_fragment0129454 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 401) (fragment0129454Chars ++ tail) =
      .ok (fragment0129454Value, tail) := by
  have hinput : fragment0129454Chars ++ tail = '{' :: (fragment0129454Field000Chars00 ++ (fragment0129454Field001Chars00 ++ (fragment0129454Field002Chars00 ++ (fragment0129454Field003Chars00 ++ (fragment0129454Field004Chars00 ++ (fragment0129454Field005Chars00 ++ (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0129454Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 401) (fragment0129454Chars ++ tail) =
        SourceJson.value (fuel + 401) ('{' :: (fragment0129454Field000Chars00 ++ (fragment0129454Field001Chars00 ++ (fragment0129454Field002Chars00 ++ (fragment0129454Field003Chars00 ++ (fragment0129454Field004Chars00 ++ (fragment0129454Field005Chars00 ++ (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 401)) hinput
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0129454Field000Chars00 ++ (fragment0129454Field001Chars00 ++ (fragment0129454Field002Chars00 ++ (fragment0129454Field003Chars00 ++ (fragment0129454Field004Chars00 ++ (fragment0129454Field005Chars00 ++ (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail)))))))))))) fragment0129454Acc00000 := by rfl
    _ = SourceJson.object (fuel + 399) (SourceJson.white (fragment0129454Field001Chars00 ++ (fragment0129454Field002Chars00 ++ (fragment0129454Field003Chars00 ++ (fragment0129454Field004Chars00 ++ (fragment0129454Field005Chars00 ++ (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail))))))))))) fragment0129454Acc00100 := object_fragment0129454_field_000 fuel (fragment0129454Field001Chars00 ++ (fragment0129454Field002Chars00 ++ (fragment0129454Field003Chars00 ++ (fragment0129454Field004Chars00 ++ (fragment0129454Field005Chars00 ++ (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 398) (SourceJson.white (fragment0129454Field002Chars00 ++ (fragment0129454Field003Chars00 ++ (fragment0129454Field004Chars00 ++ (fragment0129454Field005Chars00 ++ (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail)))))))))) fragment0129454Acc00200 := object_fragment0129454_field_001 fuel (fragment0129454Field002Chars00 ++ (fragment0129454Field003Chars00 ++ (fragment0129454Field004Chars00 ++ (fragment0129454Field005Chars00 ++ (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 397) (SourceJson.white (fragment0129454Field003Chars00 ++ (fragment0129454Field004Chars00 ++ (fragment0129454Field005Chars00 ++ (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail))))))))) fragment0129454Acc00300 := object_fragment0129454_field_002 fuel (fragment0129454Field003Chars00 ++ (fragment0129454Field004Chars00 ++ (fragment0129454Field005Chars00 ++ (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 396) (SourceJson.white (fragment0129454Field004Chars00 ++ (fragment0129454Field005Chars00 ++ (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail)))))))) fragment0129454Acc00400 := object_fragment0129454_field_003 fuel (fragment0129454Field004Chars00 ++ (fragment0129454Field005Chars00 ++ (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 395) (SourceJson.white (fragment0129454Field005Chars00 ++ (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail))))))) fragment0129454Acc00500 := object_fragment0129454_field_004 fuel (fragment0129454Field005Chars00 ++ (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 394) (SourceJson.white (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail)))))) fragment0129454Acc00600 := object_fragment0129454_field_005 fuel (fragment0129454Field006Chars00 ++ (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 393) (SourceJson.white (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail))))) fragment0129454Acc00700 := object_fragment0129454_field_006 fuel (fragment0129454Field007Chars00 ++ (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 392) (SourceJson.white (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail)))) fragment0129454Acc00800 := object_fragment0129454_field_007 fuel (fragment0129454Field008Chars00 ++ (fragment0129454Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 391) (SourceJson.white (fragment0129454Field009Chars00 ++ (tail))) fragment0129454Acc00900 := object_fragment0129454_field_008 fuel (fragment0129454Field009Chars00 ++ (tail))
    _ = .ok (fragment0129454Value, tail) := object_fragment0129454_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0008_before_reader"
  err.flush

noncomputable def chunk0008LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0008SuffixChars00 : List Char := [',']
noncomputable def chunk0008Chars00 : List Char := chunk0008LeadChars00 ++ fragment0117888Chars ++ chunk0008SuffixChars00
noncomputable def chunk0008Push00 (acc : List SourceJson) : List SourceJson := fragment0117888Value :: acc

noncomputable def chunk0008AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0008_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 465)
      (SourceJson.white (chunk0008LeadChars00 ++ (fragment0117888Chars ++ rest))) acc =
      (SourceJson.value (fuel + 464) (fragment0117888Chars ++ rest)).bind
        (chunk0008AfterValue00 (fuel + 464) acc) := by rfl

theorem array_chunk0008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 465) (SourceJson.white (chunk0008Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 464) (SourceJson.white tail) (chunk0008Push00 acc) := by
  have hinput : chunk0008Chars00 ++ tail = chunk0008LeadChars00 ++ (fragment0117888Chars ++ (chunk0008SuffixChars00 ++ tail)) := by
    simp only [chunk0008Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 465) (SourceJson.white (chunk0008Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 465)
          (SourceJson.white (chunk0008LeadChars00 ++ (fragment0117888Chars ++ (chunk0008SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 465) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 464) (fragment0117888Chars ++ (chunk0008SuffixChars00 ++ tail))).bind
        (chunk0008AfterValue00 (fuel + 464) acc) := array_chunk0008_head fuel (chunk0008SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0117888Value, chunk0008SuffixChars00 ++ tail)).bind
        (chunk0008AfterValue00 (fuel + 464) acc) :=
      congrArg (fun result => result.bind (chunk0008AfterValue00 (fuel + 464) acc))
        (value_fragment0117888 (fuel + 245) (chunk0008SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 464) (SourceJson.white tail) (chunk0008Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0008_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0009_before_reader"
  err.flush

noncomputable def chunk0009LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0009SuffixChars00 : List Char := [',']
noncomputable def chunk0009Chars00 : List Char := chunk0009LeadChars00 ++ fragment0119450Chars ++ chunk0009SuffixChars00
noncomputable def chunk0009Push00 (acc : List SourceJson) : List SourceJson := fragment0119450Value :: acc

noncomputable def chunk0009AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0009_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 464)
      (SourceJson.white (chunk0009LeadChars00 ++ (fragment0119450Chars ++ rest))) acc =
      (SourceJson.value (fuel + 463) (fragment0119450Chars ++ rest)).bind
        (chunk0009AfterValue00 (fuel + 463) acc) := by rfl

theorem array_chunk0009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 464) (SourceJson.white (chunk0009Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 463) (SourceJson.white tail) (chunk0009Push00 acc) := by
  have hinput : chunk0009Chars00 ++ tail = chunk0009LeadChars00 ++ (fragment0119450Chars ++ (chunk0009SuffixChars00 ++ tail)) := by
    simp only [chunk0009Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 464) (SourceJson.white (chunk0009Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 464)
          (SourceJson.white (chunk0009LeadChars00 ++ (fragment0119450Chars ++ (chunk0009SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 464) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 463) (fragment0119450Chars ++ (chunk0009SuffixChars00 ++ tail))).bind
        (chunk0009AfterValue00 (fuel + 463) acc) := array_chunk0009_head fuel (chunk0009SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0119450Value, chunk0009SuffixChars00 ++ tail)).bind
        (chunk0009AfterValue00 (fuel + 463) acc) :=
      congrArg (fun result => result.bind (chunk0009AfterValue00 (fuel + 463) acc))
        (value_fragment0119450 (fuel + 86) (chunk0009SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 463) (SourceJson.white tail) (chunk0009Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0009_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0010_before_reader"
  err.flush

noncomputable def chunk0010LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0010SuffixChars00 : List Char := [',']
noncomputable def chunk0010Chars00 : List Char := chunk0010LeadChars00 ++ fragment0121338Chars ++ chunk0010SuffixChars00
noncomputable def chunk0010Push00 (acc : List SourceJson) : List SourceJson := fragment0121338Value :: acc

noncomputable def chunk0010AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0010_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 463)
      (SourceJson.white (chunk0010LeadChars00 ++ (fragment0121338Chars ++ rest))) acc =
      (SourceJson.value (fuel + 462) (fragment0121338Chars ++ rest)).bind
        (chunk0010AfterValue00 (fuel + 462) acc) := by rfl

theorem array_chunk0010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 463) (SourceJson.white (chunk0010Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 462) (SourceJson.white tail) (chunk0010Push00 acc) := by
  have hinput : chunk0010Chars00 ++ tail = chunk0010LeadChars00 ++ (fragment0121338Chars ++ (chunk0010SuffixChars00 ++ tail)) := by
    simp only [chunk0010Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 463) (SourceJson.white (chunk0010Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 463)
          (SourceJson.white (chunk0010LeadChars00 ++ (fragment0121338Chars ++ (chunk0010SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 463) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 462) (fragment0121338Chars ++ (chunk0010SuffixChars00 ++ tail))).bind
        (chunk0010AfterValue00 (fuel + 462) acc) := array_chunk0010_head fuel (chunk0010SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0121338Value, chunk0010SuffixChars00 ++ tail)).bind
        (chunk0010AfterValue00 (fuel + 462) acc) :=
      congrArg (fun result => result.bind (chunk0010AfterValue00 (fuel + 462) acc))
        (value_fragment0121338 (fuel + 215) (chunk0010SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 462) (SourceJson.white tail) (chunk0010Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0010_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0011_before_reader"
  err.flush

noncomputable def chunk0011LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0011SuffixChars00 : List Char := [',']
noncomputable def chunk0011Chars00 : List Char := chunk0011LeadChars00 ++ fragment0122954Chars ++ chunk0011SuffixChars00
noncomputable def chunk0011Push00 (acc : List SourceJson) : List SourceJson := fragment0122954Value :: acc

noncomputable def chunk0011AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0011_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 462)
      (SourceJson.white (chunk0011LeadChars00 ++ (fragment0122954Chars ++ rest))) acc =
      (SourceJson.value (fuel + 461) (fragment0122954Chars ++ rest)).bind
        (chunk0011AfterValue00 (fuel + 461) acc) := by rfl

theorem array_chunk0011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 462) (SourceJson.white (chunk0011Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 461) (SourceJson.white tail) (chunk0011Push00 acc) := by
  have hinput : chunk0011Chars00 ++ tail = chunk0011LeadChars00 ++ (fragment0122954Chars ++ (chunk0011SuffixChars00 ++ tail)) := by
    simp only [chunk0011Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 462) (SourceJson.white (chunk0011Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 462)
          (SourceJson.white (chunk0011LeadChars00 ++ (fragment0122954Chars ++ (chunk0011SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 462) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 461) (fragment0122954Chars ++ (chunk0011SuffixChars00 ++ tail))).bind
        (chunk0011AfterValue00 (fuel + 461) acc) := array_chunk0011_head fuel (chunk0011SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0122954Value, chunk0011SuffixChars00 ++ tail)).bind
        (chunk0011AfterValue00 (fuel + 461) acc) :=
      congrArg (fun result => result.bind (chunk0011AfterValue00 (fuel + 461) acc))
        (value_fragment0122954 (fuel + 223) (chunk0011SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 461) (SourceJson.white tail) (chunk0011Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0011_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0012_before_reader"
  err.flush

noncomputable def chunk0012LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0012SuffixChars00 : List Char := [',']
noncomputable def chunk0012Chars00 : List Char := chunk0012LeadChars00 ++ fragment0124549Chars ++ chunk0012SuffixChars00
noncomputable def chunk0012Push00 (acc : List SourceJson) : List SourceJson := fragment0124549Value :: acc

noncomputable def chunk0012AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0012_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 461)
      (SourceJson.white (chunk0012LeadChars00 ++ (fragment0124549Chars ++ rest))) acc =
      (SourceJson.value (fuel + 460) (fragment0124549Chars ++ rest)).bind
        (chunk0012AfterValue00 (fuel + 460) acc) := by rfl

theorem array_chunk0012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 461) (SourceJson.white (chunk0012Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 460) (SourceJson.white tail) (chunk0012Push00 acc) := by
  have hinput : chunk0012Chars00 ++ tail = chunk0012LeadChars00 ++ (fragment0124549Chars ++ (chunk0012SuffixChars00 ++ tail)) := by
    simp only [chunk0012Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 461) (SourceJson.white (chunk0012Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 461)
          (SourceJson.white (chunk0012LeadChars00 ++ (fragment0124549Chars ++ (chunk0012SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 461) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 460) (fragment0124549Chars ++ (chunk0012SuffixChars00 ++ tail))).bind
        (chunk0012AfterValue00 (fuel + 460) acc) := array_chunk0012_head fuel (chunk0012SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0124549Value, chunk0012SuffixChars00 ++ tail)).bind
        (chunk0012AfterValue00 (fuel + 460) acc) :=
      congrArg (fun result => result.bind (chunk0012AfterValue00 (fuel + 460) acc))
        (value_fragment0124549 (fuel + 215) (chunk0012SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 460) (SourceJson.white tail) (chunk0012Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0012_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0013_before_reader"
  err.flush

noncomputable def chunk0013LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0013SuffixChars00 : List Char := [',']
noncomputable def chunk0013Chars00 : List Char := chunk0013LeadChars00 ++ fragment0126175Chars ++ chunk0013SuffixChars00
noncomputable def chunk0013Push00 (acc : List SourceJson) : List SourceJson := fragment0126175Value :: acc

noncomputable def chunk0013AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0013_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 460)
      (SourceJson.white (chunk0013LeadChars00 ++ (fragment0126175Chars ++ rest))) acc =
      (SourceJson.value (fuel + 459) (fragment0126175Chars ++ rest)).bind
        (chunk0013AfterValue00 (fuel + 459) acc) := by rfl

theorem array_chunk0013 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 460) (SourceJson.white (chunk0013Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 459) (SourceJson.white tail) (chunk0013Push00 acc) := by
  have hinput : chunk0013Chars00 ++ tail = chunk0013LeadChars00 ++ (fragment0126175Chars ++ (chunk0013SuffixChars00 ++ tail)) := by
    simp only [chunk0013Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 460) (SourceJson.white (chunk0013Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 460)
          (SourceJson.white (chunk0013LeadChars00 ++ (fragment0126175Chars ++ (chunk0013SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 460) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 459) (fragment0126175Chars ++ (chunk0013SuffixChars00 ++ tail))).bind
        (chunk0013AfterValue00 (fuel + 459) acc) := array_chunk0013_head fuel (chunk0013SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0126175Value, chunk0013SuffixChars00 ++ tail)).bind
        (chunk0013AfterValue00 (fuel + 459) acc) :=
      congrArg (fun result => result.bind (chunk0013AfterValue00 (fuel + 459) acc))
        (value_fragment0126175 (fuel + 195) (chunk0013SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 459) (SourceJson.white tail) (chunk0013Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0013_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_before_reader"
  err.flush

noncomputable def chunk0014LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0014SuffixChars00 : List Char := [',']
noncomputable def chunk0014Chars00 : List Char := chunk0014LeadChars00 ++ fragment0127827Chars ++ chunk0014SuffixChars00
noncomputable def chunk0014Push00 (acc : List SourceJson) : List SourceJson := fragment0127827Value :: acc

noncomputable def chunk0014AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0014_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 459)
      (SourceJson.white (chunk0014LeadChars00 ++ (fragment0127827Chars ++ rest))) acc =
      (SourceJson.value (fuel + 458) (fragment0127827Chars ++ rest)).bind
        (chunk0014AfterValue00 (fuel + 458) acc) := by rfl

theorem array_chunk0014 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 459) (SourceJson.white (chunk0014Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 458) (SourceJson.white tail) (chunk0014Push00 acc) := by
  have hinput : chunk0014Chars00 ++ tail = chunk0014LeadChars00 ++ (fragment0127827Chars ++ (chunk0014SuffixChars00 ++ tail)) := by
    simp only [chunk0014Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 459) (SourceJson.white (chunk0014Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 459)
          (SourceJson.white (chunk0014LeadChars00 ++ (fragment0127827Chars ++ (chunk0014SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 459) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 458) (fragment0127827Chars ++ (chunk0014SuffixChars00 ++ tail))).bind
        (chunk0014AfterValue00 (fuel + 458) acc) := array_chunk0014_head fuel (chunk0014SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0127827Value, chunk0014SuffixChars00 ++ tail)).bind
        (chunk0014AfterValue00 (fuel + 458) acc) :=
      congrArg (fun result => result.bind (chunk0014AfterValue00 (fuel + 458) acc))
        (value_fragment0127827 (fuel + 208) (chunk0014SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 458) (SourceJson.white tail) (chunk0014Push00 acc) := by rfl

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
noncomputable def chunk0015Chars00 : List Char := chunk0015LeadChars00 ++ fragment0129454Chars ++ chunk0015SuffixChars00
noncomputable def chunk0015Push00 (acc : List SourceJson) : List SourceJson := fragment0129454Value :: acc

noncomputable def chunk0015AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0015_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 458)
      (SourceJson.white (chunk0015LeadChars00 ++ (fragment0129454Chars ++ rest))) acc =
      (SourceJson.value (fuel + 457) (fragment0129454Chars ++ rest)).bind
        (chunk0015AfterValue00 (fuel + 457) acc) := by rfl

theorem array_chunk0015 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 458) (SourceJson.white (chunk0015Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 457) (SourceJson.white tail) (chunk0015Push00 acc) := by
  have hinput : chunk0015Chars00 ++ tail = chunk0015LeadChars00 ++ (fragment0129454Chars ++ (chunk0015SuffixChars00 ++ tail)) := by
    simp only [chunk0015Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 458) (SourceJson.white (chunk0015Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 458)
          (SourceJson.white (chunk0015LeadChars00 ++ (fragment0129454Chars ++ (chunk0015SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 458) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 457) (fragment0129454Chars ++ (chunk0015SuffixChars00 ++ tail))).bind
        (chunk0015AfterValue00 (fuel + 457) acc) := array_chunk0015_head fuel (chunk0015SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0129454Value, chunk0015SuffixChars00 ++ tail)).bind
        (chunk0015AfterValue00 (fuel + 457) acc) :=
      congrArg (fun result => result.bind (chunk0015AfterValue00 (fuel + 457) acc))
        (value_fragment0129454 (fuel + 56) (chunk0015SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 457) (SourceJson.white tail) (chunk0015Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0008Chars00 ++ chunk0009Chars00 ++ chunk0010Chars00 ++ chunk0011Chars00 ++ chunk0012Chars00 ++ chunk0013Chars00 ++ chunk0014Chars00 ++ chunk0015Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0015Push00 (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 465) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 457) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0008Chars00 ++ (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 465) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 465) (SourceJson.white (chunk0008Chars00 ++ (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 465) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 464) (SourceJson.white (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))))) (chunk0008Push00 (acc)) := array_chunk0008 fuel (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 463) (SourceJson.white (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) (chunk0009Push00 (chunk0008Push00 (acc))) := array_chunk0009 fuel (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))) (chunk0008Push00 (acc))
    _ = SourceJson.array (fuel + 462) (SourceJson.white (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))) (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))) := array_chunk0010 fuel (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))) (chunk0009Push00 (chunk0008Push00 (acc)))
    _ = SourceJson.array (fuel + 461) (SourceJson.white (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))) (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))) := array_chunk0011 fuel (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))) (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))
    _ = SourceJson.array (fuel + 460) (SourceJson.white (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))) (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))) := array_chunk0012 fuel (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))) (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))
    _ = SourceJson.array (fuel + 459) (SourceJson.white (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))) (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))) := array_chunk0013 fuel (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))) (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))
    _ = SourceJson.array (fuel + 458) (SourceJson.white (chunk0015Chars00 ++ (tail))) (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))))) := array_chunk0014 fuel (chunk0015Chars00 ++ (tail)) (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))))
    _ = SourceJson.array (fuel + 457) (SourceJson.white tail) (blockPush acc) := array_chunk0015 fuel (tail) (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 117882).take 13504 = blockChars := by rfl

theorem block_original_split : sourceRest 117882 = blockChars ++ sourceRest 131386 := by
  calc
    sourceRest 117882 = (sourceRest 117882).take 13504 ++ (sourceRest 117882).drop 13504 :=
      (List.take_append_drop 13504 (sourceRest 117882)).symm
    _ = blockChars ++ (sourceRest 117882).drop 13504 :=
      congrArg (fun part => part ++ (sourceRest 117882).drop 13504) block_original_prefix
    _ = blockChars ++ sourceRest 131386 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 117882 13504)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 465) (SourceJson.white (sourceRest 117882)) acc =
      SourceJson.array (fuel + 457) (SourceJson.white (sourceRest 131386)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 465) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 131386) acc)

#print axioms object_fragment0117888_field_000
#print axioms object_fragment0117888_field_001
#print axioms object_fragment0117888_field_002
#print axioms object_fragment0117888_field_003
#print axioms object_fragment0117888_field_004
#print axioms object_fragment0117888_field_005
#print axioms object_fragment0117888_field_006
#print axioms object_fragment0117888_field_007
#print axioms object_fragment0117888_field_008
#print axioms object_fragment0117888_field_009
#print axioms value_fragment0117888
#print axioms object_fragment0119450_field_000
#print axioms object_fragment0119450_field_001
#print axioms object_fragment0119450_field_002
#print axioms object_fragment0119450_field_003
#print axioms object_fragment0119450_field_004
#print axioms object_fragment0119450_field_005
#print axioms object_fragment0119450_field_006
#print axioms object_fragment0119450_field_007
#print axioms object_fragment0119450_field_008
#print axioms object_fragment0119450_field_009
#print axioms value_fragment0119450
#print axioms object_fragment0121338_field_000
#print axioms object_fragment0121338_field_001
#print axioms object_fragment0121338_field_002
#print axioms object_fragment0121338_field_003
#print axioms object_fragment0121338_field_004
#print axioms object_fragment0121338_field_005
#print axioms object_fragment0121338_field_006
#print axioms object_fragment0121338_field_007
#print axioms object_fragment0121338_field_008
#print axioms object_fragment0121338_field_009
#print axioms value_fragment0121338
#print axioms object_fragment0122954_field_000
#print axioms object_fragment0122954_field_001
#print axioms object_fragment0122954_field_002
#print axioms object_fragment0122954_field_003
#print axioms object_fragment0122954_field_004
#print axioms object_fragment0122954_field_005
#print axioms object_fragment0122954_field_006
#print axioms object_fragment0122954_field_007
#print axioms object_fragment0122954_field_008
#print axioms object_fragment0122954_field_009
#print axioms value_fragment0122954
#print axioms object_fragment0124549_field_000
#print axioms object_fragment0124549_field_001
#print axioms object_fragment0124549_field_002
#print axioms object_fragment0124549_field_003
#print axioms object_fragment0124549_field_004
#print axioms object_fragment0124549_field_005
#print axioms object_fragment0124549_field_006
#print axioms object_fragment0124549_field_007
#print axioms object_fragment0124549_field_008
#print axioms object_fragment0124549_field_009
#print axioms value_fragment0124549
#print axioms object_fragment0126175_field_000
#print axioms object_fragment0126175_field_001
#print axioms object_fragment0126175_field_002
#print axioms object_fragment0126175_field_003
#print axioms object_fragment0126175_field_004
#print axioms object_fragment0126175_field_005
#print axioms object_fragment0126175_field_006
#print axioms object_fragment0126175_field_007
#print axioms object_fragment0126175_field_008
#print axioms object_fragment0126175_field_009
#print axioms value_fragment0126175
#print axioms object_fragment0127827_field_000
#print axioms object_fragment0127827_field_001
#print axioms object_fragment0127827_field_002
#print axioms object_fragment0127827_field_003
#print axioms object_fragment0127827_field_004
#print axioms object_fragment0127827_field_005
#print axioms object_fragment0127827_field_006
#print axioms object_fragment0127827_field_007
#print axioms object_fragment0127827_field_008
#print axioms object_fragment0127827_field_009
#print axioms value_fragment0127827
#print axioms object_fragment0129454_field_000
#print axioms object_fragment0129454_field_001
#print axioms object_fragment0129454_field_002
#print axioms object_fragment0129454_field_003
#print axioms object_fragment0129454_field_004
#print axioms object_fragment0129454_field_005
#print axioms object_fragment0129454_field_006
#print axioms object_fragment0129454_field_007
#print axioms object_fragment0129454_field_008
#print axioms object_fragment0129454_field_009
#print axioms value_fragment0129454
#print axioms array_chunk0008_head
#print axioms array_chunk0008
#print axioms array_chunk0009_head
#print axioms array_chunk0009
#print axioms array_chunk0010_head
#print axioms array_chunk0010
#print axioms array_chunk0011_head
#print axioms array_chunk0011
#print axioms array_chunk0012_head
#print axioms array_chunk0012
#print axioms array_chunk0013_head
#print axioms array_chunk0013
#print axioms array_chunk0014_head
#print axioms array_chunk0014
#print axioms array_chunk0015_head
#print axioms array_chunk0015
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock001

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
