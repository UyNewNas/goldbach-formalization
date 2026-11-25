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

namespace SimplicesBlock059

noncomputable def fragment0424263Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0424263Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0424263Field000Value00 : SourceJson := .number (String.ofList ['1', '1', '6'])
noncomputable def fragment0424263Acc00100 : List (String × SourceJson) := (fragment0424263Field000Key00, fragment0424263Field000Value00) :: fragment0424263Acc00000
noncomputable def fragment0424263Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '6', ',']

theorem object_fragment0424263_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 281) (SourceJson.white (fragment0424263Field000Chars00 ++ tail)) fragment0424263Acc00000 =
      SourceJson.object (fuel + 280) (SourceJson.white tail) fragment0424263Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0424263_object_field_000"
  err.flush

noncomputable def fragment0424263Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0424263Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['3', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '5'])]
noncomputable def fragment0424263Acc00200 : List (String × SourceJson) := (fragment0424263Field001Key00, fragment0424263Field001Value00) :: fragment0424263Acc00100
noncomputable def fragment0424263Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0424263_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 280) (SourceJson.white (fragment0424263Field001Chars00 ++ tail)) fragment0424263Acc00100 =
      SourceJson.object (fuel + 279) (SourceJson.white tail) fragment0424263Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0424263_object_field_001"
  err.flush

noncomputable def fragment0424263Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0424263Field002Value00 : SourceJson := .str (String.ofList ['1', '8', '4', '7', '3', '7', '7', '3', '2', '4', '9', '3', '6', '5', '1', '1', '3', '8', '9', '9', '6', '0', '2', '0', '0', '3', '9', '9', '3', '2', '4', '4', '6', '3', '2', '1', '8', '6', '9', '9', '0', '7', '4', '9', '/', '3', '2', '8', '8', '9', '8', '1', '3', '7', '4', '0', '8', '3', '3', '9', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0424263Acc00300 : List (String × SourceJson) := (fragment0424263Field002Key00, fragment0424263Field002Value00) :: fragment0424263Acc00200
noncomputable def fragment0424263Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '8', '4', '7', '3', '7', '7', '3', '2', '4', '9', '3', '6', '5', '1', '1', '3', '8', '9', '9', '6', '0', '2', '0', '0', '3', '9', '9', '3', '2', '4', '4', '6', '3', '2', '1', '8', '6', '9', '9', '0', '7', '4', '9', '/', '3', '2', '8', '8', '9', '8', '1', '3', '7', '4', '0', '8', '3', '3', '9', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0424263_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 279) (SourceJson.white (fragment0424263Field002Chars00 ++ tail)) fragment0424263Acc00200 =
      SourceJson.object (fuel + 278) (SourceJson.white tail) fragment0424263Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0424263_object_field_002"
  err.flush

noncomputable def fragment0424263Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0424263Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0424263Acc00400 : List (String × SourceJson) := (fragment0424263Field003Key00, fragment0424263Field003Value00) :: fragment0424263Acc00300
noncomputable def fragment0424263Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0424263_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 278) (SourceJson.white (fragment0424263Field003Chars00 ++ tail)) fragment0424263Acc00300 =
      SourceJson.object (fuel + 277) (SourceJson.white tail) fragment0424263Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0424263_object_field_003"
  err.flush

noncomputable def fragment0424263Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0424263Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '5', '5', '7', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0424263Acc00500 : List (String × SourceJson) := (fragment0424263Field004Key00, fragment0424263Field004Value00) :: fragment0424263Acc00400
noncomputable def fragment0424263Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '5', '5', '7', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0424263_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 277) (SourceJson.white (fragment0424263Field004Chars00 ++ tail)) fragment0424263Acc00400 =
      SourceJson.object (fuel + 276) (SourceJson.white tail) fragment0424263Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0424263_object_field_004"
  err.flush

noncomputable def fragment0424263Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0424263Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '2', '9', '9', '3', '2', '5', '6', '0', '2', '1', '6', '1', '1', '9', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '0', '6', '1', '7', '5', '9', '1', '1', '7', '8', '5', '3', '9', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '5', '1', '9', '6', '5', '1', '8', '5', '5', '7', '9', '2', '1', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '0', '2', '0', '2', '2', '6', '2', '7', '9', '9', '6', '9', '3', '/', '2', '3', '4', '6', '0', '0', '0', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '5', '8', '1', '3', '1', '4', '2', '8', '2', '9', '2', '6', '1', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '2', '7', '4', '5', '8', '6', '0', '4', '3', '3', '8', '3', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '3', '8', '5', '5', '2', '9', '1', '2', '4', '0', '3', '/', '9', '8', '7', '7', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '4', '3', '0', '3', '5', '4', '9', '2', '1', '1', '8', '9', '/', '1', '8', '7', '6', '8', '0', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '3', '0', '2', '4', '0', '2', '3', '2', '2', '6', '9', '9', '1', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '8', '9', '0', '9', '4', '5', '8', '2', '5', '1', '9', '1', '1', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0424263Acc00600 : List (String × SourceJson) := (fragment0424263Field005Key00, fragment0424263Field005Value00) :: fragment0424263Acc00500
noncomputable def fragment0424263Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '9', '3', '2', '5', '6', '0', '2', '1', '6', '1', '1', '9', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '0', '6', '1', '7', '5', '9', '1', '1', '7', '8', '5', '3', '9', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '5', '1', '9', '6', '5', '1', '8', '5', '5', '7', '9', '2', '1', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '0', '2', '0', '2', '2', '6', '2', '7', '9', '9', '6', '9', '3', '/', '2', '3', '4', '6', '0', '0', '0', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '5', '8', '1', '3', '1', '4', '2', '8', '2', '9', '2', '6', '1', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '2', '7', '4', '5', '8', '6', '0', '4', '3', '3', '8', '3', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '3', '8', '5', '5', '2', '9', '1', '2', '4', '0', '3', '/', '9', '8', '7', '7', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '4', '3', '0', '3', '5', '4', '9', '2', '1', '1', '8', '9', '/', '1', '8', '7', '6', '8', '0', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '3', '0', '2', '4', '0', '2', '3', '2', '2', '6', '9', '9', '1', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '8', '9', '0', '9', '4', '5', '8', '2', '5', '1', '9', '1', '1', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0424263_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 276) (SourceJson.white (fragment0424263Field005Chars00 ++ tail)) fragment0424263Acc00500 =
      SourceJson.object (fuel + 275) (SourceJson.white tail) fragment0424263Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0424263_object_field_005"
  err.flush

noncomputable def fragment0424263Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0424263Field006Value00 : SourceJson := .str (String.ofList ['6', '1', '5', '7', '2', '5', '1', '5', '7', '4', '4', '5', '3', '4', '9', '1', '7', '6', '8', '1', '8', '0', '7', '8', '2', '6', '6', '3', '4', '6', '3', '2', '7', '6', '6', '3', '1', '5', '0', '0', '5', '6', '3', '6', '0', '2', '2', '6', '8', '3', '6', '4', '/', '8', '4', '0', '4', '3', '5', '4', '3', '4', '0', '3', '0', '0', '5', '8', '4', '6', '6', '6', '6', '0', '1', '4', '2', '7', '9', '0', '3', '9', '3', '0', '0', '6', '5', '2', '2', '6', '8', '9', '5', '7', '5', '4', '7', '2', '2', '9', '3', '4', '5', '0', '5', '8', '6', '2', '8', '3', '6', '0', '2', '8', '7', '7', '3', '1', '2', '5'])
noncomputable def fragment0424263Acc00700 : List (String × SourceJson) := (fragment0424263Field006Key00, fragment0424263Field006Value00) :: fragment0424263Acc00600
noncomputable def fragment0424263Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '1', '5', '7', '2', '5', '1', '5', '7', '4', '4', '5', '3', '4', '9', '1', '7', '6', '8', '1', '8', '0', '7', '8', '2', '6', '6', '3', '4', '6', '3', '2', '7', '6', '6', '3', '1', '5', '0', '0', '5', '6', '3', '6', '0', '2', '2', '6', '8', '3', '6', '4', '/', '8', '4', '0', '4', '3', '5', '4', '3', '4', '0', '3', '0', '0', '5', '8', '4', '6', '6', '6', '6', '0', '1', '4', '2', '7', '9', '0', '3', '9', '3', '0', '0', '6', '5', '2', '2', '6', '8', '9', '5', '7', '5', '4', '7', '2', '2', '9', '3', '4', '5', '0', '5', '8', '6', '2', '8', '3', '6', '0', '2', '8', '7', '7', '3', '1', '2', '5', '"', ',']

theorem object_fragment0424263_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 275) (SourceJson.white (fragment0424263Field006Chars00 ++ tail)) fragment0424263Acc00600 =
      SourceJson.object (fuel + 274) (SourceJson.white tail) fragment0424263Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0424263_object_field_006"
  err.flush

noncomputable def fragment0424263Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0424263Field007Value00 : SourceJson := .str (String.ofList ['3', '1', '3', '5', '0', '5', '9', '2', '5', '9', '0', '0', '2', '0', '2', '0', '3', '0', '4', '4', '1', '0', '0', '7', '3', '1', '5', '6', '0', '7', '2', '1', '5', '4', '4', '5', '8', '9', '6', '6', '1', '1', '0', '7', '9', '0', '3', '5', '2', '9', '6', '9', '4', '8', '4', '7', '6', '4', '8', '6', '3', '3', '3', '6', '9', '1', '6', '6', '8', '8', '8', '7', '9', '9', '0', '7', '4', '5', '8', '9', '6', '8', '7', '0', '7', '5', '3', '2', '2', '4', '6', '8', '5', '4', '6', '4', '2', '3', '1', '3', '8', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '8', '2', '5', '8', '2', '8', '7', '3', '7', '2', '6', '3', '4', '5', '9', '1', '3', '2', '8', '1', '2', '9', '0', '9', '6', '0', '4', '6', '1', '4', '2', '9', '1', '8', '5', '1', '8', '2', '3', '2', '8', '9', '1', '2', '4', '0', '6', '8', '4', '5', '4', '0', '6', '1', '4', '2', '7', '4', '1', '3', '6', '1', '9', '2', '3', '2', '2', '3', '6', '6', '4', '5', '3', '9', '0', '4', '7', '7', '4', '0', '1', '0', '5', '7', '9', '2', '5', '3', '2', '0', '0', '4', '6', '7', '5', '5', '2', '8', '0', '8', '3', '8', '4', '2', '4', '9', '7', '1', '1', '0', '8', '2', '9', '6', '7', '7', '8', '1', '3', '7', '9', '9', '5', '4', '8', '5', '2', '4', '8', '2', '6', '4', '6', '9', '0', '0', '9', '0', '9', '3', '3'])
noncomputable def fragment0424263Acc00800 : List (String × SourceJson) := (fragment0424263Field007Key00, fragment0424263Field007Value00) :: fragment0424263Acc00700
noncomputable def fragment0424263Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '1', '3', '5', '0', '5', '9', '2', '5', '9', '0', '0', '2', '0', '2', '0', '3', '0', '4', '4', '1', '0', '0', '7', '3', '1', '5', '6', '0', '7', '2', '1', '5', '4', '4', '5', '8', '9', '6', '6', '1', '1', '0', '7', '9', '0', '3', '5', '2', '9', '6', '9', '4', '8', '4', '7', '6', '4', '8', '6', '3', '3', '3', '6', '9', '1', '6', '6', '8', '8', '8', '7', '9', '9', '0', '7', '4', '5', '8', '9', '6', '8', '7', '0', '7', '5', '3', '2', '2', '4', '6', '8', '5', '4', '6', '4', '2', '3', '1', '3', '8', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '8', '2', '5', '8', '2', '8', '7', '3', '7', '2', '6', '3', '4', '5', '9', '1', '3', '2', '8', '1', '2', '9', '0', '9', '6', '0', '4', '6', '1', '4', '2', '9', '1', '8', '5', '1', '8', '2', '3', '2', '8', '9', '1', '2', '4', '0', '6', '8', '4', '5', '4', '0', '6', '1', '4', '2', '7', '4', '1', '3', '6', '1', '9', '2', '3', '2', '2', '3', '6', '6', '4', '5', '3', '9', '0', '4', '7', '7', '4', '0', '1', '0', '5', '7', '9', '2', '5', '3', '2', '0', '0', '4', '6', '7', '5', '5', '2', '8', '0', '8', '3', '8', '4', '2', '4', '9', '7', '1', '1', '0', '8', '2', '9', '6', '7', '7', '8', '1', '3', '7', '9', '9', '5', '4', '8', '5', '2', '4', '8', '2', '6', '4', '6', '9', '0', '0', '9', '0', '9', '3', '3', '"', ',']

theorem object_fragment0424263_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 274) (SourceJson.white (fragment0424263Field007Chars00 ++ tail)) fragment0424263Acc00700 =
      SourceJson.object (fuel + 273) (SourceJson.white tail) fragment0424263Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0424263_object_field_007"
  err.flush

noncomputable def fragment0424263Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0424263Field008Value00 : SourceJson := .str (String.ofList ['5', '8', '0', '4', '4', '6', '4', '0', '7', '4', '5', '6', '6', '4'])
noncomputable def fragment0424263Acc00900 : List (String × SourceJson) := (fragment0424263Field008Key00, fragment0424263Field008Value00) :: fragment0424263Acc00800
noncomputable def fragment0424263Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '8', '0', '4', '4', '6', '4', '0', '7', '4', '5', '6', '6', '4', '"', ',']

theorem object_fragment0424263_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 273) (SourceJson.white (fragment0424263Field008Chars00 ++ tail)) fragment0424263Acc00800 =
      SourceJson.object (fuel + 272) (SourceJson.white tail) fragment0424263Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0424263_object_field_008"
  err.flush

noncomputable def fragment0424263Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0424263Field009Value00 : SourceJson := .str (String.ofList ['3', '1', '7', '3', '9', '1', '2', '8', '5', '7', '0', '6', '7', '1', '5'])
noncomputable def fragment0424263Acc01000 : List (String × SourceJson) := (fragment0424263Field009Key00, fragment0424263Field009Value00) :: fragment0424263Acc00900
noncomputable def fragment0424263Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '7', '3', '9', '1', '2', '8', '5', '7', '0', '6', '7', '1', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0424263_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 272) (SourceJson.white (fragment0424263Field009Chars00 ++ tail)) fragment0424263Acc00900 =
      .ok (.obj (fragment0424263Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0424263_object_field_009"
  err.flush

noncomputable def fragment0424263Chars : List Char := '{' :: (fragment0424263Field000Chars00 ++ fragment0424263Field001Chars00 ++ fragment0424263Field002Chars00 ++ fragment0424263Field003Chars00 ++ fragment0424263Field004Chars00 ++ fragment0424263Field005Chars00 ++ fragment0424263Field006Chars00 ++ fragment0424263Field007Chars00 ++ fragment0424263Field008Chars00 ++ fragment0424263Field009Chars00)
noncomputable def fragment0424263Value : SourceJson := .obj (fragment0424263Acc01000.reverse)

theorem value_fragment0424263 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 282) (fragment0424263Chars ++ tail) =
      .ok (fragment0424263Value, tail) := by
  have hinput : fragment0424263Chars ++ tail = '{' :: (fragment0424263Field000Chars00 ++ (fragment0424263Field001Chars00 ++ (fragment0424263Field002Chars00 ++ (fragment0424263Field003Chars00 ++ (fragment0424263Field004Chars00 ++ (fragment0424263Field005Chars00 ++ (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0424263Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 282) (fragment0424263Chars ++ tail) =
        SourceJson.value (fuel + 282) ('{' :: (fragment0424263Field000Chars00 ++ (fragment0424263Field001Chars00 ++ (fragment0424263Field002Chars00 ++ (fragment0424263Field003Chars00 ++ (fragment0424263Field004Chars00 ++ (fragment0424263Field005Chars00 ++ (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 282)) hinput
    _ = SourceJson.object (fuel + 281) (SourceJson.white (fragment0424263Field000Chars00 ++ (fragment0424263Field001Chars00 ++ (fragment0424263Field002Chars00 ++ (fragment0424263Field003Chars00 ++ (fragment0424263Field004Chars00 ++ (fragment0424263Field005Chars00 ++ (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail)))))))))))) fragment0424263Acc00000 := by rfl
    _ = SourceJson.object (fuel + 280) (SourceJson.white (fragment0424263Field001Chars00 ++ (fragment0424263Field002Chars00 ++ (fragment0424263Field003Chars00 ++ (fragment0424263Field004Chars00 ++ (fragment0424263Field005Chars00 ++ (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail))))))))))) fragment0424263Acc00100 := object_fragment0424263_field_000 fuel (fragment0424263Field001Chars00 ++ (fragment0424263Field002Chars00 ++ (fragment0424263Field003Chars00 ++ (fragment0424263Field004Chars00 ++ (fragment0424263Field005Chars00 ++ (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 279) (SourceJson.white (fragment0424263Field002Chars00 ++ (fragment0424263Field003Chars00 ++ (fragment0424263Field004Chars00 ++ (fragment0424263Field005Chars00 ++ (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail)))))))))) fragment0424263Acc00200 := object_fragment0424263_field_001 fuel (fragment0424263Field002Chars00 ++ (fragment0424263Field003Chars00 ++ (fragment0424263Field004Chars00 ++ (fragment0424263Field005Chars00 ++ (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 278) (SourceJson.white (fragment0424263Field003Chars00 ++ (fragment0424263Field004Chars00 ++ (fragment0424263Field005Chars00 ++ (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail))))))))) fragment0424263Acc00300 := object_fragment0424263_field_002 fuel (fragment0424263Field003Chars00 ++ (fragment0424263Field004Chars00 ++ (fragment0424263Field005Chars00 ++ (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 277) (SourceJson.white (fragment0424263Field004Chars00 ++ (fragment0424263Field005Chars00 ++ (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail)))))))) fragment0424263Acc00400 := object_fragment0424263_field_003 fuel (fragment0424263Field004Chars00 ++ (fragment0424263Field005Chars00 ++ (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 276) (SourceJson.white (fragment0424263Field005Chars00 ++ (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail))))))) fragment0424263Acc00500 := object_fragment0424263_field_004 fuel (fragment0424263Field005Chars00 ++ (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 275) (SourceJson.white (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail)))))) fragment0424263Acc00600 := object_fragment0424263_field_005 fuel (fragment0424263Field006Chars00 ++ (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 274) (SourceJson.white (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail))))) fragment0424263Acc00700 := object_fragment0424263_field_006 fuel (fragment0424263Field007Chars00 ++ (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 273) (SourceJson.white (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail)))) fragment0424263Acc00800 := object_fragment0424263_field_007 fuel (fragment0424263Field008Chars00 ++ (fragment0424263Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 272) (SourceJson.white (fragment0424263Field009Chars00 ++ (tail))) fragment0424263Acc00900 := object_fragment0424263_field_008 fuel (fragment0424263Field009Chars00 ++ (tail))
    _ = .ok (fragment0424263Value, tail) := object_fragment0424263_field_009 fuel (tail)

noncomputable def fragment0425968Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0425968Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0425968Field000Value00 : SourceJson := .number (String.ofList ['1', '1', '7'])
noncomputable def fragment0425968Acc00100 : List (String × SourceJson) := (fragment0425968Field000Key00, fragment0425968Field000Value00) :: fragment0425968Acc00000
noncomputable def fragment0425968Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '7', ',']

theorem object_fragment0425968_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 219) (SourceJson.white (fragment0425968Field000Chars00 ++ tail)) fragment0425968Acc00000 =
      SourceJson.object (fuel + 218) (SourceJson.white tail) fragment0425968Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0425968_object_field_000"
  err.flush

noncomputable def fragment0425968Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0425968Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['3', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '4'])]
noncomputable def fragment0425968Acc00200 : List (String × SourceJson) := (fragment0425968Field001Key00, fragment0425968Field001Value00) :: fragment0425968Acc00100
noncomputable def fragment0425968Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0425968_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0425968Field001Chars00 ++ tail)) fragment0425968Acc00100 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment0425968Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0425968_object_field_001"
  err.flush

noncomputable def fragment0425968Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0425968Field002Value00 : SourceJson := .str (String.ofList ['1', '0', '3', '2', '3', '7', '9', '9', '2', '1', '9', '5', '2', '3', '8', '0', '2', '3', '1', '4', '4', '1', '3', '5', '9', '6', '3', '3', '9', '5', '9', '6', '8', '4', '3', '6', '4', '7', '9', '2', '7', '9', '/', '1', '7', '5', '4', '1', '7', '2', '5', '0', '7', '1', '0', '9', '1', '1', '7', '1', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0425968Acc00300 : List (String × SourceJson) := (fragment0425968Field002Key00, fragment0425968Field002Value00) :: fragment0425968Acc00200
noncomputable def fragment0425968Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '0', '3', '2', '3', '7', '9', '9', '2', '1', '9', '5', '2', '3', '8', '0', '2', '3', '1', '4', '4', '1', '3', '5', '9', '6', '3', '3', '9', '5', '9', '6', '8', '4', '3', '6', '4', '7', '9', '2', '7', '9', '/', '1', '7', '5', '4', '1', '7', '2', '5', '0', '7', '1', '0', '9', '1', '1', '7', '1', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0425968_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0425968Field002Chars00 ++ tail)) fragment0425968Acc00200 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0425968Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0425968_object_field_002"
  err.flush

noncomputable def fragment0425968Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0425968Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0425968Acc00400 : List (String × SourceJson) := (fragment0425968Field003Key00, fragment0425968Field003Value00) :: fragment0425968Acc00300
noncomputable def fragment0425968Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0425968_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0425968Field003Chars00 ++ tail)) fragment0425968Acc00300 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment0425968Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0425968_object_field_003"
  err.flush

noncomputable def fragment0425968Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0425968Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '3', '1', '/', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '6', '3', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0425968Acc00500 : List (String × SourceJson) := (fragment0425968Field004Key00, fragment0425968Field004Value00) :: fragment0425968Acc00400
noncomputable def fragment0425968Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '3', '1', '/', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '6', '3', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0425968_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0425968Field004Chars00 ++ tail)) fragment0425968Acc00400 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment0425968Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0425968_object_field_004"
  err.flush

noncomputable def fragment0425968Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0425968Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '4', '0', '5', '5', '0', '9', '1', '6', '4', '1', '1', '/', '1', '9', '0', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '9', '6', '7', '3', '4', '8', '6', '0', '7', '/', '1', '9', '0', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '4', '7', '4', '3', '7', '9', '8', '8', '9', '/', '3', '8', '0', '3', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '6', '9', '9', '8', '6', '9', '8', '3', '2', '9', '3', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '5', '4', '1', '6', '3', '6', '2', '7', '8', '7', '/', '1', '3', '3', '1', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '7', '7', '6', '5', '6', '2', '5', '9', '2', '7', '/', '1', '9', '0', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '3', '0', '7', '7', '6', '8', '7', '1', '1', '/', '7', '9', '8', '6', '3', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '1', '3', '8', '9', '0', '7', '8', '2', '3', '7', '9', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '1', '3', '8', '8', '8', '1', '2', '0', '2', '5', '1', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '3', '4', '8', '6', '3', '9', '4', '2', '4', '9', '/', '7', '9', '8', '6', '3', '8', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0425968Acc00600 : List (String × SourceJson) := (fragment0425968Field005Key00, fragment0425968Field005Value00) :: fragment0425968Acc00500
noncomputable def fragment0425968Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '5', '5', '0', '9', '1', '6', '4', '1', '1', '/', '1', '9', '0', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '9', '6', '7', '3', '4', '8', '6', '0', '7', '/', '1', '9', '0', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '4', '7', '4', '3', '7', '9', '8', '8', '9', '/', '3', '8', '0', '3', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '9', '9', '8', '6', '9', '8', '3', '2', '9', '3', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '5', '4', '1', '6', '3', '6', '2', '7', '8', '7', '/', '1', '3', '3', '1', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '7', '6', '5', '6', '2', '5', '9', '2', '7', '/', '1', '9', '0', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '1', '3', '0', '7', '7', '6', '8', '7', '1', '1', '/', '7', '9', '8', '6', '3', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '1', '3', '8', '9', '0', '7', '8', '2', '3', '7', '9', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '1', '3', '8', '8', '8', '1', '2', '0', '2', '5', '1', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '3', '4', '8', '6', '3', '9', '4', '2', '4', '9', '/', '7', '9', '8', '6', '3', '8', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0425968_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment0425968Field005Chars00 ++ tail)) fragment0425968Acc00500 =
      SourceJson.object (fuel + 213) (SourceJson.white tail) fragment0425968Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0425968_object_field_005"
  err.flush

noncomputable def fragment0425968Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0425968Field006Value00 : SourceJson := .str (String.ofList ['1', '5', '1', '7', '1', '4', '7', '4', '4', '2', '0', '4', '2', '0', '2', '8', '7', '1', '0', '6', '4', '8', '7', '1', '7', '2', '1', '2', '7', '2', '8', '9', '3', '3', '6', '3', '0', '0', '0', '7', '4', '0', '3', '8', '9', '8', '3', '/', '1', '9', '4', '7', '9', '3', '3', '1', '6', '5', '3', '1', '5', '5', '9', '8', '6', '9', '7', '7', '6', '8', '9', '4', '1', '7', '2', '4', '0', '8', '9', '2', '4', '3', '1', '9', '7', '8', '9', '8', '0', '5', '6', '1', '7', '8', '9', '9', '2', '8', '4', '9', '5', '8', '0', '0', '2', '6', '5', '6', '2', '5', '0', '0', '0'])
noncomputable def fragment0425968Acc00700 : List (String × SourceJson) := (fragment0425968Field006Key00, fragment0425968Field006Value00) :: fragment0425968Acc00600
noncomputable def fragment0425968Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '1', '7', '1', '4', '7', '4', '4', '2', '0', '4', '2', '0', '2', '8', '7', '1', '0', '6', '4', '8', '7', '1', '7', '2', '1', '2', '7', '2', '8', '9', '3', '3', '6', '3', '0', '0', '0', '7', '4', '0', '3', '8', '9', '8', '3', '/', '1', '9', '4', '7', '9', '3', '3', '1', '6', '5', '3', '1', '5', '5', '9', '8', '6', '9', '7', '7', '6', '8', '9', '4', '1', '7', '2', '4', '0', '8', '9', '2', '4', '3', '1', '9', '7', '8', '9', '8', '0', '5', '6', '1', '7', '8', '9', '9', '2', '8', '4', '9', '5', '8', '0', '0', '2', '6', '5', '6', '2', '5', '0', '0', '0', '"', ',']

theorem object_fragment0425968_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0425968Field006Chars00 ++ tail)) fragment0425968Acc00600 =
      SourceJson.object (fuel + 212) (SourceJson.white tail) fragment0425968Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0425968_object_field_006"
  err.flush

noncomputable def fragment0425968Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0425968Field007Value00 : SourceJson := .str (String.ofList ['7', '1', '2', '2', '5', '8', '3', '4', '3', '1', '1', '4', '0', '8', '9', '9', '8', '2', '2', '2', '8', '2', '2', '8', '1', '0', '7', '0', '9', '3', '8', '0', '1', '6', '1', '3', '2', '8', '5', '1', '5', '6', '1', '0', '6', '7', '5', '9', '3', '9', '0', '5', '1', '2', '0', '5', '7', '2', '4', '2', '4', '4', '4', '5', '9', '7', '1', '0', '2', '8', '2', '7', '1', '3', '5', '5', '8', '3', '0', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '9', '3', '3', '1', '4', '0', '6', '7', '1', '3', '4', '4', '2', '9', '4', '5', '1', '0', '5', '5', '8', '9', '0', '8', '1', '3', '5', '0', '8', '1', '1', '9', '1', '1', '1', '9', '1', '8', '8', '5', '1', '3', '0', '0', '6', '2', '9', '9', '8', '7', '5', '3', '1', '7', '7', '1', '2', '9', '0', '8', '1', '8', '5', '0', '2', '5', '3', '2', '0', '4', '4', '5', '9', '2', '8', '5', '3', '1', '1', '3', '4', '2', '7', '0', '0', '2', '2', '7', '2', '7', '7', '5', '2', '3', '6', '0', '3', '9', '1', '7', '4', '7', '4', '8', '5', '7', '3', '8', '0', '3', '1'])
noncomputable def fragment0425968Acc00800 : List (String × SourceJson) := (fragment0425968Field007Key00, fragment0425968Field007Value00) :: fragment0425968Acc00700
noncomputable def fragment0425968Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '1', '2', '2', '5', '8', '3', '4', '3', '1', '1', '4', '0', '8', '9', '9', '8', '2', '2', '2', '8', '2', '2', '8', '1', '0', '7', '0', '9', '3', '8', '0', '1', '6', '1', '3', '2', '8', '5', '1', '5', '6', '1', '0', '6', '7', '5', '9', '3', '9', '0', '5', '1', '2', '0', '5', '7', '2', '4', '2', '4', '4', '4', '5', '9', '7', '1', '0', '2', '8', '2', '7', '1', '3', '5', '5', '8', '3', '0', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '9', '3', '3', '1', '4', '0', '6', '7', '1', '3', '4', '4', '2', '9', '4', '5', '1', '0', '5', '5', '8', '9', '0', '8', '1', '3', '5', '0', '8', '1', '1', '9', '1', '1', '1', '9', '1', '8', '8', '5', '1', '3', '0', '0', '6', '2', '9', '9', '8', '7', '5', '3', '1', '7', '7', '1', '2', '9', '0', '8', '1', '8', '5', '0', '2', '5', '3', '2', '0', '4', '4', '5', '9', '2', '8', '5', '3', '1', '1', '3', '4', '2', '7', '0', '0', '2', '2', '7', '2', '7', '7', '5', '2', '3', '6', '0', '3', '9', '1', '7', '4', '7', '4', '8', '5', '7', '3', '8', '0', '3', '1', '"', ',']

theorem object_fragment0425968_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 212) (SourceJson.white (fragment0425968Field007Chars00 ++ tail)) fragment0425968Acc00700 =
      SourceJson.object (fuel + 211) (SourceJson.white tail) fragment0425968Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0425968_object_field_007"
  err.flush

noncomputable def fragment0425968Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0425968Field008Value00 : SourceJson := .str (String.ofList ['6', '1', '7', '0', '6', '8', '4', '2', '0', '1', '9'])
noncomputable def fragment0425968Acc00900 : List (String × SourceJson) := (fragment0425968Field008Key00, fragment0425968Field008Value00) :: fragment0425968Acc00800
noncomputable def fragment0425968Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '1', '7', '0', '6', '8', '4', '2', '0', '1', '9', '"', ',']

theorem object_fragment0425968_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 211) (SourceJson.white (fragment0425968Field008Chars00 ++ tail)) fragment0425968Acc00800 =
      SourceJson.object (fuel + 210) (SourceJson.white tail) fragment0425968Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0425968_object_field_008"
  err.flush

noncomputable def fragment0425968Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0425968Field009Value00 : SourceJson := .str (String.ofList ['3', '3', '3', '2', '5', '7', '2', '5', '4', '8', '4', '5'])
noncomputable def fragment0425968Acc01000 : List (String × SourceJson) := (fragment0425968Field009Key00, fragment0425968Field009Value00) :: fragment0425968Acc00900
noncomputable def fragment0425968Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '3', '2', '5', '7', '2', '5', '4', '8', '4', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0425968_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 210) (SourceJson.white (fragment0425968Field009Chars00 ++ tail)) fragment0425968Acc00900 =
      .ok (.obj (fragment0425968Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0425968_object_field_009"
  err.flush

noncomputable def fragment0425968Chars : List Char := '{' :: (fragment0425968Field000Chars00 ++ fragment0425968Field001Chars00 ++ fragment0425968Field002Chars00 ++ fragment0425968Field003Chars00 ++ fragment0425968Field004Chars00 ++ fragment0425968Field005Chars00 ++ fragment0425968Field006Chars00 ++ fragment0425968Field007Chars00 ++ fragment0425968Field008Chars00 ++ fragment0425968Field009Chars00)
noncomputable def fragment0425968Value : SourceJson := .obj (fragment0425968Acc01000.reverse)

theorem value_fragment0425968 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 220) (fragment0425968Chars ++ tail) =
      .ok (fragment0425968Value, tail) := by
  have hinput : fragment0425968Chars ++ tail = '{' :: (fragment0425968Field000Chars00 ++ (fragment0425968Field001Chars00 ++ (fragment0425968Field002Chars00 ++ (fragment0425968Field003Chars00 ++ (fragment0425968Field004Chars00 ++ (fragment0425968Field005Chars00 ++ (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0425968Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 220) (fragment0425968Chars ++ tail) =
        SourceJson.value (fuel + 220) ('{' :: (fragment0425968Field000Chars00 ++ (fragment0425968Field001Chars00 ++ (fragment0425968Field002Chars00 ++ (fragment0425968Field003Chars00 ++ (fragment0425968Field004Chars00 ++ (fragment0425968Field005Chars00 ++ (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 220)) hinput
    _ = SourceJson.object (fuel + 219) (SourceJson.white (fragment0425968Field000Chars00 ++ (fragment0425968Field001Chars00 ++ (fragment0425968Field002Chars00 ++ (fragment0425968Field003Chars00 ++ (fragment0425968Field004Chars00 ++ (fragment0425968Field005Chars00 ++ (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail)))))))))))) fragment0425968Acc00000 := by rfl
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0425968Field001Chars00 ++ (fragment0425968Field002Chars00 ++ (fragment0425968Field003Chars00 ++ (fragment0425968Field004Chars00 ++ (fragment0425968Field005Chars00 ++ (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail))))))))))) fragment0425968Acc00100 := object_fragment0425968_field_000 fuel (fragment0425968Field001Chars00 ++ (fragment0425968Field002Chars00 ++ (fragment0425968Field003Chars00 ++ (fragment0425968Field004Chars00 ++ (fragment0425968Field005Chars00 ++ (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0425968Field002Chars00 ++ (fragment0425968Field003Chars00 ++ (fragment0425968Field004Chars00 ++ (fragment0425968Field005Chars00 ++ (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail)))))))))) fragment0425968Acc00200 := object_fragment0425968_field_001 fuel (fragment0425968Field002Chars00 ++ (fragment0425968Field003Chars00 ++ (fragment0425968Field004Chars00 ++ (fragment0425968Field005Chars00 ++ (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0425968Field003Chars00 ++ (fragment0425968Field004Chars00 ++ (fragment0425968Field005Chars00 ++ (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail))))))))) fragment0425968Acc00300 := object_fragment0425968_field_002 fuel (fragment0425968Field003Chars00 ++ (fragment0425968Field004Chars00 ++ (fragment0425968Field005Chars00 ++ (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0425968Field004Chars00 ++ (fragment0425968Field005Chars00 ++ (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail)))))))) fragment0425968Acc00400 := object_fragment0425968_field_003 fuel (fragment0425968Field004Chars00 ++ (fragment0425968Field005Chars00 ++ (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment0425968Field005Chars00 ++ (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail))))))) fragment0425968Acc00500 := object_fragment0425968_field_004 fuel (fragment0425968Field005Chars00 ++ (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail)))))) fragment0425968Acc00600 := object_fragment0425968_field_005 fuel (fragment0425968Field006Chars00 ++ (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 212) (SourceJson.white (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail))))) fragment0425968Acc00700 := object_fragment0425968_field_006 fuel (fragment0425968Field007Chars00 ++ (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 211) (SourceJson.white (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail)))) fragment0425968Acc00800 := object_fragment0425968_field_007 fuel (fragment0425968Field008Chars00 ++ (fragment0425968Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 210) (SourceJson.white (fragment0425968Field009Chars00 ++ (tail))) fragment0425968Acc00900 := object_fragment0425968_field_008 fuel (fragment0425968Field009Chars00 ++ (tail))
    _ = .ok (fragment0425968Value, tail) := object_fragment0425968_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0116_before_reader"
  err.flush

noncomputable def chunk0116LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0116SuffixChars00 : List Char := [',']
noncomputable def chunk0116Chars00 : List Char := chunk0116LeadChars00 ++ fragment0424263Chars ++ chunk0116SuffixChars00
noncomputable def chunk0116Push00 (acc : List SourceJson) : List SourceJson := fragment0424263Value :: acc

noncomputable def chunk0116AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0116_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 488)
      (SourceJson.white (chunk0116LeadChars00 ++ (fragment0424263Chars ++ rest))) acc =
      (SourceJson.value (fuel + 487) (fragment0424263Chars ++ rest)).bind
        (chunk0116AfterValue00 (fuel + 487) acc) := by rfl

theorem array_chunk0116 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 488) (SourceJson.white (chunk0116Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 487) (SourceJson.white tail) (chunk0116Push00 acc) := by
  have hinput : chunk0116Chars00 ++ tail = chunk0116LeadChars00 ++ (fragment0424263Chars ++ (chunk0116SuffixChars00 ++ tail)) := by
    simp only [chunk0116Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 488) (SourceJson.white (chunk0116Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 488)
          (SourceJson.white (chunk0116LeadChars00 ++ (fragment0424263Chars ++ (chunk0116SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 488) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 487) (fragment0424263Chars ++ (chunk0116SuffixChars00 ++ tail))).bind
        (chunk0116AfterValue00 (fuel + 487) acc) := array_chunk0116_head fuel (chunk0116SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0424263Value, chunk0116SuffixChars00 ++ tail)).bind
        (chunk0116AfterValue00 (fuel + 487) acc) :=
      congrArg (fun result => result.bind (chunk0116AfterValue00 (fuel + 487) acc))
        (value_fragment0424263 (fuel + 205) (chunk0116SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 487) (SourceJson.white tail) (chunk0116Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0116_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0117_before_reader"
  err.flush

noncomputable def chunk0117LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0117SuffixChars00 : List Char := [',']
noncomputable def chunk0117Chars00 : List Char := chunk0117LeadChars00 ++ fragment0425968Chars ++ chunk0117SuffixChars00
noncomputable def chunk0117Push00 (acc : List SourceJson) : List SourceJson := fragment0425968Value :: acc

noncomputable def chunk0117AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0117_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 487)
      (SourceJson.white (chunk0117LeadChars00 ++ (fragment0425968Chars ++ rest))) acc =
      (SourceJson.value (fuel + 486) (fragment0425968Chars ++ rest)).bind
        (chunk0117AfterValue00 (fuel + 486) acc) := by rfl

theorem array_chunk0117 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 487) (SourceJson.white (chunk0117Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 486) (SourceJson.white tail) (chunk0117Push00 acc) := by
  have hinput : chunk0117Chars00 ++ tail = chunk0117LeadChars00 ++ (fragment0425968Chars ++ (chunk0117SuffixChars00 ++ tail)) := by
    simp only [chunk0117Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 487) (SourceJson.white (chunk0117Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 487)
          (SourceJson.white (chunk0117LeadChars00 ++ (fragment0425968Chars ++ (chunk0117SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 487) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 486) (fragment0425968Chars ++ (chunk0117SuffixChars00 ++ tail))).bind
        (chunk0117AfterValue00 (fuel + 486) acc) := array_chunk0117_head fuel (chunk0117SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0425968Value, chunk0117SuffixChars00 ++ tail)).bind
        (chunk0117AfterValue00 (fuel + 486) acc) :=
      congrArg (fun result => result.bind (chunk0117AfterValue00 (fuel + 486) acc))
        (value_fragment0425968 (fuel + 266) (chunk0117SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 486) (SourceJson.white tail) (chunk0117Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0117_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0116Chars00 ++ chunk0117Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0117Push00 (chunk0116Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 488) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 486) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0116Chars00 ++ (chunk0117Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 488) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 488) (SourceJson.white (chunk0116Chars00 ++ (chunk0117Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 488) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 487) (SourceJson.white (chunk0117Chars00 ++ (tail))) (chunk0116Push00 (acc)) := array_chunk0116 fuel (chunk0117Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 486) (SourceJson.white tail) (blockPush acc) := array_chunk0117 fuel (tail) (chunk0116Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 424257).take 3271 = blockChars := by rfl

theorem block_original_split : sourceRest 424257 = blockChars ++ sourceRest 427528 := by
  calc
    sourceRest 424257 = (sourceRest 424257).take 3271 ++ (sourceRest 424257).drop 3271 :=
      (List.take_append_drop 3271 (sourceRest 424257)).symm
    _ = blockChars ++ (sourceRest 424257).drop 3271 :=
      congrArg (fun part => part ++ (sourceRest 424257).drop 3271) block_original_prefix
    _ = blockChars ++ sourceRest 427528 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 424257 3271)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 488) (SourceJson.white (sourceRest 424257)) acc =
      SourceJson.array (fuel + 486) (SourceJson.white (sourceRest 427528)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 488) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 427528) acc)

#print axioms object_fragment0424263_field_000
#print axioms object_fragment0424263_field_001
#print axioms object_fragment0424263_field_002
#print axioms object_fragment0424263_field_003
#print axioms object_fragment0424263_field_004
#print axioms object_fragment0424263_field_005
#print axioms object_fragment0424263_field_006
#print axioms object_fragment0424263_field_007
#print axioms object_fragment0424263_field_008
#print axioms object_fragment0424263_field_009
#print axioms value_fragment0424263
#print axioms object_fragment0425968_field_000
#print axioms object_fragment0425968_field_001
#print axioms object_fragment0425968_field_002
#print axioms object_fragment0425968_field_003
#print axioms object_fragment0425968_field_004
#print axioms object_fragment0425968_field_005
#print axioms object_fragment0425968_field_006
#print axioms object_fragment0425968_field_007
#print axioms object_fragment0425968_field_008
#print axioms object_fragment0425968_field_009
#print axioms value_fragment0425968
#print axioms array_chunk0116_head
#print axioms array_chunk0116
#print axioms array_chunk0117_head
#print axioms array_chunk0117
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock059

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
