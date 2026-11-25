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

namespace SimplicesBlock011

noncomputable def fragment0263460Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0263460Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0263460Field000Value00 : SourceJson := .number (String.ofList ['2', '2'])
noncomputable def fragment0263460Acc00100 : List (String × SourceJson) := (fragment0263460Field000Key00, fragment0263460Field000Value00) :: fragment0263460Acc00000
noncomputable def fragment0263460Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '2', ',']

theorem object_fragment0263460_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0263460Field000Chars00 ++ tail)) fragment0263460Acc00000 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0263460Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263460_object_field_000"
  err.flush

noncomputable def fragment0263460Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0263460Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0263460Acc00200 : List (String × SourceJson) := (fragment0263460Field001Key00, fragment0263460Field001Value00) :: fragment0263460Acc00100
noncomputable def fragment0263460Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0263460_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0263460Field001Chars00 ++ tail)) fragment0263460Acc00100 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0263460Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263460_object_field_001"
  err.flush

noncomputable def fragment0263460Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0263460Field002Value00 : SourceJson := .str (String.ofList ['2', '2', '7', '6', '6', '8', '6', '5', '0', '8', '0', '6', '6', '7', '1', '9', '7', '0', '2', '0', '3', '9', '7', '1', '1', '7', '1', '7', '5', '8', '7', '7', '3', '2', '5', '0', '9', '/', '6', '3', '8', '9', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0263460Acc00300 : List (String × SourceJson) := (fragment0263460Field002Key00, fragment0263460Field002Value00) :: fragment0263460Acc00200
noncomputable def fragment0263460Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '2', '7', '6', '6', '8', '6', '5', '0', '8', '0', '6', '6', '7', '1', '9', '7', '0', '2', '0', '3', '9', '7', '1', '1', '7', '1', '7', '5', '8', '7', '7', '3', '2', '5', '0', '9', '/', '6', '3', '8', '9', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0263460_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0263460Field002Chars00 ++ tail)) fragment0263460Acc00200 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0263460Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263460_object_field_002"
  err.flush

noncomputable def fragment0263460Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0263460Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0263460Acc00400 : List (String × SourceJson) := (fragment0263460Field003Key00, fragment0263460Field003Value00) :: fragment0263460Acc00300
noncomputable def fragment0263460Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0263460_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0263460Field003Chars00 ++ tail)) fragment0263460Acc00300 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0263460Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263460_object_field_003"
  err.flush

noncomputable def fragment0263460Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0263460Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0263460Acc00500 : List (String × SourceJson) := (fragment0263460Field004Key00, fragment0263460Field004Value00) :: fragment0263460Acc00400
noncomputable def fragment0263460Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0263460_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0263460Field004Chars00 ++ tail)) fragment0263460Acc00400 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0263460Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263460_object_field_004"
  err.flush

noncomputable def fragment0263460Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0263460Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '6', '2', '1', '9', '4', '2', '1', '5', '0', '3', '/', '8', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '9', '6', '9', '8', '0', '2', '3', '6', '1', '/', '6', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '1', '9', '1', '0', '3', '7', '5', '2', '7', '/', '1', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '4', '3', '0', '1', '1', '9', '6', '3', '1', '1', '/', '6', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '4', '4', '2', '9', '9', '6', '0', '8', '6', '7', '/', '1', '8', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '7', '0', '0', '6', '9', '9', '4', '1', '5', '3', '/', '9', '1', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '6', '6', '2', '5', '5', '2', '3', '6', '5', '7', '/', '9', '1', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '0', '1', '5', '1', '1', '0', '7', '2', '0', '9', '/', '1', '8', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '1', '4', '6', '0', '9', '1', '8', '8', '8', '9', '/', '1', '8', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '0', '5', '7', '1', '0', '9', '1', '8', '1', '7', '/', '1', '8', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0263460Acc00600 : List (String × SourceJson) := (fragment0263460Field005Key00, fragment0263460Field005Value00) :: fragment0263460Acc00500
noncomputable def fragment0263460Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '2', '1', '9', '4', '2', '1', '5', '0', '3', '/', '8', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '9', '6', '9', '8', '0', '2', '3', '6', '1', '/', '6', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '1', '9', '1', '0', '3', '7', '5', '2', '7', '/', '1', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '4', '3', '0', '1', '1', '9', '6', '3', '1', '1', '/', '6', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '4', '4', '2', '9', '9', '6', '0', '8', '6', '7', '/', '1', '8', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '7', '0', '0', '6', '9', '9', '4', '1', '5', '3', '/', '9', '1', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '6', '6', '2', '5', '5', '2', '3', '6', '5', '7', '/', '9', '1', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '0', '1', '5', '1', '1', '0', '7', '2', '0', '9', '/', '1', '8', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '1', '4', '6', '0', '9', '1', '8', '8', '8', '9', '/', '1', '8', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '0', '5', '7', '1', '0', '9', '1', '8', '1', '7', '/', '1', '8', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0263460_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0263460Field005Chars00 ++ tail)) fragment0263460Acc00500 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0263460Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263460_object_field_005"
  err.flush

noncomputable def fragment0263460Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0263460Field006Value00 : SourceJson := .str (String.ofList ['9', '7', '9', '7', '9', '0', '2', '1', '2', '6', '4', '4', '0', '2', '9', '3', '9', '1', '1', '5', '2', '6', '7', '2', '3', '0', '6', '8', '4', '0', '8', '9', '5', '8', '6', '3', '8', '4', '3', '3', '0', '8', '8', '0', '0', '0', '0', '0', '/', '5', '0', '9', '4', '2', '8', '6', '1', '9', '3', '3', '0', '5', '2', '4', '6', '8', '6', '9', '1', '2', '1', '5', '0', '8', '1', '4', '0', '9', '7', '8', '8', '3', '0', '2', '9', '6', '9', '6', '6', '0', '1', '5', '7', '4', '2', '8', '6', '9', '8', '9', '3', '5', '1', '9', '2', '6', '7', '7'])
noncomputable def fragment0263460Acc00700 : List (String × SourceJson) := (fragment0263460Field006Key00, fragment0263460Field006Value00) :: fragment0263460Acc00600
noncomputable def fragment0263460Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '7', '9', '7', '9', '0', '2', '1', '2', '6', '4', '4', '0', '2', '9', '3', '9', '1', '1', '5', '2', '6', '7', '2', '3', '0', '6', '8', '4', '0', '8', '9', '5', '8', '6', '3', '8', '4', '3', '3', '0', '8', '8', '0', '0', '0', '0', '0', '/', '5', '0', '9', '4', '2', '8', '6', '1', '9', '3', '3', '0', '5', '2', '4', '6', '8', '6', '9', '1', '2', '1', '5', '0', '8', '1', '4', '0', '9', '7', '8', '8', '3', '0', '2', '9', '6', '9', '6', '6', '0', '1', '5', '7', '4', '2', '8', '6', '9', '8', '9', '3', '5', '1', '9', '2', '6', '7', '7', '"', ',']

theorem object_fragment0263460_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0263460Field006Chars00 ++ tail)) fragment0263460Acc00600 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0263460Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263460_object_field_006"
  err.flush

noncomputable def fragment0263460Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0263460Field007Value00 : SourceJson := .str (String.ofList ['1', '5', '9', '1', '4', '4', '9', '2', '0', '3', '4', '3', '8', '8', '0', '5', '4', '1', '8', '2', '0', '2', '3', '7', '6', '7', '7', '5', '4', '8', '7', '6', '0', '8', '2', '0', '7', '1', '3', '7', '5', '6', '1', '9', '4', '8', '1', '2', '4', '2', '2', '5', '8', '1', '8', '1', '0', '5', '7', '6', '3', '6', '6', '3', '2', '3', '5', '8', '5', '3', '4', '4', '0', '5', '0', '1', '4', '1', '5', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '9', '5', '3', '5', '9', '9', '4', '8', '6', '1', '8', '3', '0', '7', '8', '7', '0', '8', '9', '8', '4', '9', '1', '4', '1', '0', '8', '8', '7', '8', '7', '2', '8', '3', '9', '2', '8', '6', '3', '4', '5', '2', '3', '2', '8', '5', '0', '5', '0', '2', '3', '2', '4', '4', '0', '9', '6', '2', '2', '6', '3', '2', '5', '8', '0', '8', '2', '4', '8', '6', '9', '9', '0', '8', '3', '8', '3', '2', '7', '0', '0', '8', '2', '4', '1', '8', '3', '3', '9', '8', '8', '1', '7', '3', '5', '1', '4', '7', '1', '4', '8', '2', '6', '9', '2', '0', '2', '5', '2', '0', '6', '0', '3'])
noncomputable def fragment0263460Acc00800 : List (String × SourceJson) := (fragment0263460Field007Key00, fragment0263460Field007Value00) :: fragment0263460Acc00700
noncomputable def fragment0263460Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '9', '1', '4', '4', '9', '2', '0', '3', '4', '3', '8', '8', '0', '5', '4', '1', '8', '2', '0', '2', '3', '7', '6', '7', '7', '5', '4', '8', '7', '6', '0', '8', '2', '0', '7', '1', '3', '7', '5', '6', '1', '9', '4', '8', '1', '2', '4', '2', '2', '5', '8', '1', '8', '1', '0', '5', '7', '6', '3', '6', '6', '3', '2', '3', '5', '8', '5', '3', '4', '4', '0', '5', '0', '1', '4', '1', '5', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '9', '5', '3', '5', '9', '9', '4', '8', '6', '1', '8', '3', '0', '7', '8', '7', '0', '8', '9', '8', '4', '9', '1', '4', '1', '0', '8', '8', '7', '8', '7', '2', '8', '3', '9', '2', '8', '6', '3', '4', '5', '2', '3', '2', '8', '5', '0', '5', '0', '2', '3', '2', '4', '4', '0', '9', '6', '2', '2', '6', '3', '2', '5', '8', '0', '8', '2', '4', '8', '6', '9', '9', '0', '8', '3', '8', '3', '2', '7', '0', '0', '8', '2', '4', '1', '8', '3', '3', '9', '8', '8', '1', '7', '3', '5', '1', '4', '7', '1', '4', '8', '2', '6', '9', '2', '0', '2', '5', '2', '0', '6', '0', '3', '"', ',']

theorem object_fragment0263460_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0263460Field007Chars00 ++ tail)) fragment0263460Acc00700 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0263460Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263460_object_field_007"
  err.flush

noncomputable def fragment0263460Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0263460Field008Value00 : SourceJson := .str (String.ofList ['1', '5', '2', '3', '8', '0', '4', '8', '1', '2', '9', '1', '4', '9', '4', '2', '7', '0', '6'])
noncomputable def fragment0263460Acc00900 : List (String × SourceJson) := (fragment0263460Field008Key00, fragment0263460Field008Value00) :: fragment0263460Acc00800
noncomputable def fragment0263460Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '2', '3', '8', '0', '4', '8', '1', '2', '9', '1', '4', '9', '4', '2', '7', '0', '6', '"', ',']

theorem object_fragment0263460_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0263460Field008Chars00 ++ tail)) fragment0263460Acc00800 =
      SourceJson.object (fuel + 222) (SourceJson.white tail) fragment0263460Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263460_object_field_008"
  err.flush

noncomputable def fragment0263460Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0263460Field009Value00 : SourceJson := .str (String.ofList ['1', '1', '5', '1', '1', '0', '6', '5', '0', '4', '1', '4', '3', '1', '6', '9', '4', '0', '1', '3'])
noncomputable def fragment0263460Acc01000 : List (String × SourceJson) := (fragment0263460Field009Key00, fragment0263460Field009Value00) :: fragment0263460Acc00900
noncomputable def fragment0263460Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '5', '1', '1', '0', '6', '5', '0', '4', '1', '4', '3', '1', '6', '9', '4', '0', '1', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0263460_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment0263460Field009Chars00 ++ tail)) fragment0263460Acc00900 =
      .ok (.obj (fragment0263460Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263460_object_field_009"
  err.flush

noncomputable def fragment0263460Chars : List Char := '{' :: (fragment0263460Field000Chars00 ++ fragment0263460Field001Chars00 ++ fragment0263460Field002Chars00 ++ fragment0263460Field003Chars00 ++ fragment0263460Field004Chars00 ++ fragment0263460Field005Chars00 ++ fragment0263460Field006Chars00 ++ fragment0263460Field007Chars00 ++ fragment0263460Field008Chars00 ++ fragment0263460Field009Chars00)
noncomputable def fragment0263460Value : SourceJson := .obj (fragment0263460Acc01000.reverse)

theorem value_fragment0263460 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 232) (fragment0263460Chars ++ tail) =
      .ok (fragment0263460Value, tail) := by
  have hinput : fragment0263460Chars ++ tail = '{' :: (fragment0263460Field000Chars00 ++ (fragment0263460Field001Chars00 ++ (fragment0263460Field002Chars00 ++ (fragment0263460Field003Chars00 ++ (fragment0263460Field004Chars00 ++ (fragment0263460Field005Chars00 ++ (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0263460Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 232) (fragment0263460Chars ++ tail) =
        SourceJson.value (fuel + 232) ('{' :: (fragment0263460Field000Chars00 ++ (fragment0263460Field001Chars00 ++ (fragment0263460Field002Chars00 ++ (fragment0263460Field003Chars00 ++ (fragment0263460Field004Chars00 ++ (fragment0263460Field005Chars00 ++ (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 232)) hinput
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0263460Field000Chars00 ++ (fragment0263460Field001Chars00 ++ (fragment0263460Field002Chars00 ++ (fragment0263460Field003Chars00 ++ (fragment0263460Field004Chars00 ++ (fragment0263460Field005Chars00 ++ (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail)))))))))))) fragment0263460Acc00000 := by rfl
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0263460Field001Chars00 ++ (fragment0263460Field002Chars00 ++ (fragment0263460Field003Chars00 ++ (fragment0263460Field004Chars00 ++ (fragment0263460Field005Chars00 ++ (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail))))))))))) fragment0263460Acc00100 := object_fragment0263460_field_000 fuel (fragment0263460Field001Chars00 ++ (fragment0263460Field002Chars00 ++ (fragment0263460Field003Chars00 ++ (fragment0263460Field004Chars00 ++ (fragment0263460Field005Chars00 ++ (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0263460Field002Chars00 ++ (fragment0263460Field003Chars00 ++ (fragment0263460Field004Chars00 ++ (fragment0263460Field005Chars00 ++ (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail)))))))))) fragment0263460Acc00200 := object_fragment0263460_field_001 fuel (fragment0263460Field002Chars00 ++ (fragment0263460Field003Chars00 ++ (fragment0263460Field004Chars00 ++ (fragment0263460Field005Chars00 ++ (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0263460Field003Chars00 ++ (fragment0263460Field004Chars00 ++ (fragment0263460Field005Chars00 ++ (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail))))))))) fragment0263460Acc00300 := object_fragment0263460_field_002 fuel (fragment0263460Field003Chars00 ++ (fragment0263460Field004Chars00 ++ (fragment0263460Field005Chars00 ++ (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0263460Field004Chars00 ++ (fragment0263460Field005Chars00 ++ (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail)))))))) fragment0263460Acc00400 := object_fragment0263460_field_003 fuel (fragment0263460Field004Chars00 ++ (fragment0263460Field005Chars00 ++ (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0263460Field005Chars00 ++ (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail))))))) fragment0263460Acc00500 := object_fragment0263460_field_004 fuel (fragment0263460Field005Chars00 ++ (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail)))))) fragment0263460Acc00600 := object_fragment0263460_field_005 fuel (fragment0263460Field006Chars00 ++ (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail))))) fragment0263460Acc00700 := object_fragment0263460_field_006 fuel (fragment0263460Field007Chars00 ++ (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail)))) fragment0263460Acc00800 := object_fragment0263460_field_007 fuel (fragment0263460Field008Chars00 ++ (fragment0263460Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment0263460Field009Chars00 ++ (tail))) fragment0263460Acc00900 := object_fragment0263460_field_008 fuel (fragment0263460Field009Chars00 ++ (tail))
    _ = .ok (fragment0263460Value, tail) := object_fragment0263460_field_009 fuel (tail)

noncomputable def fragment0265036Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0265036Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0265036Field000Value00 : SourceJson := .number (String.ofList ['2', '3'])
noncomputable def fragment0265036Acc00100 : List (String × SourceJson) := (fragment0265036Field000Key00, fragment0265036Field000Value00) :: fragment0265036Acc00000
noncomputable def fragment0265036Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '3', ',']

theorem object_fragment0265036_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 205) (SourceJson.white (fragment0265036Field000Chars00 ++ tail)) fragment0265036Acc00000 =
      SourceJson.object (fuel + 204) (SourceJson.white tail) fragment0265036Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0265036_object_field_000"
  err.flush

noncomputable def fragment0265036Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0265036Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0265036Acc00200 : List (String × SourceJson) := (fragment0265036Field001Key00, fragment0265036Field001Value00) :: fragment0265036Acc00100
noncomputable def fragment0265036Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0265036_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0265036Field001Chars00 ++ tail)) fragment0265036Acc00100 =
      SourceJson.object (fuel + 203) (SourceJson.white tail) fragment0265036Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0265036_object_field_001"
  err.flush

noncomputable def fragment0265036Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0265036Field002Value00 : SourceJson := .str (String.ofList ['4', '8', '1', '9', '2', '2', '4', '5', '6', '9', '5', '6', '0', '3', '8', '4', '6', '3', '0', '0', '8', '3', '0', '7', '9', '8', '3', '0', '1', '1', '0', '8', '4', '5', '0', '4', '3', '5', '8', '0', '1', '/', '8', '3', '2', '3', '5', '9', '6', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0265036Acc00300 : List (String × SourceJson) := (fragment0265036Field002Key00, fragment0265036Field002Value00) :: fragment0265036Acc00200
noncomputable def fragment0265036Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '8', '1', '9', '2', '2', '4', '5', '6', '9', '5', '6', '0', '3', '8', '4', '6', '3', '0', '0', '8', '3', '0', '7', '9', '8', '3', '0', '1', '1', '0', '8', '4', '5', '0', '4', '3', '5', '8', '0', '1', '/', '8', '3', '2', '3', '5', '9', '6', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0265036_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0265036Field002Chars00 ++ tail)) fragment0265036Acc00200 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0265036Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0265036_object_field_002"
  err.flush

noncomputable def fragment0265036Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0265036Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0265036Acc00400 : List (String × SourceJson) := (fragment0265036Field003Key00, fragment0265036Field003Value00) :: fragment0265036Acc00300
noncomputable def fragment0265036Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0265036_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0265036Field003Chars00 ++ tail)) fragment0265036Acc00300 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0265036Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0265036_object_field_003"
  err.flush

noncomputable def fragment0265036Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0265036Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0265036Acc00500 : List (String × SourceJson) := (fragment0265036Field004Key00, fragment0265036Field004Value00) :: fragment0265036Acc00400
noncomputable def fragment0265036Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0265036_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0265036Field004Chars00 ++ tail)) fragment0265036Acc00400 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0265036Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0265036_object_field_004"
  err.flush

noncomputable def fragment0265036Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0265036Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '7', '7', '4', '1', '9', '9', '4', '5', '1', '/', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '9', '1', '4', '3', '0', '7', '8', '3', '7', '/', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '4', '3', '4', '4', '8', '5', '2', '7', '/', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '8', '4', '5', '1', '7', '5', '9', '6', '1', '/', '1', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '4', '9', '7', '1', '3', '6', '2', '9', '3', '/', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '7', '2', '3', '9', '0', '3', '0', '9', '/', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '4', '2', '1', '8', '7', '2', '6', '1', '/', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '7', '2', '2', '3', '5', '5', '8', '7', '1', '/', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '1', '4', '4', '8', '6', '9', '3', '1', '1', '/', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '0', '3', '7', '4', '8', '3', '9', '4', '9', '/', '1', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0265036Acc00600 : List (String × SourceJson) := (fragment0265036Field005Key00, fragment0265036Field005Value00) :: fragment0265036Acc00500
noncomputable def fragment0265036Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '7', '4', '1', '9', '9', '4', '5', '1', '/', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '9', '1', '4', '3', '0', '7', '8', '3', '7', '/', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '4', '3', '4', '4', '8', '5', '2', '7', '/', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '8', '4', '5', '1', '7', '5', '9', '6', '1', '/', '1', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '4', '9', '7', '1', '3', '6', '2', '9', '3', '/', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '7', '2', '3', '9', '0', '3', '0', '9', '/', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '4', '2', '1', '8', '7', '2', '6', '1', '/', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '2', '2', '3', '5', '5', '8', '7', '1', '/', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '4', '4', '8', '6', '9', '3', '1', '1', '/', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '0', '3', '7', '4', '8', '3', '9', '4', '9', '/', '1', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0265036_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0265036Field005Chars00 ++ tail)) fragment0265036Acc00500 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0265036Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0265036_object_field_005"
  err.flush

noncomputable def fragment0265036Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0265036Field006Value00 : SourceJson := .str (String.ofList ['3', '1', '0', '5', '5', '8', '6', '6', '2', '5', '0', '2', '3', '9', '6', '7', '2', '1', '1', '8', '7', '5', '7', '7', '5', '4', '9', '2', '5', '7', '0', '6', '6', '7', '8', '4', '7', '3', '1', '4', '9', '7', '4', '6', '1', '6', '6', '2', '5', '0', '0', '/', '1', '0', '4', '4', '9', '8', '8', '4', '5', '5', '1', '3', '8', '8', '6', '6', '7', '6', '9', '8', '7', '9', '1', '9', '3', '1', '3', '2', '6', '1', '7', '6', '8', '3', '7', '4', '7', '4', '4', '6', '2', '7', '1', '6', '9', '8', '1', '1', '1', '5', '4', '1', '0', '8', '1', '4', '7', '4', '5', '8', '5', '9'])
noncomputable def fragment0265036Acc00700 : List (String × SourceJson) := (fragment0265036Field006Key00, fragment0265036Field006Value00) :: fragment0265036Acc00600
noncomputable def fragment0265036Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '1', '0', '5', '5', '8', '6', '6', '2', '5', '0', '2', '3', '9', '6', '7', '2', '1', '1', '8', '7', '5', '7', '7', '5', '4', '9', '2', '5', '7', '0', '6', '6', '7', '8', '4', '7', '3', '1', '4', '9', '7', '4', '6', '1', '6', '6', '2', '5', '0', '0', '/', '1', '0', '4', '4', '9', '8', '8', '4', '5', '5', '1', '3', '8', '8', '6', '6', '7', '6', '9', '8', '7', '9', '1', '9', '3', '1', '3', '2', '6', '1', '7', '6', '8', '3', '7', '4', '7', '4', '4', '6', '2', '7', '1', '6', '9', '8', '1', '1', '1', '5', '4', '1', '0', '8', '1', '4', '7', '4', '5', '8', '5', '9', '"', ',']

theorem object_fragment0265036_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0265036Field006Chars00 ++ tail)) fragment0265036Acc00600 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0265036Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0265036_object_field_006"
  err.flush

noncomputable def fragment0265036Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0265036Field007Value00 : SourceJson := .str (String.ofList ['8', '5', '4', '8', '8', '5', '3', '5', '5', '6', '7', '1', '3', '4', '7', '9', '5', '0', '1', '7', '9', '3', '0', '1', '6', '0', '8', '1', '4', '3', '7', '8', '8', '2', '2', '5', '7', '4', '0', '2', '8', '8', '2', '7', '7', '1', '6', '8', '7', '6', '0', '7', '4', '7', '9', '1', '7', '9', '5', '0', '5', '0', '7', '2', '8', '6', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '3', '7', '7', '8', '2', '0', '4', '9', '7', '3', '7', '6', '7', '4', '5', '7', '5', '0', '3', '5', '6', '8', '1', '0', '6', '4', '3', '8', '1', '8', '4', '7', '6', '1', '4', '0', '2', '0', '0', '6', '3', '3', '1', '2', '8', '0', '8', '5', '8', '0', '9', '9', '7', '9', '4', '7', '2', '3', '8', '2', '1', '1', '6', '5', '9', '5', '9', '8', '0', '4', '6', '8', '5', '0', '4', '7', '6', '7', '2', '9', '0', '2', '9', '2', '7', '5', '4', '8', '1', '8', '3', '2', '6', '5', '6', '6', '8', '9', '3', '7'])
noncomputable def fragment0265036Acc00800 : List (String × SourceJson) := (fragment0265036Field007Key00, fragment0265036Field007Value00) :: fragment0265036Acc00700
noncomputable def fragment0265036Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '5', '4', '8', '8', '5', '3', '5', '5', '6', '7', '1', '3', '4', '7', '9', '5', '0', '1', '7', '9', '3', '0', '1', '6', '0', '8', '1', '4', '3', '7', '8', '8', '2', '2', '5', '7', '4', '0', '2', '8', '8', '2', '7', '7', '1', '6', '8', '7', '6', '0', '7', '4', '7', '9', '1', '7', '9', '5', '0', '5', '0', '7', '2', '8', '6', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '3', '7', '7', '8', '2', '0', '4', '9', '7', '3', '7', '6', '7', '4', '5', '7', '5', '0', '3', '5', '6', '8', '1', '0', '6', '4', '3', '8', '1', '8', '4', '7', '6', '1', '4', '0', '2', '0', '0', '6', '3', '3', '1', '2', '8', '0', '8', '5', '8', '0', '9', '9', '7', '9', '4', '7', '2', '3', '8', '2', '1', '1', '6', '5', '9', '5', '9', '8', '0', '4', '6', '8', '5', '0', '4', '7', '6', '7', '2', '9', '0', '2', '9', '2', '7', '5', '4', '8', '1', '8', '3', '2', '6', '5', '6', '6', '8', '9', '3', '7', '"', ',']

theorem object_fragment0265036_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0265036Field007Chars00 ++ tail)) fragment0265036Acc00700 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0265036Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0265036_object_field_007"
  err.flush

noncomputable def fragment0265036Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0265036Field008Value00 : SourceJson := .str (String.ofList ['2', '3', '5', '4', '5', '7', '0', '7', '1', '9', '1', '2', '6', '5', '3', '2', '4', '9', '0'])
noncomputable def fragment0265036Acc00900 : List (String × SourceJson) := (fragment0265036Field008Key00, fragment0265036Field008Value00) :: fragment0265036Acc00800
noncomputable def fragment0265036Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '5', '4', '5', '7', '0', '7', '1', '9', '1', '2', '6', '5', '3', '2', '4', '9', '0', '"', ',']

theorem object_fragment0265036_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0265036Field008Chars00 ++ tail)) fragment0265036Acc00800 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0265036Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0265036_object_field_008"
  err.flush

noncomputable def fragment0265036Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0265036Field009Value00 : SourceJson := .str (String.ofList ['1', '8', '6', '1', '8', '7', '6', '1', '3', '6', '7', '2', '6', '7', '2', '8', '8', '5', '3', '8'])
noncomputable def fragment0265036Acc01000 : List (String × SourceJson) := (fragment0265036Field009Key00, fragment0265036Field009Value00) :: fragment0265036Acc00900
noncomputable def fragment0265036Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '6', '1', '8', '7', '6', '1', '3', '6', '7', '2', '6', '7', '2', '8', '8', '5', '3', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0265036_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0265036Field009Chars00 ++ tail)) fragment0265036Acc00900 =
      .ok (.obj (fragment0265036Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0265036_object_field_009"
  err.flush

noncomputable def fragment0265036Chars : List Char := '{' :: (fragment0265036Field000Chars00 ++ fragment0265036Field001Chars00 ++ fragment0265036Field002Chars00 ++ fragment0265036Field003Chars00 ++ fragment0265036Field004Chars00 ++ fragment0265036Field005Chars00 ++ fragment0265036Field006Chars00 ++ fragment0265036Field007Chars00 ++ fragment0265036Field008Chars00 ++ fragment0265036Field009Chars00)
noncomputable def fragment0265036Value : SourceJson := .obj (fragment0265036Acc01000.reverse)

theorem value_fragment0265036 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 206) (fragment0265036Chars ++ tail) =
      .ok (fragment0265036Value, tail) := by
  have hinput : fragment0265036Chars ++ tail = '{' :: (fragment0265036Field000Chars00 ++ (fragment0265036Field001Chars00 ++ (fragment0265036Field002Chars00 ++ (fragment0265036Field003Chars00 ++ (fragment0265036Field004Chars00 ++ (fragment0265036Field005Chars00 ++ (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0265036Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 206) (fragment0265036Chars ++ tail) =
        SourceJson.value (fuel + 206) ('{' :: (fragment0265036Field000Chars00 ++ (fragment0265036Field001Chars00 ++ (fragment0265036Field002Chars00 ++ (fragment0265036Field003Chars00 ++ (fragment0265036Field004Chars00 ++ (fragment0265036Field005Chars00 ++ (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 206)) hinput
    _ = SourceJson.object (fuel + 205) (SourceJson.white (fragment0265036Field000Chars00 ++ (fragment0265036Field001Chars00 ++ (fragment0265036Field002Chars00 ++ (fragment0265036Field003Chars00 ++ (fragment0265036Field004Chars00 ++ (fragment0265036Field005Chars00 ++ (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail)))))))))))) fragment0265036Acc00000 := by rfl
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0265036Field001Chars00 ++ (fragment0265036Field002Chars00 ++ (fragment0265036Field003Chars00 ++ (fragment0265036Field004Chars00 ++ (fragment0265036Field005Chars00 ++ (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail))))))))))) fragment0265036Acc00100 := object_fragment0265036_field_000 fuel (fragment0265036Field001Chars00 ++ (fragment0265036Field002Chars00 ++ (fragment0265036Field003Chars00 ++ (fragment0265036Field004Chars00 ++ (fragment0265036Field005Chars00 ++ (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0265036Field002Chars00 ++ (fragment0265036Field003Chars00 ++ (fragment0265036Field004Chars00 ++ (fragment0265036Field005Chars00 ++ (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail)))))))))) fragment0265036Acc00200 := object_fragment0265036_field_001 fuel (fragment0265036Field002Chars00 ++ (fragment0265036Field003Chars00 ++ (fragment0265036Field004Chars00 ++ (fragment0265036Field005Chars00 ++ (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0265036Field003Chars00 ++ (fragment0265036Field004Chars00 ++ (fragment0265036Field005Chars00 ++ (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail))))))))) fragment0265036Acc00300 := object_fragment0265036_field_002 fuel (fragment0265036Field003Chars00 ++ (fragment0265036Field004Chars00 ++ (fragment0265036Field005Chars00 ++ (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0265036Field004Chars00 ++ (fragment0265036Field005Chars00 ++ (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail)))))))) fragment0265036Acc00400 := object_fragment0265036_field_003 fuel (fragment0265036Field004Chars00 ++ (fragment0265036Field005Chars00 ++ (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0265036Field005Chars00 ++ (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail))))))) fragment0265036Acc00500 := object_fragment0265036_field_004 fuel (fragment0265036Field005Chars00 ++ (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail)))))) fragment0265036Acc00600 := object_fragment0265036_field_005 fuel (fragment0265036Field006Chars00 ++ (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail))))) fragment0265036Acc00700 := object_fragment0265036_field_006 fuel (fragment0265036Field007Chars00 ++ (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail)))) fragment0265036Acc00800 := object_fragment0265036_field_007 fuel (fragment0265036Field008Chars00 ++ (fragment0265036Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0265036Field009Chars00 ++ (tail))) fragment0265036Acc00900 := object_fragment0265036_field_008 fuel (fragment0265036Field009Chars00 ++ (tail))
    _ = .ok (fragment0265036Value, tail) := object_fragment0265036_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0022_before_reader"
  err.flush

noncomputable def chunk0022LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0022SuffixChars00 : List Char := [',']
noncomputable def chunk0022Chars00 : List Char := chunk0022LeadChars00 ++ fragment0263460Chars ++ chunk0022SuffixChars00
noncomputable def chunk0022Push00 (acc : List SourceJson) : List SourceJson := fragment0263460Value :: acc

noncomputable def chunk0022AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0022_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 582)
      (SourceJson.white (chunk0022LeadChars00 ++ (fragment0263460Chars ++ rest))) acc =
      (SourceJson.value (fuel + 581) (fragment0263460Chars ++ rest)).bind
        (chunk0022AfterValue00 (fuel + 581) acc) := by rfl

theorem array_chunk0022 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 582) (SourceJson.white (chunk0022Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 581) (SourceJson.white tail) (chunk0022Push00 acc) := by
  have hinput : chunk0022Chars00 ++ tail = chunk0022LeadChars00 ++ (fragment0263460Chars ++ (chunk0022SuffixChars00 ++ tail)) := by
    simp only [chunk0022Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 582) (SourceJson.white (chunk0022Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 582)
          (SourceJson.white (chunk0022LeadChars00 ++ (fragment0263460Chars ++ (chunk0022SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 582) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 581) (fragment0263460Chars ++ (chunk0022SuffixChars00 ++ tail))).bind
        (chunk0022AfterValue00 (fuel + 581) acc) := array_chunk0022_head fuel (chunk0022SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0263460Value, chunk0022SuffixChars00 ++ tail)).bind
        (chunk0022AfterValue00 (fuel + 581) acc) :=
      congrArg (fun result => result.bind (chunk0022AfterValue00 (fuel + 581) acc))
        (value_fragment0263460 (fuel + 349) (chunk0022SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 581) (SourceJson.white tail) (chunk0022Push00 acc) := by rfl

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
noncomputable def chunk0023Chars00 : List Char := chunk0023LeadChars00 ++ fragment0265036Chars ++ chunk0023SuffixChars00
noncomputable def chunk0023Push00 (acc : List SourceJson) : List SourceJson := fragment0265036Value :: acc

noncomputable def chunk0023AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0023_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 581)
      (SourceJson.white (chunk0023LeadChars00 ++ (fragment0265036Chars ++ rest))) acc =
      (SourceJson.value (fuel + 580) (fragment0265036Chars ++ rest)).bind
        (chunk0023AfterValue00 (fuel + 580) acc) := by rfl

theorem array_chunk0023 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 581) (SourceJson.white (chunk0023Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 580) (SourceJson.white tail) (chunk0023Push00 acc) := by
  have hinput : chunk0023Chars00 ++ tail = chunk0023LeadChars00 ++ (fragment0265036Chars ++ (chunk0023SuffixChars00 ++ tail)) := by
    simp only [chunk0023Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 581) (SourceJson.white (chunk0023Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 581)
          (SourceJson.white (chunk0023LeadChars00 ++ (fragment0265036Chars ++ (chunk0023SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 581) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 580) (fragment0265036Chars ++ (chunk0023SuffixChars00 ++ tail))).bind
        (chunk0023AfterValue00 (fuel + 580) acc) := array_chunk0023_head fuel (chunk0023SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0265036Value, chunk0023SuffixChars00 ++ tail)).bind
        (chunk0023AfterValue00 (fuel + 580) acc) :=
      congrArg (fun result => result.bind (chunk0023AfterValue00 (fuel + 580) acc))
        (value_fragment0265036 (fuel + 374) (chunk0023SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 580) (SourceJson.white tail) (chunk0023Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0023_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0022Chars00 ++ chunk0023Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0023Push00 (chunk0022Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 582) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 580) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 582) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 582) (SourceJson.white (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 582) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 581) (SourceJson.white (chunk0023Chars00 ++ (tail))) (chunk0022Push00 (acc)) := array_chunk0022 fuel (chunk0023Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 580) (SourceJson.white tail) (blockPush acc) := array_chunk0023 fuel (tail) (chunk0022Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 263454).take 3112 = blockChars := by rfl

theorem block_original_split : sourceRest 263454 = blockChars ++ sourceRest 266566 := by
  calc
    sourceRest 263454 = (sourceRest 263454).take 3112 ++ (sourceRest 263454).drop 3112 :=
      (List.take_append_drop 3112 (sourceRest 263454)).symm
    _ = blockChars ++ (sourceRest 263454).drop 3112 :=
      congrArg (fun part => part ++ (sourceRest 263454).drop 3112) block_original_prefix
    _ = blockChars ++ sourceRest 266566 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 263454 3112)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 582) (SourceJson.white (sourceRest 263454)) acc =
      SourceJson.array (fuel + 580) (SourceJson.white (sourceRest 266566)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 582) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 266566) acc)

#print axioms object_fragment0263460_field_000
#print axioms object_fragment0263460_field_001
#print axioms object_fragment0263460_field_002
#print axioms object_fragment0263460_field_003
#print axioms object_fragment0263460_field_004
#print axioms object_fragment0263460_field_005
#print axioms object_fragment0263460_field_006
#print axioms object_fragment0263460_field_007
#print axioms object_fragment0263460_field_008
#print axioms object_fragment0263460_field_009
#print axioms value_fragment0263460
#print axioms object_fragment0265036_field_000
#print axioms object_fragment0265036_field_001
#print axioms object_fragment0265036_field_002
#print axioms object_fragment0265036_field_003
#print axioms object_fragment0265036_field_004
#print axioms object_fragment0265036_field_005
#print axioms object_fragment0265036_field_006
#print axioms object_fragment0265036_field_007
#print axioms object_fragment0265036_field_008
#print axioms object_fragment0265036_field_009
#print axioms value_fragment0265036
#print axioms array_chunk0022_head
#print axioms array_chunk0022
#print axioms array_chunk0023_head
#print axioms array_chunk0023
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock011

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
