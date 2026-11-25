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

namespace SimplicesBlock036

noncomputable def fragment0346760Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0346760Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0346760Field000Value00 : SourceJson := .number (String.ofList ['7', '1'])
noncomputable def fragment0346760Acc00100 : List (String × SourceJson) := (fragment0346760Field000Key00, fragment0346760Field000Value00) :: fragment0346760Acc00000
noncomputable def fragment0346760Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '1', ',']

theorem object_fragment0346760_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0346760Field000Chars00 ++ tail)) fragment0346760Acc00000 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0346760Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0346760_object_field_000"
  err.flush

noncomputable def fragment0346760Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0346760Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '4'])]
noncomputable def fragment0346760Acc00200 : List (String × SourceJson) := (fragment0346760Field001Key00, fragment0346760Field001Value00) :: fragment0346760Acc00100
noncomputable def fragment0346760Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0346760_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0346760Field001Chars00 ++ tail)) fragment0346760Acc00100 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0346760Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0346760_object_field_001"
  err.flush

noncomputable def fragment0346760Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0346760Field002Value00 : SourceJson := .str (String.ofList ['2', '5', '3', '7', '3', '1', '9', '1', '6', '8', '9', '0', '4', '5', '3', '9', '1', '0', '7', '4', '5', '8', '6', '0', '5', '9', '1', '0', '3', '1', '0', '0', '2', '7', '9', '5', '5', '7', '1', '7', '8', '3', '8', '7', '/', '1', '6', '4', '5', '8', '9', '0', '2', '5', '3', '5', '8', '3', '8', '6', '2', '9', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0346760Acc00300 : List (String × SourceJson) := (fragment0346760Field002Key00, fragment0346760Field002Value00) :: fragment0346760Acc00200
noncomputable def fragment0346760Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '5', '3', '7', '3', '1', '9', '1', '6', '8', '9', '0', '4', '5', '3', '9', '1', '0', '7', '4', '5', '8', '6', '0', '5', '9', '1', '0', '3', '1', '0', '0', '2', '7', '9', '5', '5', '7', '1', '7', '8', '3', '8', '7', '/', '1', '6', '4', '5', '8', '9', '0', '2', '5', '3', '5', '8', '3', '8', '6', '2', '9', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0346760_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0346760Field002Chars00 ++ tail)) fragment0346760Acc00200 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0346760Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0346760_object_field_002"
  err.flush

noncomputable def fragment0346760Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0346760Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0346760Acc00400 : List (String × SourceJson) := (fragment0346760Field003Key00, fragment0346760Field003Value00) :: fragment0346760Acc00300
noncomputable def fragment0346760Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0346760_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0346760Field003Chars00 ++ tail)) fragment0346760Acc00300 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0346760Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0346760_object_field_003"
  err.flush

noncomputable def fragment0346760Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0346760Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '3', '1', '/', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0346760Acc00500 : List (String × SourceJson) := (fragment0346760Field004Key00, fragment0346760Field004Value00) :: fragment0346760Acc00400
noncomputable def fragment0346760Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '3', '1', '/', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0346760_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0346760Field004Chars00 ++ tail)) fragment0346760Acc00400 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0346760Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0346760_object_field_004"
  err.flush

noncomputable def fragment0346760Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0346760Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '5', '9', '9', '4', '0', '5', '3', '2', '8', '9', '3', '/', '2', '3', '7', '6', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '2', '3', '0', '5', '3', '6', '5', '6', '9', '/', '1', '1', '8', '8', '4', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '3', '1', '3', '4', '2', '5', '2', '9', '9', '/', '1', '7', '8', '2', '6', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '3', '7', '6', '8', '4', '0', '1', '9', '9', '7', '/', '1', '1', '0', '9', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '0', '6', '0', '8', '7', '4', '8', '4', '6', '1', '7', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '0', '7', '6', '2', '0', '1', '8', '9', '4', '9', '/', '7', '1', '3', '0', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '0', '9', '2', '9', '8', '4', '6', '1', '2', '9', '/', '5', '2', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '3', '4', '3', '6', '1', '2', '0', '3', '3', '4', '1', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '5', '3', '8', '4', '7', '4', '7', '8', '0', '7', '3', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '9', '1', '5', '6', '1', '2', '3', '8', '9', '5', '1', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0346760Acc00600 : List (String × SourceJson) := (fragment0346760Field005Key00, fragment0346760Field005Value00) :: fragment0346760Acc00500
noncomputable def fragment0346760Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '9', '4', '0', '5', '3', '2', '8', '9', '3', '/', '2', '3', '7', '6', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '2', '3', '0', '5', '3', '6', '5', '6', '9', '/', '1', '1', '8', '8', '4', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '3', '1', '3', '4', '2', '5', '2', '9', '9', '/', '1', '7', '8', '2', '6', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '3', '7', '6', '8', '4', '0', '1', '9', '9', '7', '/', '1', '1', '0', '9', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '0', '6', '0', '8', '7', '4', '8', '4', '6', '1', '7', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '0', '7', '6', '2', '0', '1', '8', '9', '4', '9', '/', '7', '1', '3', '0', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '0', '9', '2', '9', '8', '4', '6', '1', '2', '9', '/', '5', '2', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '3', '4', '3', '6', '1', '2', '0', '3', '3', '4', '1', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '5', '3', '8', '4', '7', '4', '7', '8', '0', '7', '3', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '9', '1', '5', '6', '1', '2', '3', '8', '9', '5', '1', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0346760_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0346760Field005Chars00 ++ tail)) fragment0346760Acc00500 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0346760Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0346760_object_field_005"
  err.flush

noncomputable def fragment0346760Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0346760Field006Value00 : SourceJson := .str (String.ofList ['2', '6', '1', '0', '1', '2', '5', '4', '4', '2', '6', '0', '5', '9', '0', '8', '1', '7', '7', '5', '2', '8', '5', '5', '8', '9', '1', '7', '0', '2', '5', '6', '2', '0', '8', '4', '7', '8', '8', '4', '0', '2', '6', '3', '1', '5', '0', '0', '9', '3', '/', '1', '2', '7', '9', '2', '1', '7', '2', '0', '9', '7', '3', '8', '0', '9', '2', '2', '7', '8', '9', '8', '8', '0', '6', '5', '6', '2', '2', '3', '6', '1', '0', '4', '9', '5', '9', '9', '3', '5', '3', '0', '7', '9', '2', '5', '1', '0', '6', '9', '0', '2', '0', '6', '0', '4', '5', '0', '3', '4', '9', '2', '4', '0', '4', '8'])
noncomputable def fragment0346760Acc00700 : List (String × SourceJson) := (fragment0346760Field006Key00, fragment0346760Field006Value00) :: fragment0346760Acc00600
noncomputable def fragment0346760Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '6', '1', '0', '1', '2', '5', '4', '4', '2', '6', '0', '5', '9', '0', '8', '1', '7', '7', '5', '2', '8', '5', '5', '8', '9', '1', '7', '0', '2', '5', '6', '2', '0', '8', '4', '7', '8', '8', '4', '0', '2', '6', '3', '1', '5', '0', '0', '9', '3', '/', '1', '2', '7', '9', '2', '1', '7', '2', '0', '9', '7', '3', '8', '0', '9', '2', '2', '7', '8', '9', '8', '8', '0', '6', '5', '6', '2', '2', '3', '6', '1', '0', '4', '9', '5', '9', '9', '3', '5', '3', '0', '7', '9', '2', '5', '1', '0', '6', '9', '0', '2', '0', '6', '0', '4', '5', '0', '3', '4', '9', '2', '4', '0', '4', '8', '"', ',']

theorem object_fragment0346760_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0346760Field006Chars00 ++ tail)) fragment0346760Acc00600 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0346760Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0346760_object_field_006"
  err.flush

noncomputable def fragment0346760Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0346760Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '1', '3', '8', '7', '9', '8', '3', '0', '1', '8', '8', '9', '2', '1', '5', '8', '1', '8', '7', '2', '8', '4', '0', '6', '6', '8', '8', '7', '4', '3', '4', '6', '7', '6', '9', '5', '8', '8', '8', '8', '4', '1', '8', '4', '5', '8', '6', '7', '1', '6', '7', '2', '7', '0', '2', '7', '3', '6', '9', '2', '1', '3', '8', '5', '7', '2', '4', '6', '0', '5', '6', '9', '6', '7', '1', '4', '0', '9', '4', '1', '5', '0', '5', '4', '3', '2', '1', '2', '8', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '6', '1', '0', '7', '5', '6', '9', '5', '6', '4', '1', '4', '1', '2', '9', '3', '6', '5', '8', '5', '6', '3', '2', '3', '4', '6', '1', '5', '4', '5', '9', '0', '8', '3', '2', '1', '4', '7', '0', '3', '8', '8', '8', '6', '7', '6', '3', '1', '9', '6', '4', '6', '3', '0', '7', '0', '8', '8', '6', '1', '8', '9', '0', '3', '7', '0', '9', '5', '4', '6', '2', '7', '7', '1', '0', '6', '3', '5', '1', '3', '6', '4', '1', '7', '9', '8', '3', '5', '4', '2', '5', '4', '2', '7', '1', '6', '1', '4', '0', '4', '4', '8', '3', '5', '3', '8', '4', '7', '3', '3', '2', '0', '5', '0', '6', '4', '3'])
noncomputable def fragment0346760Acc00800 : List (String × SourceJson) := (fragment0346760Field007Key00, fragment0346760Field007Value00) :: fragment0346760Acc00700
noncomputable def fragment0346760Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '1', '3', '8', '7', '9', '8', '3', '0', '1', '8', '8', '9', '2', '1', '5', '8', '1', '8', '7', '2', '8', '4', '0', '6', '6', '8', '8', '7', '4', '3', '4', '6', '7', '6', '9', '5', '8', '8', '8', '8', '4', '1', '8', '4', '5', '8', '6', '7', '1', '6', '7', '2', '7', '0', '2', '7', '3', '6', '9', '2', '1', '3', '8', '5', '7', '2', '4', '6', '0', '5', '6', '9', '6', '7', '1', '4', '0', '9', '4', '1', '5', '0', '5', '4', '3', '2', '1', '2', '8', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '6', '1', '0', '7', '5', '6', '9', '5', '6', '4', '1', '4', '1', '2', '9', '3', '6', '5', '8', '5', '6', '3', '2', '3', '4', '6', '1', '5', '4', '5', '9', '0', '8', '3', '2', '1', '4', '7', '0', '3', '8', '8', '8', '6', '7', '6', '3', '1', '9', '6', '4', '6', '3', '0', '7', '0', '8', '8', '6', '1', '8', '9', '0', '3', '7', '0', '9', '5', '4', '6', '2', '7', '7', '1', '0', '6', '3', '5', '1', '3', '6', '4', '1', '7', '9', '8', '3', '5', '4', '2', '5', '4', '2', '7', '1', '6', '1', '4', '0', '4', '4', '8', '3', '5', '3', '8', '4', '7', '3', '3', '2', '0', '5', '0', '6', '4', '3', '"', ',']

theorem object_fragment0346760_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0346760Field007Chars00 ++ tail)) fragment0346760Acc00700 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0346760Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0346760_object_field_007"
  err.flush

noncomputable def fragment0346760Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0346760Field008Value00 : SourceJson := .str (String.ofList ['1', '6', '1', '6', '5', '7', '8', '0', '2', '2', '6', '7', '7', '9', '1'])
noncomputable def fragment0346760Acc00900 : List (String × SourceJson) := (fragment0346760Field008Key00, fragment0346760Field008Value00) :: fragment0346760Acc00800
noncomputable def fragment0346760Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '1', '6', '5', '7', '8', '0', '2', '2', '6', '7', '7', '9', '1', '"', ',']

theorem object_fragment0346760_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0346760Field008Chars00 ++ tail)) fragment0346760Acc00800 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0346760Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0346760_object_field_008"
  err.flush

noncomputable def fragment0346760Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0346760Field009Value00 : SourceJson := .str (String.ofList ['9', '1', '8', '2', '4', '8', '7', '1', '4', '5', '1', '6', '4', '0', '8'])
noncomputable def fragment0346760Acc01000 : List (String × SourceJson) := (fragment0346760Field009Key00, fragment0346760Field009Value00) :: fragment0346760Acc00900
noncomputable def fragment0346760Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '1', '8', '2', '4', '8', '7', '1', '4', '5', '1', '6', '4', '0', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0346760_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0346760Field009Chars00 ++ tail)) fragment0346760Acc00900 =
      .ok (.obj (fragment0346760Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0346760_object_field_009"
  err.flush

noncomputable def fragment0346760Chars : List Char := '{' :: (fragment0346760Field000Chars00 ++ fragment0346760Field001Chars00 ++ fragment0346760Field002Chars00 ++ fragment0346760Field003Chars00 ++ fragment0346760Field004Chars00 ++ fragment0346760Field005Chars00 ++ fragment0346760Field006Chars00 ++ fragment0346760Field007Chars00 ++ fragment0346760Field008Chars00 ++ fragment0346760Field009Chars00)
noncomputable def fragment0346760Value : SourceJson := .obj (fragment0346760Acc01000.reverse)

theorem value_fragment0346760 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 235) (fragment0346760Chars ++ tail) =
      .ok (fragment0346760Value, tail) := by
  have hinput : fragment0346760Chars ++ tail = '{' :: (fragment0346760Field000Chars00 ++ (fragment0346760Field001Chars00 ++ (fragment0346760Field002Chars00 ++ (fragment0346760Field003Chars00 ++ (fragment0346760Field004Chars00 ++ (fragment0346760Field005Chars00 ++ (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0346760Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 235) (fragment0346760Chars ++ tail) =
        SourceJson.value (fuel + 235) ('{' :: (fragment0346760Field000Chars00 ++ (fragment0346760Field001Chars00 ++ (fragment0346760Field002Chars00 ++ (fragment0346760Field003Chars00 ++ (fragment0346760Field004Chars00 ++ (fragment0346760Field005Chars00 ++ (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 235)) hinput
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0346760Field000Chars00 ++ (fragment0346760Field001Chars00 ++ (fragment0346760Field002Chars00 ++ (fragment0346760Field003Chars00 ++ (fragment0346760Field004Chars00 ++ (fragment0346760Field005Chars00 ++ (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail)))))))))))) fragment0346760Acc00000 := by rfl
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0346760Field001Chars00 ++ (fragment0346760Field002Chars00 ++ (fragment0346760Field003Chars00 ++ (fragment0346760Field004Chars00 ++ (fragment0346760Field005Chars00 ++ (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail))))))))))) fragment0346760Acc00100 := object_fragment0346760_field_000 fuel (fragment0346760Field001Chars00 ++ (fragment0346760Field002Chars00 ++ (fragment0346760Field003Chars00 ++ (fragment0346760Field004Chars00 ++ (fragment0346760Field005Chars00 ++ (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0346760Field002Chars00 ++ (fragment0346760Field003Chars00 ++ (fragment0346760Field004Chars00 ++ (fragment0346760Field005Chars00 ++ (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail)))))))))) fragment0346760Acc00200 := object_fragment0346760_field_001 fuel (fragment0346760Field002Chars00 ++ (fragment0346760Field003Chars00 ++ (fragment0346760Field004Chars00 ++ (fragment0346760Field005Chars00 ++ (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0346760Field003Chars00 ++ (fragment0346760Field004Chars00 ++ (fragment0346760Field005Chars00 ++ (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail))))))))) fragment0346760Acc00300 := object_fragment0346760_field_002 fuel (fragment0346760Field003Chars00 ++ (fragment0346760Field004Chars00 ++ (fragment0346760Field005Chars00 ++ (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0346760Field004Chars00 ++ (fragment0346760Field005Chars00 ++ (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail)))))))) fragment0346760Acc00400 := object_fragment0346760_field_003 fuel (fragment0346760Field004Chars00 ++ (fragment0346760Field005Chars00 ++ (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0346760Field005Chars00 ++ (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail))))))) fragment0346760Acc00500 := object_fragment0346760_field_004 fuel (fragment0346760Field005Chars00 ++ (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail)))))) fragment0346760Acc00600 := object_fragment0346760_field_005 fuel (fragment0346760Field006Chars00 ++ (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail))))) fragment0346760Acc00700 := object_fragment0346760_field_006 fuel (fragment0346760Field007Chars00 ++ (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail)))) fragment0346760Acc00800 := object_fragment0346760_field_007 fuel (fragment0346760Field008Chars00 ++ (fragment0346760Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0346760Field009Chars00 ++ (tail))) fragment0346760Acc00900 := object_fragment0346760_field_008 fuel (fragment0346760Field009Chars00 ++ (tail))
    _ = .ok (fragment0346760Value, tail) := object_fragment0346760_field_009 fuel (tail)

noncomputable def fragment0348367Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0348367Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0348367Field000Value00 : SourceJson := .number (String.ofList ['7', '2'])
noncomputable def fragment0348367Acc00100 : List (String × SourceJson) := (fragment0348367Field000Key00, fragment0348367Field000Value00) :: fragment0348367Acc00000
noncomputable def fragment0348367Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '2', ',']

theorem object_fragment0348367_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 270) (SourceJson.white (fragment0348367Field000Chars00 ++ tail)) fragment0348367Acc00000 =
      SourceJson.object (fuel + 269) (SourceJson.white tail) fragment0348367Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0348367_object_field_000"
  err.flush

noncomputable def fragment0348367Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0348367Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5'])]
noncomputable def fragment0348367Acc00200 : List (String × SourceJson) := (fragment0348367Field001Key00, fragment0348367Field001Value00) :: fragment0348367Acc00100
noncomputable def fragment0348367Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0348367_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 269) (SourceJson.white (fragment0348367Field001Chars00 ++ tail)) fragment0348367Acc00100 =
      SourceJson.object (fuel + 268) (SourceJson.white tail) fragment0348367Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0348367_object_field_001"
  err.flush

noncomputable def fragment0348367Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0348367Field002Value00 : SourceJson := .str (String.ofList ['5', '2', '0', '6', '5', '6', '7', '6', '1', '8', '4', '3', '8', '6', '8', '9', '4', '0', '0', '9', '7', '9', '5', '6', '9', '8', '7', '5', '2', '0', '5', '0', '5', '1', '4', '1', '9', '0', '6', '1', '/', '7', '2', '8', '3', '6', '4', '4', '2', '4', '9', '4', '4', '8', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0348367Acc00300 : List (String × SourceJson) := (fragment0348367Field002Key00, fragment0348367Field002Value00) :: fragment0348367Acc00200
noncomputable def fragment0348367Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '2', '0', '6', '5', '6', '7', '6', '1', '8', '4', '3', '8', '6', '8', '9', '4', '0', '0', '9', '7', '9', '5', '6', '9', '8', '7', '5', '2', '0', '5', '0', '5', '1', '4', '1', '9', '0', '6', '1', '/', '7', '2', '8', '3', '6', '4', '4', '2', '4', '9', '4', '4', '8', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0348367_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 268) (SourceJson.white (fragment0348367Field002Chars00 ++ tail)) fragment0348367Acc00200 =
      SourceJson.object (fuel + 267) (SourceJson.white tail) fragment0348367Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0348367_object_field_002"
  err.flush

noncomputable def fragment0348367Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0348367Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0348367Acc00400 : List (String × SourceJson) := (fragment0348367Field003Key00, fragment0348367Field003Value00) :: fragment0348367Acc00300
noncomputable def fragment0348367Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0348367_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 267) (SourceJson.white (fragment0348367Field003Chars00 ++ tail)) fragment0348367Acc00300 =
      SourceJson.object (fuel + 266) (SourceJson.white tail) fragment0348367Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0348367_object_field_003"
  err.flush

noncomputable def fragment0348367Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0348367Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '5', '5', '7', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0348367Acc00500 : List (String × SourceJson) := (fragment0348367Field004Key00, fragment0348367Field004Value00) :: fragment0348367Acc00400
noncomputable def fragment0348367Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '5', '5', '7', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0348367_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 266) (SourceJson.white (fragment0348367Field004Chars00 ++ tail)) fragment0348367Acc00400 =
      SourceJson.object (fuel + 265) (SourceJson.white tail) fragment0348367Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0348367_object_field_004"
  err.flush

noncomputable def fragment0348367Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0348367Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '2', '5', '2', '6', '0', '3', '9', '9', '8', '0', '7', '1', '7', '/', '1', '8', '3', '4', '0', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '8', '6', '8', '5', '0', '1', '4', '5', '3', '2', '8', '7', '/', '1', '8', '3', '4', '0', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '7', '1', '5', '0', '6', '0', '5', '2', '0', '2', '4', '8', '9', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '7', '6', '5', '2', '9', '2', '5', '9', '2', '1', '1', '/', '1', '0', '1', '8', '9', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '3', '6', '6', '8', '0', '6', '6', '3', '3', '6', '1', '4', '3', '/', '2', '7', '5', '1', '0', '6', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '4', '7', '0', '5', '8', '1', '5', '0', '6', '9', '6', '7', '3', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '0', '3', '4', '0', '7', '2', '6', '7', '9', '5', '3', '/', '1', '4', '4', '7', '9', '2', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '0', '0', '9', '7', '8', '7', '9', '3', '0', '8', '3', '3', '1', '/', '1', '3', '7', '5', '5', '3', '2', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '4', '5', '7', '0', '5', '3', '1', '0', '7', '1', '2', '7', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '4', '5', '6', '7', '5', '9', '6', '6', '0', '1', '8', '3', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0348367Acc00600 : List (String × SourceJson) := (fragment0348367Field005Key00, fragment0348367Field005Value00) :: fragment0348367Acc00500
noncomputable def fragment0348367Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '5', '2', '6', '0', '3', '9', '9', '8', '0', '7', '1', '7', '/', '1', '8', '3', '4', '0', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '8', '6', '8', '5', '0', '1', '4', '5', '3', '2', '8', '7', '/', '1', '8', '3', '4', '0', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '7', '1', '5', '0', '6', '0', '5', '2', '0', '2', '4', '8', '9', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '7', '6', '5', '2', '9', '2', '5', '9', '2', '1', '1', '/', '1', '0', '1', '8', '9', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '3', '6', '6', '8', '0', '6', '6', '3', '3', '6', '1', '4', '3', '/', '2', '7', '5', '1', '0', '6', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '4', '7', '0', '5', '8', '1', '5', '0', '6', '9', '6', '7', '3', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '0', '3', '4', '0', '7', '2', '6', '7', '9', '5', '3', '/', '1', '4', '4', '7', '9', '2', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '0', '9', '7', '8', '7', '9', '3', '0', '8', '3', '3', '1', '/', '1', '3', '7', '5', '5', '3', '2', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '4', '5', '7', '0', '5', '3', '1', '0', '7', '1', '2', '7', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '4', '5', '6', '7', '5', '9', '6', '6', '0', '1', '8', '3', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0348367_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 265) (SourceJson.white (fragment0348367Field005Chars00 ++ tail)) fragment0348367Acc00500 =
      SourceJson.object (fuel + 264) (SourceJson.white tail) fragment0348367Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0348367_object_field_005"
  err.flush

noncomputable def fragment0348367Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0348367Field006Value00 : SourceJson := .str (String.ofList ['1', '5', '5', '2', '9', '8', '5', '1', '5', '5', '5', '9', '5', '4', '3', '8', '6', '2', '0', '8', '3', '3', '9', '1', '8', '4', '8', '9', '4', '4', '0', '7', '7', '7', '8', '1', '2', '3', '3', '2', '8', '8', '3', '8', '6', '0', '4', '7', '0', '0', '/', '1', '8', '9', '2', '2', '6', '7', '6', '6', '0', '0', '9', '4', '2', '1', '9', '7', '5', '8', '7', '6', '8', '3', '5', '9', '9', '2', '7', '0', '8', '8', '9', '3', '8', '3', '2', '2', '9', '3', '2', '6', '3', '1', '9', '9', '5', '3', '5', '3', '0', '9', '1', '5', '5', '1', '9', '8', '8', '7', '5', '3', '9', '1', '2', '6', '8', '8', '8', '7'])
noncomputable def fragment0348367Acc00700 : List (String × SourceJson) := (fragment0348367Field006Key00, fragment0348367Field006Value00) :: fragment0348367Acc00600
noncomputable def fragment0348367Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '5', '2', '9', '8', '5', '1', '5', '5', '5', '9', '5', '4', '3', '8', '6', '2', '0', '8', '3', '3', '9', '1', '8', '4', '8', '9', '4', '4', '0', '7', '7', '7', '8', '1', '2', '3', '3', '2', '8', '8', '3', '8', '6', '0', '4', '7', '0', '0', '/', '1', '8', '9', '2', '2', '6', '7', '6', '6', '0', '0', '9', '4', '2', '1', '9', '7', '5', '8', '7', '6', '8', '3', '5', '9', '9', '2', '7', '0', '8', '8', '9', '3', '8', '3', '2', '2', '9', '3', '2', '6', '3', '1', '9', '9', '5', '3', '5', '3', '0', '9', '1', '5', '5', '1', '9', '8', '8', '7', '5', '3', '9', '1', '2', '6', '8', '8', '8', '7', '"', ',']

theorem object_fragment0348367_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment0348367Field006Chars00 ++ tail)) fragment0348367Acc00600 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment0348367Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0348367_object_field_006"
  err.flush

noncomputable def fragment0348367Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0348367Field007Value00 : SourceJson := .str (String.ofList ['6', '8', '0', '6', '5', '9', '4', '8', '3', '7', '3', '5', '9', '4', '1', '0', '9', '6', '4', '1', '4', '1', '4', '5', '5', '4', '5', '6', '3', '7', '3', '3', '3', '6', '5', '0', '6', '8', '1', '4', '8', '2', '6', '8', '0', '9', '6', '2', '3', '7', '5', '1', '8', '9', '6', '2', '5', '0', '3', '5', '9', '7', '2', '0', '4', '0', '9', '1', '0', '0', '3', '4', '7', '7', '9', '0', '7', '0', '3', '1', '1', '6', '5', '5', '0', '1', '1', '0', '0', '0', '2', '5', '2', '2', '7', '4', '9', '3', '4', '5', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '9', '9', '0', '6', '4', '5', '3', '5', '5', '2', '3', '9', '6', '2', '0', '0', '0', '8', '3', '2', '2', '4', '5', '2', '3', '8', '5', '0', '2', '7', '1', '2', '1', '5', '6', '9', '0', '6', '7', '2', '3', '6', '2', '5', '2', '0', '0', '3', '1', '4', '4', '4', '6', '9', '4', '5', '5', '6', '3', '1', '8', '8', '9', '3', '8', '1', '7', '9', '7', '0', '5', '9', '2', '9', '2', '4', '1', '1', '5', '5', '4', '0', '4', '4', '3', '2', '6', '4', '7', '1', '4', '1', '4', '4', '9', '8', '4', '1', '3', '4', '4', '3', '5', '3', '3', '9', '2', '0', '6', '0', '0', '0', '3', '0', '2', '7', '1', '9', '5', '4', '2', '7', '0', '3', '5', '3', '6', '0', '9', '2', '6', '8', '4', '2', '4', '7', '9'])
noncomputable def fragment0348367Acc00800 : List (String × SourceJson) := (fragment0348367Field007Key00, fragment0348367Field007Value00) :: fragment0348367Acc00700
noncomputable def fragment0348367Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '8', '0', '6', '5', '9', '4', '8', '3', '7', '3', '5', '9', '4', '1', '0', '9', '6', '4', '1', '4', '1', '4', '5', '5', '4', '5', '6', '3', '7', '3', '3', '3', '6', '5', '0', '6', '8', '1', '4', '8', '2', '6', '8', '0', '9', '6', '2', '3', '7', '5', '1', '8', '9', '6', '2', '5', '0', '3', '5', '9', '7', '2', '0', '4', '0', '9', '1', '0', '0', '3', '4', '7', '7', '9', '0', '7', '0', '3', '1', '1', '6', '5', '5', '0', '1', '1', '0', '0', '0', '2', '5', '2', '2', '7', '4', '9', '3', '4', '5', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '9', '9', '0', '6', '4', '5', '3', '5', '5', '2', '3', '9', '6', '2', '0', '0', '0', '8', '3', '2', '2', '4', '5', '2', '3', '8', '5', '0', '2', '7', '1', '2', '1', '5', '6', '9', '0', '6', '7', '2', '3', '6', '2', '5', '2', '0', '0', '3', '1', '4', '4', '4', '6', '9', '4', '5', '5', '6', '3', '1', '8', '8', '9', '3', '8', '1', '7', '9', '7', '0', '5', '9', '2', '9', '2', '4', '1', '1', '5', '5', '4', '0', '4', '4', '3', '2', '6', '4', '7', '1', '4', '1', '4', '4', '9', '8', '4', '1', '3', '4', '4', '3', '5', '3', '3', '9', '2', '0', '6', '0', '0', '0', '3', '0', '2', '7', '1', '9', '5', '4', '2', '7', '0', '3', '5', '3', '6', '0', '9', '2', '6', '8', '4', '2', '4', '7', '9', '"', ',']

theorem object_fragment0348367_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0348367Field007Chars00 ++ tail)) fragment0348367Acc00700 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0348367Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0348367_object_field_007"
  err.flush

noncomputable def fragment0348367Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0348367Field008Value00 : SourceJson := .str (String.ofList ['6', '5', '0', '2', '2', '5', '9', '8', '4', '8'])
noncomputable def fragment0348367Acc00900 : List (String × SourceJson) := (fragment0348367Field008Key00, fragment0348367Field008Value00) :: fragment0348367Acc00800
noncomputable def fragment0348367Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '5', '0', '2', '2', '5', '9', '8', '4', '8', '"', ',']

theorem object_fragment0348367_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0348367Field008Chars00 ++ tail)) fragment0348367Acc00800 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0348367Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0348367_object_field_008"
  err.flush

noncomputable def fragment0348367Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0348367Field009Value00 : SourceJson := .str (String.ofList ['3', '5', '9', '7', '4', '0', '3', '5', '0', '8', '4'])
noncomputable def fragment0348367Acc01000 : List (String × SourceJson) := (fragment0348367Field009Key00, fragment0348367Field009Value00) :: fragment0348367Acc00900
noncomputable def fragment0348367Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '5', '9', '7', '4', '0', '3', '5', '0', '8', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0348367_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0348367Field009Chars00 ++ tail)) fragment0348367Acc00900 =
      .ok (.obj (fragment0348367Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0348367_object_field_009"
  err.flush

noncomputable def fragment0348367Chars : List Char := '{' :: (fragment0348367Field000Chars00 ++ fragment0348367Field001Chars00 ++ fragment0348367Field002Chars00 ++ fragment0348367Field003Chars00 ++ fragment0348367Field004Chars00 ++ fragment0348367Field005Chars00 ++ fragment0348367Field006Chars00 ++ fragment0348367Field007Chars00 ++ fragment0348367Field008Chars00 ++ fragment0348367Field009Chars00)
noncomputable def fragment0348367Value : SourceJson := .obj (fragment0348367Acc01000.reverse)

theorem value_fragment0348367 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 271) (fragment0348367Chars ++ tail) =
      .ok (fragment0348367Value, tail) := by
  have hinput : fragment0348367Chars ++ tail = '{' :: (fragment0348367Field000Chars00 ++ (fragment0348367Field001Chars00 ++ (fragment0348367Field002Chars00 ++ (fragment0348367Field003Chars00 ++ (fragment0348367Field004Chars00 ++ (fragment0348367Field005Chars00 ++ (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0348367Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 271) (fragment0348367Chars ++ tail) =
        SourceJson.value (fuel + 271) ('{' :: (fragment0348367Field000Chars00 ++ (fragment0348367Field001Chars00 ++ (fragment0348367Field002Chars00 ++ (fragment0348367Field003Chars00 ++ (fragment0348367Field004Chars00 ++ (fragment0348367Field005Chars00 ++ (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 271)) hinput
    _ = SourceJson.object (fuel + 270) (SourceJson.white (fragment0348367Field000Chars00 ++ (fragment0348367Field001Chars00 ++ (fragment0348367Field002Chars00 ++ (fragment0348367Field003Chars00 ++ (fragment0348367Field004Chars00 ++ (fragment0348367Field005Chars00 ++ (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail)))))))))))) fragment0348367Acc00000 := by rfl
    _ = SourceJson.object (fuel + 269) (SourceJson.white (fragment0348367Field001Chars00 ++ (fragment0348367Field002Chars00 ++ (fragment0348367Field003Chars00 ++ (fragment0348367Field004Chars00 ++ (fragment0348367Field005Chars00 ++ (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail))))))))))) fragment0348367Acc00100 := object_fragment0348367_field_000 fuel (fragment0348367Field001Chars00 ++ (fragment0348367Field002Chars00 ++ (fragment0348367Field003Chars00 ++ (fragment0348367Field004Chars00 ++ (fragment0348367Field005Chars00 ++ (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 268) (SourceJson.white (fragment0348367Field002Chars00 ++ (fragment0348367Field003Chars00 ++ (fragment0348367Field004Chars00 ++ (fragment0348367Field005Chars00 ++ (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail)))))))))) fragment0348367Acc00200 := object_fragment0348367_field_001 fuel (fragment0348367Field002Chars00 ++ (fragment0348367Field003Chars00 ++ (fragment0348367Field004Chars00 ++ (fragment0348367Field005Chars00 ++ (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 267) (SourceJson.white (fragment0348367Field003Chars00 ++ (fragment0348367Field004Chars00 ++ (fragment0348367Field005Chars00 ++ (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail))))))))) fragment0348367Acc00300 := object_fragment0348367_field_002 fuel (fragment0348367Field003Chars00 ++ (fragment0348367Field004Chars00 ++ (fragment0348367Field005Chars00 ++ (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 266) (SourceJson.white (fragment0348367Field004Chars00 ++ (fragment0348367Field005Chars00 ++ (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail)))))))) fragment0348367Acc00400 := object_fragment0348367_field_003 fuel (fragment0348367Field004Chars00 ++ (fragment0348367Field005Chars00 ++ (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 265) (SourceJson.white (fragment0348367Field005Chars00 ++ (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail))))))) fragment0348367Acc00500 := object_fragment0348367_field_004 fuel (fragment0348367Field005Chars00 ++ (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail)))))) fragment0348367Acc00600 := object_fragment0348367_field_005 fuel (fragment0348367Field006Chars00 ++ (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail))))) fragment0348367Acc00700 := object_fragment0348367_field_006 fuel (fragment0348367Field007Chars00 ++ (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail)))) fragment0348367Acc00800 := object_fragment0348367_field_007 fuel (fragment0348367Field008Chars00 ++ (fragment0348367Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0348367Field009Chars00 ++ (tail))) fragment0348367Acc00900 := object_fragment0348367_field_008 fuel (fragment0348367Field009Chars00 ++ (tail))
    _ = .ok (fragment0348367Value, tail) := object_fragment0348367_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0071_before_reader"
  err.flush

noncomputable def chunk0071LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0071SuffixChars00 : List Char := [',']
noncomputable def chunk0071Chars00 : List Char := chunk0071LeadChars00 ++ fragment0346760Chars ++ chunk0071SuffixChars00
noncomputable def chunk0071Push00 (acc : List SourceJson) : List SourceJson := fragment0346760Value :: acc

noncomputable def chunk0071AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0071_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 533)
      (SourceJson.white (chunk0071LeadChars00 ++ (fragment0346760Chars ++ rest))) acc =
      (SourceJson.value (fuel + 532) (fragment0346760Chars ++ rest)).bind
        (chunk0071AfterValue00 (fuel + 532) acc) := by rfl

theorem array_chunk0071 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 533) (SourceJson.white (chunk0071Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 532) (SourceJson.white tail) (chunk0071Push00 acc) := by
  have hinput : chunk0071Chars00 ++ tail = chunk0071LeadChars00 ++ (fragment0346760Chars ++ (chunk0071SuffixChars00 ++ tail)) := by
    simp only [chunk0071Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 533) (SourceJson.white (chunk0071Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 533)
          (SourceJson.white (chunk0071LeadChars00 ++ (fragment0346760Chars ++ (chunk0071SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 533) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 532) (fragment0346760Chars ++ (chunk0071SuffixChars00 ++ tail))).bind
        (chunk0071AfterValue00 (fuel + 532) acc) := array_chunk0071_head fuel (chunk0071SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0346760Value, chunk0071SuffixChars00 ++ tail)).bind
        (chunk0071AfterValue00 (fuel + 532) acc) :=
      congrArg (fun result => result.bind (chunk0071AfterValue00 (fuel + 532) acc))
        (value_fragment0346760 (fuel + 297) (chunk0071SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 532) (SourceJson.white tail) (chunk0071Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0071_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0072_before_reader"
  err.flush

noncomputable def chunk0072LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0072SuffixChars00 : List Char := [',']
noncomputable def chunk0072Chars00 : List Char := chunk0072LeadChars00 ++ fragment0348367Chars ++ chunk0072SuffixChars00
noncomputable def chunk0072Push00 (acc : List SourceJson) : List SourceJson := fragment0348367Value :: acc

noncomputable def chunk0072AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0072_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 532)
      (SourceJson.white (chunk0072LeadChars00 ++ (fragment0348367Chars ++ rest))) acc =
      (SourceJson.value (fuel + 531) (fragment0348367Chars ++ rest)).bind
        (chunk0072AfterValue00 (fuel + 531) acc) := by rfl

theorem array_chunk0072 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 532) (SourceJson.white (chunk0072Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 531) (SourceJson.white tail) (chunk0072Push00 acc) := by
  have hinput : chunk0072Chars00 ++ tail = chunk0072LeadChars00 ++ (fragment0348367Chars ++ (chunk0072SuffixChars00 ++ tail)) := by
    simp only [chunk0072Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 532) (SourceJson.white (chunk0072Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 532)
          (SourceJson.white (chunk0072LeadChars00 ++ (fragment0348367Chars ++ (chunk0072SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 532) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 531) (fragment0348367Chars ++ (chunk0072SuffixChars00 ++ tail))).bind
        (chunk0072AfterValue00 (fuel + 531) acc) := array_chunk0072_head fuel (chunk0072SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0348367Value, chunk0072SuffixChars00 ++ tail)).bind
        (chunk0072AfterValue00 (fuel + 531) acc) :=
      congrArg (fun result => result.bind (chunk0072AfterValue00 (fuel + 531) acc))
        (value_fragment0348367 (fuel + 260) (chunk0072SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 531) (SourceJson.white tail) (chunk0072Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0072_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0071Chars00 ++ chunk0072Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0072Push00 (chunk0071Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 533) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 531) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0071Chars00 ++ (chunk0072Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 533) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 533) (SourceJson.white (chunk0071Chars00 ++ (chunk0072Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 533) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 532) (SourceJson.white (chunk0072Chars00 ++ (tail))) (chunk0071Push00 (acc)) := array_chunk0071 fuel (chunk0072Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 531) (SourceJson.white tail) (blockPush acc) := array_chunk0072 fuel (tail) (chunk0071Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 346754).take 3293 = blockChars := by rfl

theorem block_original_split : sourceRest 346754 = blockChars ++ sourceRest 350047 := by
  calc
    sourceRest 346754 = (sourceRest 346754).take 3293 ++ (sourceRest 346754).drop 3293 :=
      (List.take_append_drop 3293 (sourceRest 346754)).symm
    _ = blockChars ++ (sourceRest 346754).drop 3293 :=
      congrArg (fun part => part ++ (sourceRest 346754).drop 3293) block_original_prefix
    _ = blockChars ++ sourceRest 350047 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 346754 3293)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 533) (SourceJson.white (sourceRest 346754)) acc =
      SourceJson.array (fuel + 531) (SourceJson.white (sourceRest 350047)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 533) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 350047) acc)

#print axioms object_fragment0346760_field_000
#print axioms object_fragment0346760_field_001
#print axioms object_fragment0346760_field_002
#print axioms object_fragment0346760_field_003
#print axioms object_fragment0346760_field_004
#print axioms object_fragment0346760_field_005
#print axioms object_fragment0346760_field_006
#print axioms object_fragment0346760_field_007
#print axioms object_fragment0346760_field_008
#print axioms object_fragment0346760_field_009
#print axioms value_fragment0346760
#print axioms object_fragment0348367_field_000
#print axioms object_fragment0348367_field_001
#print axioms object_fragment0348367_field_002
#print axioms object_fragment0348367_field_003
#print axioms object_fragment0348367_field_004
#print axioms object_fragment0348367_field_005
#print axioms object_fragment0348367_field_006
#print axioms object_fragment0348367_field_007
#print axioms object_fragment0348367_field_008
#print axioms object_fragment0348367_field_009
#print axioms value_fragment0348367
#print axioms array_chunk0071_head
#print axioms array_chunk0071
#print axioms array_chunk0072_head
#print axioms array_chunk0072
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock036

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
