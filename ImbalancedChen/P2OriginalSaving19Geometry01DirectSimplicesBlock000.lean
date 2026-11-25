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

namespace SimplicesBlock000

noncomputable def fragment0225569Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0225569Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0225569Field000Value00 : SourceJson := .number (String.ofList ['0'])
noncomputable def fragment0225569Acc00100 : List (String × SourceJson) := (fragment0225569Field000Key00, fragment0225569Field000Value00) :: fragment0225569Acc00000
noncomputable def fragment0225569Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '0', ',']

theorem object_fragment0225569_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0225569Field000Chars00 ++ tail)) fragment0225569Acc00000 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0225569Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0225569_object_field_000"
  err.flush

noncomputable def fragment0225569Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0225569Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0225569Acc00200 : List (String × SourceJson) := (fragment0225569Field001Key00, fragment0225569Field001Value00) :: fragment0225569Acc00100
noncomputable def fragment0225569Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0225569_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0225569Field001Chars00 ++ tail)) fragment0225569Acc00100 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0225569Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0225569_object_field_001"
  err.flush

noncomputable def fragment0225569Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0225569Field002Value00 : SourceJson := .str (String.ofList ['1', '7', '1', '2', '5', '8', '1', '6', '6', '0', '4', '1', '1', '6', '9', '6', '5', '0', '0', '2', '8', '5', '0', '3', '2', '7', '5', '5', '3', '2', '0', '8', '1', '5', '8', '1', '8', '2', '6', '1', '/', '1', '0', '5', '6', '5', '4', '1', '8', '2', '2', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0225569Acc00300 : List (String × SourceJson) := (fragment0225569Field002Key00, fragment0225569Field002Value00) :: fragment0225569Acc00200
noncomputable def fragment0225569Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '7', '1', '2', '5', '8', '1', '6', '6', '0', '4', '1', '1', '6', '9', '6', '5', '0', '0', '2', '8', '5', '0', '3', '2', '7', '5', '5', '3', '2', '0', '8', '1', '5', '8', '1', '8', '2', '6', '1', '/', '1', '0', '5', '6', '5', '4', '1', '8', '2', '2', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0225569_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0225569Field002Chars00 ++ tail)) fragment0225569Acc00200 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0225569Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0225569_object_field_002"
  err.flush

noncomputable def fragment0225569Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0225569Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0225569Acc00400 : List (String × SourceJson) := (fragment0225569Field003Key00, fragment0225569Field003Value00) :: fragment0225569Acc00300
noncomputable def fragment0225569Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0225569_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0225569Field003Chars00 ++ tail)) fragment0225569Acc00300 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0225569Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0225569_object_field_003"
  err.flush

noncomputable def fragment0225569Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0225569Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '4', '0', '4', '6', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0225569Acc00500 : List (String × SourceJson) := (fragment0225569Field004Key00, fragment0225569Field004Value00) :: fragment0225569Acc00400
noncomputable def fragment0225569Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '4', '0', '4', '6', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0225569_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0225569Field004Chars00 ++ tail)) fragment0225569Acc00400 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0225569Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0225569_object_field_004"
  err.flush

noncomputable def fragment0225569Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0225569Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '2', '8', '2', '5', '8', '5', '4', '9', '1', '4', '7', '/', '2', '7', '9', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '5', '6', '5', '5', '0', '7', '8', '0', '6', '6', '7', '/', '2', '7', '9', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '6', '4', '0', '6', '4', '5', '7', '1', '2', '0', '1', '/', '5', '9', '9', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '8', '1', '4', '8', '5', '1', '9', '8', '0', '1', '/', '2', '7', '9', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '9', '2', '6', '1', '1', '7', '6', '8', '3', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '4', '2', '0', '5', '1', '4', '4', '0', '2', '7', '3', '/', '4', '1', '9', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '2', '8', '7', '7', '2', '5', '5', '8', '9', '8', '7', '/', '4', '7', '9', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '2', '9', '2', '2', '2', '3', '2', '0', '0', '1', '7', '/', '4', '7', '9', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '2', '3', '9', '6', '5', '5', '2', '6', '1', '1', '/', '8', '3', '9', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '2', '3', '7', '9', '7', '5', '9', '3', '3', '1', '/', '8', '3', '9', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0225569Acc00600 : List (String × SourceJson) := (fragment0225569Field005Key00, fragment0225569Field005Value00) :: fragment0225569Acc00500
noncomputable def fragment0225569Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '2', '8', '2', '5', '8', '5', '4', '9', '1', '4', '7', '/', '2', '7', '9', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '5', '6', '5', '5', '0', '7', '8', '0', '6', '6', '7', '/', '2', '7', '9', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '6', '4', '0', '6', '4', '5', '7', '1', '2', '0', '1', '/', '5', '9', '9', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '8', '1', '4', '8', '5', '1', '9', '8', '0', '1', '/', '2', '7', '9', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '9', '2', '6', '1', '1', '7', '6', '8', '3', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '2', '0', '5', '1', '4', '4', '0', '2', '7', '3', '/', '4', '1', '9', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '8', '7', '7', '2', '5', '5', '8', '9', '8', '7', '/', '4', '7', '9', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '2', '9', '2', '2', '2', '3', '2', '0', '0', '1', '7', '/', '4', '7', '9', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '2', '3', '9', '6', '5', '5', '2', '6', '1', '1', '/', '8', '3', '9', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '2', '3', '7', '9', '7', '5', '9', '3', '3', '1', '/', '8', '3', '9', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0225569_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0225569Field005Chars00 ++ tail)) fragment0225569Acc00500 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0225569Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0225569_object_field_005"
  err.flush

noncomputable def fragment0225569Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0225569Field006Value00 : SourceJson := .str (String.ofList ['2', '5', '9', '1', '3', '5', '6', '4', '5', '8', '4', '2', '2', '5', '0', '6', '0', '0', '2', '5', '5', '7', '7', '7', '0', '5', '3', '1', '9', '5', '0', '8', '5', '7', '2', '1', '9', '0', '8', '8', '3', '4', '3', '7', '5', '0', '/', '2', '5', '4', '1', '7', '5', '5', '2', '4', '3', '7', '8', '5', '0', '1', '6', '1', '4', '3', '5', '8', '9', '2', '8', '3', '9', '4', '4', '2', '5', '8', '1', '6', '0', '5', '9', '8', '0', '7', '6', '8', '4', '2', '9', '3', '3', '6', '8', '5', '8', '9', '4', '3', '9', '2', '6', '2', '0', '0', '0', '9'])
noncomputable def fragment0225569Acc00700 : List (String × SourceJson) := (fragment0225569Field006Key00, fragment0225569Field006Value00) :: fragment0225569Acc00600
noncomputable def fragment0225569Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '5', '9', '1', '3', '5', '6', '4', '5', '8', '4', '2', '2', '5', '0', '6', '0', '0', '2', '5', '5', '7', '7', '7', '0', '5', '3', '1', '9', '5', '0', '8', '5', '7', '2', '1', '9', '0', '8', '8', '3', '4', '3', '7', '5', '0', '/', '2', '5', '4', '1', '7', '5', '5', '2', '4', '3', '7', '8', '5', '0', '1', '6', '1', '4', '3', '5', '8', '9', '2', '8', '3', '9', '4', '4', '2', '5', '8', '1', '6', '0', '5', '9', '8', '0', '7', '6', '8', '4', '2', '9', '3', '3', '6', '8', '5', '8', '9', '4', '3', '9', '2', '6', '2', '0', '0', '0', '9', '"', ',']

theorem object_fragment0225569_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0225569Field006Chars00 ++ tail)) fragment0225569Acc00600 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0225569Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0225569_object_field_006"
  err.flush

noncomputable def fragment0225569Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0225569Field007Value00 : SourceJson := .str (String.ofList ['5', '5', '1', '5', '2', '0', '7', '1', '6', '0', '2', '9', '4', '5', '3', '7', '9', '6', '5', '5', '6', '7', '9', '5', '0', '4', '4', '3', '0', '9', '2', '9', '1', '2', '5', '3', '7', '0', '7', '2', '5', '0', '4', '2', '4', '1', '1', '5', '7', '1', '2', '8', '9', '8', '8', '1', '6', '4', '5', '7', '3', '0', '1', '8', '8', '8', '5', '5', '5', '8', '1', '1', '3', '2', '7', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '7', '8', '3', '1', '7', '0', '6', '3', '2', '7', '2', '4', '1', '8', '5', '6', '7', '6', '3', '9', '3', '8', '5', '3', '1', '8', '7', '9', '6', '8', '1', '9', '1', '7', '3', '4', '9', '7', '9', '3', '0', '3', '3', '1', '1', '5', '8', '2', '1', '4', '0', '8', '9', '1', '3', '0', '4', '3', '4', '3', '7', '2', '6', '2', '6', '2', '5', '9', '7', '3', '6', '9', '4', '7', '2', '1', '8', '7', '4', '3', '5', '5', '7', '7', '5', '5', '9', '2', '3', '1', '9', '7', '9', '5', '3', '1', '7', '0', '3', '3', '3', '8', '6', '5', '0', '8', '9', '2', '3', '0', '4', '0', '2', '3', '4', '3'])
noncomputable def fragment0225569Acc00800 : List (String × SourceJson) := (fragment0225569Field007Key00, fragment0225569Field007Value00) :: fragment0225569Acc00700
noncomputable def fragment0225569Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '5', '1', '5', '2', '0', '7', '1', '6', '0', '2', '9', '4', '5', '3', '7', '9', '6', '5', '5', '6', '7', '9', '5', '0', '4', '4', '3', '0', '9', '2', '9', '1', '2', '5', '3', '7', '0', '7', '2', '5', '0', '4', '2', '4', '1', '1', '5', '7', '1', '2', '8', '9', '8', '8', '1', '6', '4', '5', '7', '3', '0', '1', '8', '8', '8', '5', '5', '5', '8', '1', '1', '3', '2', '7', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '7', '8', '3', '1', '7', '0', '6', '3', '2', '7', '2', '4', '1', '8', '5', '6', '7', '6', '3', '9', '3', '8', '5', '3', '1', '8', '7', '9', '6', '8', '1', '9', '1', '7', '3', '4', '9', '7', '9', '3', '0', '3', '3', '1', '1', '5', '8', '2', '1', '4', '0', '8', '9', '1', '3', '0', '4', '3', '4', '3', '7', '2', '6', '2', '6', '2', '5', '9', '7', '3', '6', '9', '4', '7', '2', '1', '8', '7', '4', '3', '5', '5', '7', '7', '5', '5', '9', '2', '3', '1', '9', '7', '9', '5', '3', '1', '7', '0', '3', '3', '3', '8', '6', '5', '0', '8', '9', '2', '3', '0', '4', '0', '2', '3', '4', '3', '"', ',']

theorem object_fragment0225569_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0225569Field007Chars00 ++ tail)) fragment0225569Acc00700 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0225569Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0225569_object_field_007"
  err.flush

noncomputable def fragment0225569Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0225569Field008Value00 : SourceJson := .str (String.ofList ['8', '0', '7', '7', '4', '2', '6', '4', '6', '0', '4', '0', '7', '5'])
noncomputable def fragment0225569Acc00900 : List (String × SourceJson) := (fragment0225569Field008Key00, fragment0225569Field008Value00) :: fragment0225569Acc00800
noncomputable def fragment0225569Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '0', '7', '7', '4', '2', '6', '4', '6', '0', '4', '0', '7', '5', '"', ',']

theorem object_fragment0225569_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0225569Field008Chars00 ++ tail)) fragment0225569Acc00800 =
      SourceJson.object (fuel + 222) (SourceJson.white tail) fragment0225569Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0225569_object_field_008"
  err.flush

noncomputable def fragment0225569Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0225569Field009Value00 : SourceJson := .str (String.ofList ['5', '6', '1', '4', '1', '6', '0', '9', '8', '6', '7', '6', '3', '6', '9'])
noncomputable def fragment0225569Acc01000 : List (String × SourceJson) := (fragment0225569Field009Key00, fragment0225569Field009Value00) :: fragment0225569Acc00900
noncomputable def fragment0225569Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '6', '1', '4', '1', '6', '0', '9', '8', '6', '7', '6', '3', '6', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0225569_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment0225569Field009Chars00 ++ tail)) fragment0225569Acc00900 =
      .ok (.obj (fragment0225569Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0225569_object_field_009"
  err.flush

noncomputable def fragment0225569Chars : List Char := '{' :: (fragment0225569Field000Chars00 ++ fragment0225569Field001Chars00 ++ fragment0225569Field002Chars00 ++ fragment0225569Field003Chars00 ++ fragment0225569Field004Chars00 ++ fragment0225569Field005Chars00 ++ fragment0225569Field006Chars00 ++ fragment0225569Field007Chars00 ++ fragment0225569Field008Chars00 ++ fragment0225569Field009Chars00)
noncomputable def fragment0225569Value : SourceJson := .obj (fragment0225569Acc01000.reverse)

theorem value_fragment0225569 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 232) (fragment0225569Chars ++ tail) =
      .ok (fragment0225569Value, tail) := by
  have hinput : fragment0225569Chars ++ tail = '{' :: (fragment0225569Field000Chars00 ++ (fragment0225569Field001Chars00 ++ (fragment0225569Field002Chars00 ++ (fragment0225569Field003Chars00 ++ (fragment0225569Field004Chars00 ++ (fragment0225569Field005Chars00 ++ (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0225569Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 232) (fragment0225569Chars ++ tail) =
        SourceJson.value (fuel + 232) ('{' :: (fragment0225569Field000Chars00 ++ (fragment0225569Field001Chars00 ++ (fragment0225569Field002Chars00 ++ (fragment0225569Field003Chars00 ++ (fragment0225569Field004Chars00 ++ (fragment0225569Field005Chars00 ++ (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 232)) hinput
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0225569Field000Chars00 ++ (fragment0225569Field001Chars00 ++ (fragment0225569Field002Chars00 ++ (fragment0225569Field003Chars00 ++ (fragment0225569Field004Chars00 ++ (fragment0225569Field005Chars00 ++ (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail)))))))))))) fragment0225569Acc00000 := by rfl
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0225569Field001Chars00 ++ (fragment0225569Field002Chars00 ++ (fragment0225569Field003Chars00 ++ (fragment0225569Field004Chars00 ++ (fragment0225569Field005Chars00 ++ (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail))))))))))) fragment0225569Acc00100 := object_fragment0225569_field_000 fuel (fragment0225569Field001Chars00 ++ (fragment0225569Field002Chars00 ++ (fragment0225569Field003Chars00 ++ (fragment0225569Field004Chars00 ++ (fragment0225569Field005Chars00 ++ (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0225569Field002Chars00 ++ (fragment0225569Field003Chars00 ++ (fragment0225569Field004Chars00 ++ (fragment0225569Field005Chars00 ++ (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail)))))))))) fragment0225569Acc00200 := object_fragment0225569_field_001 fuel (fragment0225569Field002Chars00 ++ (fragment0225569Field003Chars00 ++ (fragment0225569Field004Chars00 ++ (fragment0225569Field005Chars00 ++ (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0225569Field003Chars00 ++ (fragment0225569Field004Chars00 ++ (fragment0225569Field005Chars00 ++ (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail))))))))) fragment0225569Acc00300 := object_fragment0225569_field_002 fuel (fragment0225569Field003Chars00 ++ (fragment0225569Field004Chars00 ++ (fragment0225569Field005Chars00 ++ (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0225569Field004Chars00 ++ (fragment0225569Field005Chars00 ++ (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail)))))))) fragment0225569Acc00400 := object_fragment0225569_field_003 fuel (fragment0225569Field004Chars00 ++ (fragment0225569Field005Chars00 ++ (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0225569Field005Chars00 ++ (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail))))))) fragment0225569Acc00500 := object_fragment0225569_field_004 fuel (fragment0225569Field005Chars00 ++ (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail)))))) fragment0225569Acc00600 := object_fragment0225569_field_005 fuel (fragment0225569Field006Chars00 ++ (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail))))) fragment0225569Acc00700 := object_fragment0225569_field_006 fuel (fragment0225569Field007Chars00 ++ (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail)))) fragment0225569Acc00800 := object_fragment0225569_field_007 fuel (fragment0225569Field008Chars00 ++ (fragment0225569Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment0225569Field009Chars00 ++ (tail))) fragment0225569Acc00900 := object_fragment0225569_field_008 fuel (fragment0225569Field009Chars00 ++ (tail))
    _ = .ok (fragment0225569Value, tail) := object_fragment0225569_field_009 fuel (tail)

noncomputable def fragment0227158Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0227158Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0227158Field000Value00 : SourceJson := .number (String.ofList ['1'])
noncomputable def fragment0227158Acc00100 : List (String × SourceJson) := (fragment0227158Field000Key00, fragment0227158Field000Value00) :: fragment0227158Acc00000
noncomputable def fragment0227158Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', ',']

theorem object_fragment0227158_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 349) (SourceJson.white (fragment0227158Field000Chars00 ++ tail)) fragment0227158Acc00000 =
      SourceJson.object (fuel + 348) (SourceJson.white tail) fragment0227158Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0227158_object_field_000"
  err.flush

noncomputable def fragment0227158Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0227158Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0227158Acc00200 : List (String × SourceJson) := (fragment0227158Field001Key00, fragment0227158Field001Value00) :: fragment0227158Acc00100
noncomputable def fragment0227158Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0227158_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 348) (SourceJson.white (fragment0227158Field001Chars00 ++ tail)) fragment0227158Acc00100 =
      SourceJson.object (fuel + 347) (SourceJson.white tail) fragment0227158Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0227158_object_field_001"
  err.flush

noncomputable def fragment0227158Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0227158Field002Value00 : SourceJson := .str (String.ofList ['9', '0', '8', '6', '7', '5', '9', '9', '0', '1', '5', '0', '5', '8', '7', '5', '7', '3', '8', '8', '2', '5', '5', '6', '3', '7', '4', '5', '0', '8', '0', '6', '2', '5', '9', '3', '6', '3', '5', '5', '8', '2', '6', '5', '2', '8', '0', '3', '/', '1', '0', '6', '5', '4', '3', '7', '9', '0', '4', '2', '9', '9', '3', '6', '0', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0227158Acc00300 : List (String × SourceJson) := (fragment0227158Field002Key00, fragment0227158Field002Value00) :: fragment0227158Acc00200
noncomputable def fragment0227158Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '0', '8', '6', '7', '5', '9', '9', '0', '1', '5', '0', '5', '8', '7', '5', '7', '3', '8', '8', '2', '5', '5', '6', '3', '7', '4', '5', '0', '8', '0', '6', '2', '5', '9', '3', '6', '3', '5', '5', '8', '2', '6', '5', '2', '8', '0', '3', '/', '1', '0', '6', '5', '4', '3', '7', '9', '0', '4', '2', '9', '9', '3', '6', '0', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0227158_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 347) (SourceJson.white (fragment0227158Field002Chars00 ++ tail)) fragment0227158Acc00200 =
      SourceJson.object (fuel + 346) (SourceJson.white tail) fragment0227158Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0227158_object_field_002"
  err.flush

noncomputable def fragment0227158Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0227158Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '4', '0', '2', '3', '/', '9', '3', '7', '1', '2', '5', '0', '0', '0'])
noncomputable def fragment0227158Acc00400 : List (String × SourceJson) := (fragment0227158Field003Key00, fragment0227158Field003Value00) :: fragment0227158Acc00300
noncomputable def fragment0227158Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '7', '4', '0', '2', '3', '/', '9', '3', '7', '1', '2', '5', '0', '0', '0', '"', ',']

theorem object_fragment0227158_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 346) (SourceJson.white (fragment0227158Field003Chars00 ++ tail)) fragment0227158Acc00300 =
      SourceJson.object (fuel + 345) (SourceJson.white tail) fragment0227158Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0227158_object_field_003"
  err.flush

noncomputable def fragment0227158Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0227158Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '4', '0', '4', '6', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0227158Acc00500 : List (String × SourceJson) := (fragment0227158Field004Key00, fragment0227158Field004Value00) :: fragment0227158Acc00400
noncomputable def fragment0227158Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '4', '0', '4', '6', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0227158_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 345) (SourceJson.white (fragment0227158Field004Chars00 ++ tail)) fragment0227158Acc00400 =
      SourceJson.object (fuel + 344) (SourceJson.white tail) fragment0227158Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0227158_object_field_004"
  err.flush

noncomputable def fragment0227158Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0227158Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '0', '0', '6', '0', '8', '1', '9', '2', '2', '4', '8', '2', '2', '9', '2', '7', '/', '2', '3', '4', '8', '4', '8', '5', '5', '4', '2', '3', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '7', '1', '5', '0', '6', '0', '4', '4', '2', '2', '8', '0', '0', '5', '1', '3', '/', '1', '5', '0', '3', '0', '3', '0', '7', '4', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '5', '9', '5', '2', '1', '6', '8', '7', '5', '9', '9', '2', '6', '2', '0', '9', '1', '/', '1', '2', '8', '8', '3', '1', '2', '0', '6', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '9', '4', '0', '1', '4', '8', '1', '9', '7', '6', '5', '6', '1', '3', '6', '5', '3', '/', '3', '0', '0', '6', '0', '6', '1', '4', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '5', '3', '6', '6', '8', '6', '9', '1', '0', '5', '4', '3', '0', '1', '/', '1', '8', '9', '4', '5', '7', '6', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '4', '2', '6', '9', '2', '0', '8', '1', '2', '1', '6', '1', '8', '3', '/', '9', '0', '1', '8', '1', '8', '4', '4', '8', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '5', '9', '1', '5', '6', '2', '9', '2', '9', '3', '2', '0', '6', '2', '2', '3', '/', '7', '3', '6', '1', '7', '8', '3', '2', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '0', '6', '4', '1', '4', '5', '1', '2', '4', '9', '0', '2', '3', '8', '9', '3', '/', '7', '3', '6', '1', '7', '8', '3', '2', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '8', '5', '4', '3', '6', '1', '2', '3', '4', '4', '8', '2', '3', '2', '3', '/', '5', '6', '3', '6', '3', '6', '5', '3', '0', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '9', '4', '2', '9', '0', '2', '9', '9', '8', '6', '2', '3', '1', '4', '9', '/', '4', '5', '0', '9', '0', '9', '2', '2', '4', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0227158Acc00600 : List (String × SourceJson) := (fragment0227158Field005Key00, fragment0227158Field005Value00) :: fragment0227158Acc00500
noncomputable def fragment0227158Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '0', '6', '0', '8', '1', '9', '2', '2', '4', '8', '2', '2', '9', '2', '7', '/', '2', '3', '4', '8', '4', '8', '5', '5', '4', '2', '3', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '7', '1', '5', '0', '6', '0', '4', '4', '2', '2', '8', '0', '0', '5', '1', '3', '/', '1', '5', '0', '3', '0', '3', '0', '7', '4', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '5', '9', '5', '2', '1', '6', '8', '7', '5', '9', '9', '2', '6', '2', '0', '9', '1', '/', '1', '2', '8', '8', '3', '1', '2', '0', '6', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '9', '4', '0', '1', '4', '8', '1', '9', '7', '6', '5', '6', '1', '3', '6', '5', '3', '/', '3', '0', '0', '6', '0', '6', '1', '4', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '5', '3', '6', '6', '8', '6', '9', '1', '0', '5', '4', '3', '0', '1', '/', '1', '8', '9', '4', '5', '7', '6', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '4', '2', '6', '9', '2', '0', '8', '1', '2', '1', '6', '1', '8', '3', '/', '9', '0', '1', '8', '1', '8', '4', '4', '8', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '5', '9', '1', '5', '6', '2', '9', '2', '9', '3', '2', '0', '6', '2', '2', '3', '/', '7', '3', '6', '1', '7', '8', '3', '2', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '0', '6', '4', '1', '4', '5', '1', '2', '4', '9', '0', '2', '3', '8', '9', '3', '/', '7', '3', '6', '1', '7', '8', '3', '2', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '8', '5', '4', '3', '6', '1', '2', '3', '4', '4', '8', '2', '3', '2', '3', '/', '5', '6', '3', '6', '3', '6', '5', '3', '0', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '6', '9', '4', '2', '9', '0', '2', '9', '9', '8', '6', '2', '3', '1', '4', '9', '/', '4', '5', '0', '9', '0', '9', '2', '2', '4', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0227158_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 344) (SourceJson.white (fragment0227158Field005Chars00 ++ tail)) fragment0227158Acc00500 =
      SourceJson.object (fuel + 343) (SourceJson.white tail) fragment0227158Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0227158_object_field_005"
  err.flush

noncomputable def fragment0227158Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0227158Field006Value00 : SourceJson := .str (String.ofList ['2', '4', '3', '9', '8', '4', '7', '2', '8', '2', '4', '2', '3', '7', '6', '1', '2', '9', '4', '6', '6', '0', '1', '6', '2', '1', '1', '2', '5', '4', '5', '6', '8', '2', '2', '7', '7', '5', '1', '0', '6', '7', '3', '4', '6', '8', '7', '7', '8', '5', '9', '1', '1', '7', '2', '5', '0', '0', '0', '0', '/', '2', '2', '2', '8', '6', '6', '3', '3', '1', '9', '8', '9', '8', '6', '6', '3', '4', '2', '3', '9', '3', '4', '4', '9', '0', '1', '5', '9', '0', '5', '6', '3', '6', '8', '7', '2', '8', '0', '8', '7', '0', '7', '8', '9', '6', '9', '0', '2', '2', '6', '2', '5', '2', '6', '8', '3', '4', '6', '3', '3', '1', '4', '2', '7', '3', '8', '6', '0', '6', '4', '9'])
noncomputable def fragment0227158Acc00700 : List (String × SourceJson) := (fragment0227158Field006Key00, fragment0227158Field006Value00) :: fragment0227158Acc00600
noncomputable def fragment0227158Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '4', '3', '9', '8', '4', '7', '2', '8', '2', '4', '2', '3', '7', '6', '1', '2', '9', '4', '6', '6', '0', '1', '6', '2', '1', '1', '2', '5', '4', '5', '6', '8', '2', '2', '7', '7', '5', '1', '0', '6', '7', '3', '4', '6', '8', '7', '7', '8', '5', '9', '1', '1', '7', '2', '5', '0', '0', '0', '0', '/', '2', '2', '2', '8', '6', '6', '3', '3', '1', '9', '8', '9', '8', '6', '6', '3', '4', '2', '3', '9', '3', '4', '4', '9', '0', '1', '5', '9', '0', '5', '6', '3', '6', '8', '7', '2', '8', '0', '8', '7', '0', '7', '8', '9', '6', '9', '0', '2', '2', '6', '2', '5', '2', '6', '8', '3', '4', '6', '3', '3', '1', '4', '2', '7', '3', '8', '6', '0', '6', '4', '9', '"', ',']

theorem object_fragment0227158_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 343) (SourceJson.white (fragment0227158Field006Chars00 ++ tail)) fragment0227158Acc00600 =
      SourceJson.object (fuel + 342) (SourceJson.white tail) fragment0227158Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0227158_object_field_006"
  err.flush

noncomputable def fragment0227158Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0227158Field007Value00 : SourceJson := .str (String.ofList ['3', '3', '3', '6', '3', '8', '2', '8', '7', '8', '7', '3', '2', '5', '0', '6', '8', '3', '6', '8', '5', '3', '9', '0', '1', '1', '3', '6', '2', '7', '1', '0', '4', '5', '4', '0', '6', '2', '1', '6', '8', '9', '4', '3', '3', '2', '8', '5', '9', '4', '8', '7', '7', '8', '5', '2', '6', '5', '2', '4', '2', '1', '9', '9', '0', '5', '1', '0', '8', '6', '5', '0', '1', '7', '3', '4', '2', '0', '1', '1', '6', '7', '1', '7', '7', '7', '1', '3', '6', '1', '9', '0', '6', '6', '7', '2', '9', '9', '8', '4', '9', '0', '5', '1', '5', '2', '6', '8', '0', '4', '6', '5', '9', '2', '1', '6', '8', '1', '2', '1', '8', '1', '5', '8', '8', '8', '9', '7', '4', '2', '0', '9', '6', '7', '2', '9', '6', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '2', '5', '2', '3', '8', '4', '5', '2', '8', '0', '8', '2', '0', '7', '1', '6', '1', '9', '6', '4', '8', '2', '3', '7', '5', '8', '0', '5', '7', '1', '5', '7', '4', '5', '6', '7', '2', '3', '6', '2', '4', '4', '4', '8', '5', '2', '7', '2', '3', '2', '6', '9', '6', '0', '7', '2', '8', '9', '7', '0', '6', '5', '8', '5', '7', '6', '8', '6', '7', '9', '3', '7', '4', '6', '8', '3', '6', '6', '7', '9', '7', '8', '3', '9', '0', '2', '8', '1', '3', '8', '0', '6', '8', '2', '1', '9', '6', '9', '7', '6', '8', '6', '8', '4', '7', '2', '4', '5', '3', '1', '6', '8', '7', '5', '6', '8', '7', '0', '2', '8', '2', '4', '2', '3', '1', '0', '3', '0', '2', '0', '9', '0', '4', '1', '0', '3', '8', '9', '9', '0', '7', '3', '3', '5', '6', '9', '6', '5', '9', '7', '5', '6', '8', '1', '6', '8', '0', '1', '3', '2', '2', '2', '3', '3', '8', '5', '8', '7', '3', '1', '9', '5', '1'])
noncomputable def fragment0227158Acc00800 : List (String × SourceJson) := (fragment0227158Field007Key00, fragment0227158Field007Value00) :: fragment0227158Acc00700
noncomputable def fragment0227158Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '3', '3', '6', '3', '8', '2', '8', '7', '8', '7', '3', '2', '5', '0', '6', '8', '3', '6', '8', '5', '3', '9', '0', '1', '1', '3', '6', '2', '7', '1', '0', '4', '5', '4', '0', '6', '2', '1', '6', '8', '9', '4', '3', '3', '2', '8', '5', '9', '4', '8', '7', '7', '8', '5', '2', '6', '5', '2', '4', '2', '1', '9', '9', '0', '5', '1', '0', '8', '6', '5', '0', '1', '7', '3', '4', '2', '0', '1', '1', '6', '7', '1', '7', '7', '7', '1', '3', '6', '1', '9', '0', '6', '6', '7', '2', '9', '9', '8', '4', '9', '0', '5', '1', '5', '2', '6', '8', '0', '4', '6', '5', '9', '2', '1', '6', '8', '1', '2', '1', '8', '1', '5', '8', '8', '8', '9', '7', '4', '2', '0', '9', '6', '7', '2', '9', '6', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '2', '5', '2', '3', '8', '4', '5', '2', '8', '0', '8', '2', '0', '7', '1', '6', '1', '9', '6', '4', '8', '2', '3', '7', '5', '8', '0', '5', '7', '1', '5', '7', '4', '5', '6', '7', '2', '3', '6', '2', '4', '4', '4', '8', '5', '2', '7', '2', '3', '2', '6', '9', '6', '0', '7', '2', '8', '9', '7', '0', '6', '5', '8', '5', '7', '6', '8', '6', '7', '9', '3', '7', '4', '6', '8', '3', '6', '6', '7', '9', '7', '8', '3', '9', '0', '2', '8', '1', '3', '8', '0', '6', '8', '2', '1', '9', '6', '9', '7', '6', '8', '6', '8', '4', '7', '2', '4', '5', '3', '1', '6', '8', '7', '5', '6', '8', '7', '0', '2', '8', '2', '4', '2', '3', '1', '0', '3', '0', '2', '0', '9', '0', '4', '1', '0', '3', '8', '9', '9', '0', '7', '3', '3', '5', '6', '9', '6', '5', '9', '7', '5', '6', '8', '1', '6', '8', '0', '1', '3', '2', '2', '2', '3', '3', '8', '5', '8', '7', '3', '1', '9', '5', '1', '"', ',']

theorem object_fragment0227158_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 342) (SourceJson.white (fragment0227158Field007Chars00 ++ tail)) fragment0227158Acc00700 =
      SourceJson.object (fuel + 341) (SourceJson.white tail) fragment0227158Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0227158_object_field_007"
  err.flush

noncomputable def fragment0227158Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0227158Field008Value00 : SourceJson := .str (String.ofList ['8', '6', '7', '3', '5', '6', '7', '4', '8', '2', '1', '7', '3', '3', '7', '0', '8', '6'])
noncomputable def fragment0227158Acc00900 : List (String × SourceJson) := (fragment0227158Field008Key00, fragment0227158Field008Value00) :: fragment0227158Acc00800
noncomputable def fragment0227158Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '6', '7', '3', '5', '6', '7', '4', '8', '2', '1', '7', '3', '3', '7', '0', '8', '6', '"', ',']

theorem object_fragment0227158_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 341) (SourceJson.white (fragment0227158Field008Chars00 ++ tail)) fragment0227158Acc00800 =
      SourceJson.object (fuel + 340) (SourceJson.white tail) fragment0227158Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0227158_object_field_008"
  err.flush

noncomputable def fragment0227158Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0227158Field009Value00 : SourceJson := .str (String.ofList ['6', '2', '1', '6', '1', '7', '0', '7', '9', '0', '3', '0', '3', '6', '1', '9', '1', '5', '9'])
noncomputable def fragment0227158Acc01000 : List (String × SourceJson) := (fragment0227158Field009Key00, fragment0227158Field009Value00) :: fragment0227158Acc00900
noncomputable def fragment0227158Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '2', '1', '6', '1', '7', '0', '7', '9', '0', '3', '0', '3', '6', '1', '9', '1', '5', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0227158_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 340) (SourceJson.white (fragment0227158Field009Chars00 ++ tail)) fragment0227158Acc00900 =
      .ok (.obj (fragment0227158Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0227158_object_field_009"
  err.flush

noncomputable def fragment0227158Chars : List Char := '{' :: (fragment0227158Field000Chars00 ++ fragment0227158Field001Chars00 ++ fragment0227158Field002Chars00 ++ fragment0227158Field003Chars00 ++ fragment0227158Field004Chars00 ++ fragment0227158Field005Chars00 ++ fragment0227158Field006Chars00 ++ fragment0227158Field007Chars00 ++ fragment0227158Field008Chars00 ++ fragment0227158Field009Chars00)
noncomputable def fragment0227158Value : SourceJson := .obj (fragment0227158Acc01000.reverse)

theorem value_fragment0227158 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 350) (fragment0227158Chars ++ tail) =
      .ok (fragment0227158Value, tail) := by
  have hinput : fragment0227158Chars ++ tail = '{' :: (fragment0227158Field000Chars00 ++ (fragment0227158Field001Chars00 ++ (fragment0227158Field002Chars00 ++ (fragment0227158Field003Chars00 ++ (fragment0227158Field004Chars00 ++ (fragment0227158Field005Chars00 ++ (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0227158Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 350) (fragment0227158Chars ++ tail) =
        SourceJson.value (fuel + 350) ('{' :: (fragment0227158Field000Chars00 ++ (fragment0227158Field001Chars00 ++ (fragment0227158Field002Chars00 ++ (fragment0227158Field003Chars00 ++ (fragment0227158Field004Chars00 ++ (fragment0227158Field005Chars00 ++ (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 350)) hinput
    _ = SourceJson.object (fuel + 349) (SourceJson.white (fragment0227158Field000Chars00 ++ (fragment0227158Field001Chars00 ++ (fragment0227158Field002Chars00 ++ (fragment0227158Field003Chars00 ++ (fragment0227158Field004Chars00 ++ (fragment0227158Field005Chars00 ++ (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail)))))))))))) fragment0227158Acc00000 := by rfl
    _ = SourceJson.object (fuel + 348) (SourceJson.white (fragment0227158Field001Chars00 ++ (fragment0227158Field002Chars00 ++ (fragment0227158Field003Chars00 ++ (fragment0227158Field004Chars00 ++ (fragment0227158Field005Chars00 ++ (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail))))))))))) fragment0227158Acc00100 := object_fragment0227158_field_000 fuel (fragment0227158Field001Chars00 ++ (fragment0227158Field002Chars00 ++ (fragment0227158Field003Chars00 ++ (fragment0227158Field004Chars00 ++ (fragment0227158Field005Chars00 ++ (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 347) (SourceJson.white (fragment0227158Field002Chars00 ++ (fragment0227158Field003Chars00 ++ (fragment0227158Field004Chars00 ++ (fragment0227158Field005Chars00 ++ (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail)))))))))) fragment0227158Acc00200 := object_fragment0227158_field_001 fuel (fragment0227158Field002Chars00 ++ (fragment0227158Field003Chars00 ++ (fragment0227158Field004Chars00 ++ (fragment0227158Field005Chars00 ++ (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 346) (SourceJson.white (fragment0227158Field003Chars00 ++ (fragment0227158Field004Chars00 ++ (fragment0227158Field005Chars00 ++ (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail))))))))) fragment0227158Acc00300 := object_fragment0227158_field_002 fuel (fragment0227158Field003Chars00 ++ (fragment0227158Field004Chars00 ++ (fragment0227158Field005Chars00 ++ (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 345) (SourceJson.white (fragment0227158Field004Chars00 ++ (fragment0227158Field005Chars00 ++ (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail)))))))) fragment0227158Acc00400 := object_fragment0227158_field_003 fuel (fragment0227158Field004Chars00 ++ (fragment0227158Field005Chars00 ++ (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 344) (SourceJson.white (fragment0227158Field005Chars00 ++ (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail))))))) fragment0227158Acc00500 := object_fragment0227158_field_004 fuel (fragment0227158Field005Chars00 ++ (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 343) (SourceJson.white (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail)))))) fragment0227158Acc00600 := object_fragment0227158_field_005 fuel (fragment0227158Field006Chars00 ++ (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 342) (SourceJson.white (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail))))) fragment0227158Acc00700 := object_fragment0227158_field_006 fuel (fragment0227158Field007Chars00 ++ (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 341) (SourceJson.white (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail)))) fragment0227158Acc00800 := object_fragment0227158_field_007 fuel (fragment0227158Field008Chars00 ++ (fragment0227158Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 340) (SourceJson.white (fragment0227158Field009Chars00 ++ (tail))) fragment0227158Acc00900 := object_fragment0227158_field_008 fuel (fragment0227158Field009Chars00 ++ (tail))
    _ = .ok (fragment0227158Value, tail) := object_fragment0227158_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_before_reader"
  err.flush

noncomputable def chunk0000LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0000SuffixChars00 : List Char := [',']
noncomputable def chunk0000Chars00 : List Char := chunk0000LeadChars00 ++ fragment0225569Chars ++ chunk0000SuffixChars00
noncomputable def chunk0000Push00 (acc : List SourceJson) : List SourceJson := fragment0225569Value :: acc

noncomputable def chunk0000AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0000_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 604)
      (SourceJson.white (chunk0000LeadChars00 ++ (fragment0225569Chars ++ rest))) acc =
      (SourceJson.value (fuel + 603) (fragment0225569Chars ++ rest)).bind
        (chunk0000AfterValue00 (fuel + 603) acc) := by rfl

theorem array_chunk0000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 604) (SourceJson.white (chunk0000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 603) (SourceJson.white tail) (chunk0000Push00 acc) := by
  have hinput : chunk0000Chars00 ++ tail = chunk0000LeadChars00 ++ (fragment0225569Chars ++ (chunk0000SuffixChars00 ++ tail)) := by
    simp only [chunk0000Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 604) (SourceJson.white (chunk0000Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 604)
          (SourceJson.white (chunk0000LeadChars00 ++ (fragment0225569Chars ++ (chunk0000SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 604) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 603) (fragment0225569Chars ++ (chunk0000SuffixChars00 ++ tail))).bind
        (chunk0000AfterValue00 (fuel + 603) acc) := array_chunk0000_head fuel (chunk0000SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0225569Value, chunk0000SuffixChars00 ++ tail)).bind
        (chunk0000AfterValue00 (fuel + 603) acc) :=
      congrArg (fun result => result.bind (chunk0000AfterValue00 (fuel + 603) acc))
        (value_fragment0225569 (fuel + 371) (chunk0000SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 603) (SourceJson.white tail) (chunk0000Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_before_reader"
  err.flush

noncomputable def chunk0001LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0001SuffixChars00 : List Char := [',']
noncomputable def chunk0001Chars00 : List Char := chunk0001LeadChars00 ++ fragment0227158Chars ++ chunk0001SuffixChars00
noncomputable def chunk0001Push00 (acc : List SourceJson) : List SourceJson := fragment0227158Value :: acc

noncomputable def chunk0001AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0001_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 603)
      (SourceJson.white (chunk0001LeadChars00 ++ (fragment0227158Chars ++ rest))) acc =
      (SourceJson.value (fuel + 602) (fragment0227158Chars ++ rest)).bind
        (chunk0001AfterValue00 (fuel + 602) acc) := by rfl

theorem array_chunk0001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 603) (SourceJson.white (chunk0001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 602) (SourceJson.white tail) (chunk0001Push00 acc) := by
  have hinput : chunk0001Chars00 ++ tail = chunk0001LeadChars00 ++ (fragment0227158Chars ++ (chunk0001SuffixChars00 ++ tail)) := by
    simp only [chunk0001Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 603) (SourceJson.white (chunk0001Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 603)
          (SourceJson.white (chunk0001LeadChars00 ++ (fragment0227158Chars ++ (chunk0001SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 603) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 602) (fragment0227158Chars ++ (chunk0001SuffixChars00 ++ tail))).bind
        (chunk0001AfterValue00 (fuel + 602) acc) := array_chunk0001_head fuel (chunk0001SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0227158Value, chunk0001SuffixChars00 ++ tail)).bind
        (chunk0001AfterValue00 (fuel + 602) acc) :=
      congrArg (fun result => result.bind (chunk0001AfterValue00 (fuel + 602) acc))
        (value_fragment0227158 (fuel + 252) (chunk0001SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 602) (SourceJson.white tail) (chunk0001Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0000Chars00 ++ chunk0001Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0001Push00 (chunk0000Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 604) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 602) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0000Chars00 ++ (chunk0001Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 604) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 604) (SourceJson.white (chunk0000Chars00 ++ (chunk0001Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 604) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 603) (SourceJson.white (chunk0001Chars00 ++ (tail))) (chunk0000Push00 (acc)) := array_chunk0000 fuel (chunk0001Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 602) (SourceJson.white tail) (blockPush acc) := array_chunk0001 fuel (tail) (chunk0000Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 225563).take 3459 = blockChars := by rfl

theorem block_original_split : sourceRest 225563 = blockChars ++ sourceRest 229022 := by
  calc
    sourceRest 225563 = (sourceRest 225563).take 3459 ++ (sourceRest 225563).drop 3459 :=
      (List.take_append_drop 3459 (sourceRest 225563)).symm
    _ = blockChars ++ (sourceRest 225563).drop 3459 :=
      congrArg (fun part => part ++ (sourceRest 225563).drop 3459) block_original_prefix
    _ = blockChars ++ sourceRest 229022 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 225563 3459)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 604) (SourceJson.white (sourceRest 225563)) acc =
      SourceJson.array (fuel + 602) (SourceJson.white (sourceRest 229022)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 604) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 229022) acc)

#print axioms object_fragment0225569_field_000
#print axioms object_fragment0225569_field_001
#print axioms object_fragment0225569_field_002
#print axioms object_fragment0225569_field_003
#print axioms object_fragment0225569_field_004
#print axioms object_fragment0225569_field_005
#print axioms object_fragment0225569_field_006
#print axioms object_fragment0225569_field_007
#print axioms object_fragment0225569_field_008
#print axioms object_fragment0225569_field_009
#print axioms value_fragment0225569
#print axioms object_fragment0227158_field_000
#print axioms object_fragment0227158_field_001
#print axioms object_fragment0227158_field_002
#print axioms object_fragment0227158_field_003
#print axioms object_fragment0227158_field_004
#print axioms object_fragment0227158_field_005
#print axioms object_fragment0227158_field_006
#print axioms object_fragment0227158_field_007
#print axioms object_fragment0227158_field_008
#print axioms object_fragment0227158_field_009
#print axioms value_fragment0227158
#print axioms array_chunk0000_head
#print axioms array_chunk0000
#print axioms array_chunk0001_head
#print axioms array_chunk0001
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock000

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
