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

namespace SimplicesBlock064

noncomputable def fragment0440416Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0440416Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0440416Field000Value00 : SourceJson := .number (String.ofList ['1', '2', '6'])
noncomputable def fragment0440416Acc00100 : List (String × SourceJson) := (fragment0440416Field000Key00, fragment0440416Field000Value00) :: fragment0440416Acc00000
noncomputable def fragment0440416Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '6', ',']

theorem object_fragment0440416_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0440416Field000Chars00 ++ tail)) fragment0440416Acc00000 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0440416Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0440416_object_field_000"
  err.flush

noncomputable def fragment0440416Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0440416Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0440416Acc00200 : List (String × SourceJson) := (fragment0440416Field001Key00, fragment0440416Field001Value00) :: fragment0440416Acc00100
noncomputable def fragment0440416Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0440416_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0440416Field001Chars00 ++ tail)) fragment0440416Acc00100 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0440416Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0440416_object_field_001"
  err.flush

noncomputable def fragment0440416Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0440416Field002Value00 : SourceJson := .str (String.ofList ['1', '4', '4', '6', '2', '9', '6', '0', '3', '5', '4', '7', '2', '6', '5', '6', '0', '4', '7', '0', '5', '8', '2', '1', '5', '0', '7', '1', '8', '3', '3', '8', '4', '9', '3', '8', '4', '2', '1', '/', '8', '6', '1', '2', '7', '4', '2', '3', '8', '9', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0440416Acc00300 : List (String × SourceJson) := (fragment0440416Field002Key00, fragment0440416Field002Value00) :: fragment0440416Acc00200
noncomputable def fragment0440416Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '4', '4', '6', '2', '9', '6', '0', '3', '5', '4', '7', '2', '6', '5', '6', '0', '4', '7', '0', '5', '8', '2', '1', '5', '0', '7', '1', '8', '3', '3', '8', '4', '9', '3', '8', '4', '2', '1', '/', '8', '6', '1', '2', '7', '4', '2', '3', '8', '9', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0440416_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0440416Field002Chars00 ++ tail)) fragment0440416Acc00200 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0440416Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0440416_object_field_002"
  err.flush

noncomputable def fragment0440416Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0440416Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0440416Acc00400 : List (String × SourceJson) := (fragment0440416Field003Key00, fragment0440416Field003Value00) :: fragment0440416Acc00300
noncomputable def fragment0440416Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0440416_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0440416Field003Chars00 ++ tail)) fragment0440416Acc00300 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0440416Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0440416_object_field_003"
  err.flush

noncomputable def fragment0440416Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0440416Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0440416Acc00500 : List (String × SourceJson) := (fragment0440416Field004Key00, fragment0440416Field004Value00) :: fragment0440416Acc00400
noncomputable def fragment0440416Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0440416_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0440416Field004Chars00 ++ tail)) fragment0440416Acc00400 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0440416Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0440416_object_field_004"
  err.flush

noncomputable def fragment0440416Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0440416Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '5', '7', '5', '4', '8', '0', '9', '3', '0', '6', '3', '/', '3', '1', '5', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '3', '6', '9', '9', '8', '6', '8', '4', '1', '1', '/', '1', '5', '7', '8', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '3', '9', '9', '3', '1', '4', '5', '1', '9', '9', '/', '3', '6', '4', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '2', '3', '2', '2', '4', '5', '5', '4', '3', '8', '3', '/', '3', '9', '4', '7', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '3', '2', '9', '2', '4', '6', '7', '0', '7', '/', '4', '6', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '7', '8', '6', '0', '1', '9', '4', '7', '4', '8', '1', '/', '2', '3', '6', '8', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '6', '7', '6', '2', '9', '0', '9', '0', '4', '1', '/', '1', '2', '4', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '2', '2', '0', '3', '9', '1', '5', '5', '7', '5', '9', '/', '2', '3', '6', '8', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '6', '4', '9', '4', '7', '8', '6', '3', '9', '9', '5', '7', '/', '2', '3', '6', '8', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '6', '4', '9', '4', '6', '2', '8', '5', '1', '7', '1', '7', '/', '2', '3', '6', '8', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0440416Acc00600 : List (String × SourceJson) := (fragment0440416Field005Key00, fragment0440416Field005Value00) :: fragment0440416Acc00500
noncomputable def fragment0440416Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '7', '5', '4', '8', '0', '9', '3', '0', '6', '3', '/', '3', '1', '5', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '3', '6', '9', '9', '8', '6', '8', '4', '1', '1', '/', '1', '5', '7', '8', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '3', '9', '9', '3', '1', '4', '5', '1', '9', '9', '/', '3', '6', '4', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '2', '3', '2', '2', '4', '5', '5', '4', '3', '8', '3', '/', '3', '9', '4', '7', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '3', '2', '9', '2', '4', '6', '7', '0', '7', '/', '4', '6', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '7', '8', '6', '0', '1', '9', '4', '7', '4', '8', '1', '/', '2', '3', '6', '8', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '6', '7', '6', '2', '9', '0', '9', '0', '4', '1', '/', '1', '2', '4', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '2', '2', '0', '3', '9', '1', '5', '5', '7', '5', '9', '/', '2', '3', '6', '8', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '6', '4', '9', '4', '7', '8', '6', '3', '9', '9', '5', '7', '/', '2', '3', '6', '8', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '6', '4', '9', '4', '6', '2', '8', '5', '1', '7', '1', '7', '/', '2', '3', '6', '8', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0440416_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0440416Field005Chars00 ++ tail)) fragment0440416Acc00500 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0440416Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0440416_object_field_005"
  err.flush

noncomputable def fragment0440416Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0440416Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '4', '5', '1', '9', '0', '3', '9', '8', '7', '2', '1', '6', '1', '4', '2', '4', '5', '7', '0', '2', '5', '1', '7', '8', '4', '4', '9', '8', '0', '0', '0', '9', '8', '1', '9', '2', '1', '3', '5', '0', '7', '9', '5', '0', '0', '0', '/', '2', '8', '7', '4', '9', '9', '4', '2', '3', '3', '3', '9', '1', '1', '1', '8', '6', '2', '2', '6', '5', '2', '1', '5', '1', '1', '8', '4', '6', '3', '4', '1', '2', '9', '8', '2', '3', '3', '3', '9', '8', '8', '3', '7', '5', '6', '3', '4', '4', '0', '1', '5', '8', '6', '2', '3', '1', '6', '3', '6', '9', '7', '4', '3'])
noncomputable def fragment0440416Acc00700 : List (String × SourceJson) := (fragment0440416Field006Key00, fragment0440416Field006Value00) :: fragment0440416Acc00600
noncomputable def fragment0440416Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '4', '5', '1', '9', '0', '3', '9', '8', '7', '2', '1', '6', '1', '4', '2', '4', '5', '7', '0', '2', '5', '1', '7', '8', '4', '4', '9', '8', '0', '0', '0', '9', '8', '1', '9', '2', '1', '3', '5', '0', '7', '9', '5', '0', '0', '0', '/', '2', '8', '7', '4', '9', '9', '4', '2', '3', '3', '3', '9', '1', '1', '1', '8', '6', '2', '2', '6', '5', '2', '1', '5', '1', '1', '8', '4', '6', '3', '4', '1', '2', '9', '8', '2', '3', '3', '3', '9', '8', '8', '3', '7', '5', '6', '3', '4', '4', '0', '1', '5', '8', '6', '2', '3', '1', '6', '3', '6', '9', '7', '4', '3', '"', ',']

theorem object_fragment0440416_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0440416Field006Chars00 ++ tail)) fragment0440416Acc00600 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0440416Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0440416_object_field_006"
  err.flush

noncomputable def fragment0440416Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0440416Field007Value00 : SourceJson := .str (String.ofList ['1', '7', '6', '2', '4', '6', '4', '7', '6', '2', '3', '7', '9', '5', '4', '5', '5', '7', '5', '8', '9', '3', '7', '6', '5', '1', '3', '3', '8', '0', '6', '6', '5', '2', '6', '8', '0', '7', '3', '4', '7', '8', '7', '4', '8', '1', '4', '5', '0', '3', '2', '1', '9', '0', '0', '7', '1', '0', '3', '5', '0', '6', '0', '3', '7', '6', '8', '6', '1', '1', '3', '5', '5', '8', '4', '0', '5', '6', '2', '8', '7', '9', '2', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '8', '3', '4', '8', '1', '3', '3', '0', '0', '3', '4', '3', '9', '6', '4', '1', '1', '3', '1', '6', '4', '2', '7', '7', '9', '5', '7', '2', '2', '5', '8', '7', '4', '3', '9', '0', '6', '1', '6', '9', '8', '8', '6', '1', '2', '6', '0', '2', '3', '5', '4', '8', '5', '7', '4', '0', '2', '5', '5', '8', '0', '3', '6', '5', '4', '7', '3', '2', '3', '7', '1', '1', '0', '9', '9', '8', '9', '9', '5', '5', '8', '3', '4', '0', '8', '1', '2', '6', '6', '4', '6', '7', '9', '9', '9', '7', '2', '6', '8', '2', '5', '7', '1', '5', '2', '3', '7', '1', '6', '0', '5', '6', '8', '8', '5', '6', '7', '1', '1'])
noncomputable def fragment0440416Acc00800 : List (String × SourceJson) := (fragment0440416Field007Key00, fragment0440416Field007Value00) :: fragment0440416Acc00700
noncomputable def fragment0440416Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '7', '6', '2', '4', '6', '4', '7', '6', '2', '3', '7', '9', '5', '4', '5', '5', '7', '5', '8', '9', '3', '7', '6', '5', '1', '3', '3', '8', '0', '6', '6', '5', '2', '6', '8', '0', '7', '3', '4', '7', '8', '7', '4', '8', '1', '4', '5', '0', '3', '2', '1', '9', '0', '0', '7', '1', '0', '3', '5', '0', '6', '0', '3', '7', '6', '8', '6', '1', '1', '3', '5', '5', '8', '4', '0', '5', '6', '2', '8', '7', '9', '2', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '8', '3', '4', '8', '1', '3', '3', '0', '0', '3', '4', '3', '9', '6', '4', '1', '1', '3', '1', '6', '4', '2', '7', '7', '9', '5', '7', '2', '2', '5', '8', '7', '4', '3', '9', '0', '6', '1', '6', '9', '8', '8', '6', '1', '2', '6', '0', '2', '3', '5', '4', '8', '5', '7', '4', '0', '2', '5', '5', '8', '0', '3', '6', '5', '4', '7', '3', '2', '3', '7', '1', '1', '0', '9', '9', '8', '9', '9', '5', '5', '8', '3', '4', '0', '8', '1', '2', '6', '6', '4', '6', '7', '9', '9', '9', '7', '2', '6', '8', '2', '5', '7', '1', '5', '2', '3', '7', '1', '6', '0', '5', '6', '8', '8', '5', '6', '7', '1', '1', '"', ',']

theorem object_fragment0440416_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0440416Field007Chars00 ++ tail)) fragment0440416Acc00700 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0440416Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0440416_object_field_007"
  err.flush

noncomputable def fragment0440416Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0440416Field008Value00 : SourceJson := .str (String.ofList ['5', '0', '8', '4', '9', '1', '6', '1', '0', '4', '5', '8', '7'])
noncomputable def fragment0440416Acc00900 : List (String × SourceJson) := (fragment0440416Field008Key00, fragment0440416Field008Value00) :: fragment0440416Acc00800
noncomputable def fragment0440416Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '0', '8', '4', '9', '1', '6', '1', '0', '4', '5', '8', '7', '"', ',']

theorem object_fragment0440416_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0440416Field008Chars00 ++ tail)) fragment0440416Acc00800 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0440416Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0440416_object_field_008"
  err.flush

noncomputable def fragment0440416Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0440416Field009Value00 : SourceJson := .str (String.ofList ['4', '9', '2', '5', '7', '8', '6', '2', '8', '0', '2', '6', '5', '0'])
noncomputable def fragment0440416Acc01000 : List (String × SourceJson) := (fragment0440416Field009Key00, fragment0440416Field009Value00) :: fragment0440416Acc00900
noncomputable def fragment0440416Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '9', '2', '5', '7', '8', '6', '2', '8', '0', '2', '6', '5', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0440416_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0440416Field009Chars00 ++ tail)) fragment0440416Acc00900 =
      .ok (.obj (fragment0440416Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0440416_object_field_009"
  err.flush

noncomputable def fragment0440416Chars : List Char := '{' :: (fragment0440416Field000Chars00 ++ fragment0440416Field001Chars00 ++ fragment0440416Field002Chars00 ++ fragment0440416Field003Chars00 ++ fragment0440416Field004Chars00 ++ fragment0440416Field005Chars00 ++ fragment0440416Field006Chars00 ++ fragment0440416Field007Chars00 ++ fragment0440416Field008Chars00 ++ fragment0440416Field009Chars00)
noncomputable def fragment0440416Value : SourceJson := .obj (fragment0440416Acc01000.reverse)

theorem value_fragment0440416 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 237) (fragment0440416Chars ++ tail) =
      .ok (fragment0440416Value, tail) := by
  have hinput : fragment0440416Chars ++ tail = '{' :: (fragment0440416Field000Chars00 ++ (fragment0440416Field001Chars00 ++ (fragment0440416Field002Chars00 ++ (fragment0440416Field003Chars00 ++ (fragment0440416Field004Chars00 ++ (fragment0440416Field005Chars00 ++ (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0440416Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 237) (fragment0440416Chars ++ tail) =
        SourceJson.value (fuel + 237) ('{' :: (fragment0440416Field000Chars00 ++ (fragment0440416Field001Chars00 ++ (fragment0440416Field002Chars00 ++ (fragment0440416Field003Chars00 ++ (fragment0440416Field004Chars00 ++ (fragment0440416Field005Chars00 ++ (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 237)) hinput
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0440416Field000Chars00 ++ (fragment0440416Field001Chars00 ++ (fragment0440416Field002Chars00 ++ (fragment0440416Field003Chars00 ++ (fragment0440416Field004Chars00 ++ (fragment0440416Field005Chars00 ++ (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail)))))))))))) fragment0440416Acc00000 := by rfl
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0440416Field001Chars00 ++ (fragment0440416Field002Chars00 ++ (fragment0440416Field003Chars00 ++ (fragment0440416Field004Chars00 ++ (fragment0440416Field005Chars00 ++ (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail))))))))))) fragment0440416Acc00100 := object_fragment0440416_field_000 fuel (fragment0440416Field001Chars00 ++ (fragment0440416Field002Chars00 ++ (fragment0440416Field003Chars00 ++ (fragment0440416Field004Chars00 ++ (fragment0440416Field005Chars00 ++ (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0440416Field002Chars00 ++ (fragment0440416Field003Chars00 ++ (fragment0440416Field004Chars00 ++ (fragment0440416Field005Chars00 ++ (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail)))))))))) fragment0440416Acc00200 := object_fragment0440416_field_001 fuel (fragment0440416Field002Chars00 ++ (fragment0440416Field003Chars00 ++ (fragment0440416Field004Chars00 ++ (fragment0440416Field005Chars00 ++ (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0440416Field003Chars00 ++ (fragment0440416Field004Chars00 ++ (fragment0440416Field005Chars00 ++ (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail))))))))) fragment0440416Acc00300 := object_fragment0440416_field_002 fuel (fragment0440416Field003Chars00 ++ (fragment0440416Field004Chars00 ++ (fragment0440416Field005Chars00 ++ (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0440416Field004Chars00 ++ (fragment0440416Field005Chars00 ++ (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail)))))))) fragment0440416Acc00400 := object_fragment0440416_field_003 fuel (fragment0440416Field004Chars00 ++ (fragment0440416Field005Chars00 ++ (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0440416Field005Chars00 ++ (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail))))))) fragment0440416Acc00500 := object_fragment0440416_field_004 fuel (fragment0440416Field005Chars00 ++ (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail)))))) fragment0440416Acc00600 := object_fragment0440416_field_005 fuel (fragment0440416Field006Chars00 ++ (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail))))) fragment0440416Acc00700 := object_fragment0440416_field_006 fuel (fragment0440416Field007Chars00 ++ (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail)))) fragment0440416Acc00800 := object_fragment0440416_field_007 fuel (fragment0440416Field008Chars00 ++ (fragment0440416Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0440416Field009Chars00 ++ (tail))) fragment0440416Acc00900 := object_fragment0440416_field_008 fuel (fragment0440416Field009Chars00 ++ (tail))
    _ = .ok (fragment0440416Value, tail) := object_fragment0440416_field_009 fuel (tail)

noncomputable def fragment0442020Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0442020Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0442020Field000Value00 : SourceJson := .number (String.ofList ['1', '2', '7'])
noncomputable def fragment0442020Acc00100 : List (String × SourceJson) := (fragment0442020Field000Key00, fragment0442020Field000Value00) :: fragment0442020Acc00000
noncomputable def fragment0442020Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '7', ',']

theorem object_fragment0442020_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 379) (SourceJson.white (fragment0442020Field000Chars00 ++ tail)) fragment0442020Acc00000 =
      SourceJson.object (fuel + 378) (SourceJson.white tail) fragment0442020Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0442020_object_field_000"
  err.flush

noncomputable def fragment0442020Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0442020Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0442020Acc00200 : List (String × SourceJson) := (fragment0442020Field001Key00, fragment0442020Field001Value00) :: fragment0442020Acc00100
noncomputable def fragment0442020Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0442020_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 378) (SourceJson.white (fragment0442020Field001Chars00 ++ tail)) fragment0442020Acc00100 =
      SourceJson.object (fuel + 377) (SourceJson.white tail) fragment0442020Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0442020_object_field_001"
  err.flush

noncomputable def fragment0442020Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0442020Field002Value00 : SourceJson := .str (String.ofList ['5', '6', '2', '1', '0', '3', '5', '7', '6', '8', '8', '8', '3', '6', '9', '8', '9', '2', '9', '0', '8', '5', '2', '2', '0', '9', '1', '2', '3', '3', '5', '1', '3', '2', '1', '7', '6', '4', '6', '8', '1', '/', '1', '6', '8', '4', '6', '5', '2', '4', '1', '1', '4', '3', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0442020Acc00300 : List (String × SourceJson) := (fragment0442020Field002Key00, fragment0442020Field002Value00) :: fragment0442020Acc00200
noncomputable def fragment0442020Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '6', '2', '1', '0', '3', '5', '7', '6', '8', '8', '8', '3', '6', '9', '8', '9', '2', '9', '0', '8', '5', '2', '2', '0', '9', '1', '2', '3', '3', '5', '1', '3', '2', '1', '7', '6', '4', '6', '8', '1', '/', '1', '6', '8', '4', '6', '5', '2', '4', '1', '1', '4', '3', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0442020_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 377) (SourceJson.white (fragment0442020Field002Chars00 ++ tail)) fragment0442020Acc00200 =
      SourceJson.object (fuel + 376) (SourceJson.white tail) fragment0442020Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0442020_object_field_002"
  err.flush

noncomputable def fragment0442020Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0442020Field003Value00 : SourceJson := .str (String.ofList ['6', '6', '3', '6', '9', '1', '0', '9', '/', '9', '9', '7', '5', '6', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0442020Acc00400 : List (String × SourceJson) := (fragment0442020Field003Key00, fragment0442020Field003Value00) :: fragment0442020Acc00300
noncomputable def fragment0442020Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '6', '3', '6', '9', '1', '0', '9', '/', '9', '9', '7', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0442020_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 376) (SourceJson.white (fragment0442020Field003Chars00 ++ tail)) fragment0442020Acc00300 =
      SourceJson.object (fuel + 375) (SourceJson.white tail) fragment0442020Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0442020_object_field_003"
  err.flush

noncomputable def fragment0442020Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0442020Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '7', '/', '2', '0', '8', '6', '4']), .str (String.ofList ['9', '5', '7', '/', '2', '0', '8', '6', '4'])]
noncomputable def fragment0442020Acc00500 : List (String × SourceJson) := (fragment0442020Field004Key00, fragment0442020Field004Value00) :: fragment0442020Acc00400
noncomputable def fragment0442020Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '/', '2', '0', '8', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '/', '2', '0', '8', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0442020_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 375) (SourceJson.white (fragment0442020Field004Chars00 ++ tail)) fragment0442020Acc00400 =
      SourceJson.object (fuel + 374) (SourceJson.white tail) fragment0442020Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0442020_object_field_004"
  err.flush

noncomputable def fragment0442020Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0442020Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '4', '2', '4', '5', '3', '1', '4', '0', '3', '6', '3', '8', '3', '2', '7', '0', '7', '3', '/', '1', '8', '1', '9', '7', '2', '9', '1', '8', '9', '2', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '4', '2', '5', '6', '5', '9', '7', '2', '5', '9', '8', '5', '0', '0', '7', '6', '2', '9', '/', '3', '4', '5', '7', '4', '8', '5', '4', '5', '9', '5', '3', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '7', '2', '4', '9', '1', '5', '2', '4', '6', '2', '9', '8', '3', '1', '0', '9', '8', '1', '/', '8', '6', '4', '3', '7', '1', '3', '6', '4', '8', '8', '3', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '2', '0', '8', '1', '9', '4', '2', '5', '2', '2', '5', '2', '2', '9', '7', '4', '1', '/', '2', '1', '6', '0', '9', '2', '8', '4', '1', '2', '2', '0', '8', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '4', '6', '8', '1', '0', '0', '6', '7', '7', '6', '1', '6', '3', '0', '0', '5', '9', '/', '1', '5', '2', '5', '3', '6', '1', '2', '3', '2', '1', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '6', '6', '1', '8', '8', '6', '1', '9', '6', '6', '7', '7', '8', '2', '5', '4', '3', '3', '/', '8', '6', '4', '3', '7', '1', '3', '6', '4', '8', '8', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '4', '4', '1', '1', '1', '3', '2', '1', '7', '5', '6', '6', '0', '4', '7', '5', '4', '7', '/', '5', '1', '8', '6', '2', '2', '8', '1', '8', '9', '2', '9', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '3', '6', '7', '1', '8', '3', '5', '6', '8', '9', '4', '2', '9', '9', '5', '7', '9', '3', '7', '/', '5', '1', '8', '6', '2', '2', '8', '1', '8', '9', '2', '9', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '7', '2', '4', '1', '0', '7', '3', '1', '0', '3', '9', '0', '1', '8', '6', '9', '0', '7', '/', '6', '4', '8', '2', '7', '8', '5', '2', '3', '6', '6', '2', '4', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '2', '0', '6', '7', '7', '3', '4', '8', '6', '3', '6', '9', '9', '0', '4', '5', '7', '/', '1', '0', '8', '0', '4', '6', '4', '2', '0', '6', '1', '0', '4', '1', '2', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0442020Acc00600 : List (String × SourceJson) := (fragment0442020Field005Key00, fragment0442020Field005Value00) :: fragment0442020Acc00500
noncomputable def fragment0442020Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '4', '5', '3', '1', '4', '0', '3', '6', '3', '8', '3', '2', '7', '0', '7', '3', '/', '1', '8', '1', '9', '7', '2', '9', '1', '8', '9', '2', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '4', '2', '5', '6', '5', '9', '7', '2', '5', '9', '8', '5', '0', '0', '7', '6', '2', '9', '/', '3', '4', '5', '7', '4', '8', '5', '4', '5', '9', '5', '3', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '2', '4', '9', '1', '5', '2', '4', '6', '2', '9', '8', '3', '1', '0', '9', '8', '1', '/', '8', '6', '4', '3', '7', '1', '3', '6', '4', '8', '8', '3', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '2', '0', '8', '1', '9', '4', '2', '5', '2', '2', '5', '2', '2', '9', '7', '4', '1', '/', '2', '1', '6', '0', '9', '2', '8', '4', '1', '2', '2', '0', '8', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '4', '6', '8', '1', '0', '0', '6', '7', '7', '6', '1', '6', '3', '0', '0', '5', '9', '/', '1', '5', '2', '5', '3', '6', '1', '2', '3', '2', '1', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '6', '6', '1', '8', '8', '6', '1', '9', '6', '6', '7', '7', '8', '2', '5', '4', '3', '3', '/', '8', '6', '4', '3', '7', '1', '3', '6', '4', '8', '8', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '4', '4', '1', '1', '1', '3', '2', '1', '7', '5', '6', '6', '0', '4', '7', '5', '4', '7', '/', '5', '1', '8', '6', '2', '2', '8', '1', '8', '9', '2', '9', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '6', '7', '1', '8', '3', '5', '6', '8', '9', '4', '2', '9', '9', '5', '7', '9', '3', '7', '/', '5', '1', '8', '6', '2', '2', '8', '1', '8', '9', '2', '9', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '7', '2', '4', '1', '0', '7', '3', '1', '0', '3', '9', '0', '1', '8', '6', '9', '0', '7', '/', '6', '4', '8', '2', '7', '8', '5', '2', '3', '6', '6', '2', '4', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '2', '0', '6', '7', '7', '3', '4', '8', '6', '3', '6', '9', '9', '0', '4', '5', '7', '/', '1', '0', '8', '0', '4', '6', '4', '2', '0', '6', '1', '0', '4', '1', '2', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0442020_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 374) (SourceJson.white (fragment0442020Field005Chars00 ++ tail)) fragment0442020Acc00500 =
      SourceJson.object (fuel + 373) (SourceJson.white tail) fragment0442020Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0442020_object_field_005"
  err.flush

noncomputable def fragment0442020Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0442020Field006Value00 : SourceJson := .str (String.ofList ['7', '0', '5', '2', '8', '4', '5', '3', '9', '0', '4', '0', '6', '2', '1', '5', '6', '1', '7', '9', '7', '3', '2', '3', '3', '4', '9', '0', '8', '0', '2', '0', '8', '0', '2', '5', '6', '7', '7', '2', '2', '2', '4', '5', '9', '8', '8', '8', '/', '4', '7', '4', '8', '5', '1', '2', '0', '3', '6', '9', '8', '3', '1', '6', '6', '0', '1', '8', '0', '7', '7', '7', '3', '0', '2', '4', '2', '4', '8', '4', '4', '1', '7', '3', '9', '5', '6', '8', '2', '9', '6', '4', '4', '6', '7', '6', '9', '1', '4', '1', '4', '6', '0', '0', '8', '5', '0', '5', '8', '5', '9', '3', '7', '5'])
noncomputable def fragment0442020Acc00700 : List (String × SourceJson) := (fragment0442020Field006Key00, fragment0442020Field006Value00) :: fragment0442020Acc00600
noncomputable def fragment0442020Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '0', '5', '2', '8', '4', '5', '3', '9', '0', '4', '0', '6', '2', '1', '5', '6', '1', '7', '9', '7', '3', '2', '3', '3', '4', '9', '0', '8', '0', '2', '0', '8', '0', '2', '5', '6', '7', '7', '2', '2', '2', '4', '5', '9', '8', '8', '8', '/', '4', '7', '4', '8', '5', '1', '2', '0', '3', '6', '9', '8', '3', '1', '6', '6', '0', '1', '8', '0', '7', '7', '7', '3', '0', '2', '4', '2', '4', '8', '4', '4', '1', '7', '3', '9', '5', '6', '8', '2', '9', '6', '4', '4', '6', '7', '6', '9', '1', '4', '1', '4', '6', '0', '0', '8', '5', '0', '5', '8', '5', '9', '3', '7', '5', '"', ',']

theorem object_fragment0442020_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 373) (SourceJson.white (fragment0442020Field006Chars00 ++ tail)) fragment0442020Acc00600 =
      SourceJson.object (fuel + 372) (SourceJson.white tail) fragment0442020Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0442020_object_field_006"
  err.flush

noncomputable def fragment0442020Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0442020Field007Value00 : SourceJson := .str (String.ofList ['9', '8', '2', '8', '0', '0', '1', '3', '2', '1', '9', '6', '0', '4', '6', '4', '8', '7', '5', '0', '5', '8', '1', '9', '1', '9', '2', '8', '1', '1', '9', '2', '6', '1', '8', '2', '7', '9', '1', '0', '1', '9', '6', '3', '4', '8', '9', '5', '9', '4', '6', '7', '6', '9', '8', '7', '8', '0', '7', '8', '5', '7', '6', '8', '5', '6', '8', '1', '9', '2', '2', '5', '6', '1', '0', '3', '6', '3', '8', '6', '4', '1', '1', '2', '1', '2', '9', '2', '5', '8', '7', '2', '4', '1', '7', '5', '8', '1', '5', '5', '2', '9', '2', '1', '4', '4', '3', '8', '3', '7', '6', '3', '2', '1', '9', '4', '1', '2', '0', '5', '6', '4', '9', '3', '7', '3', '6', '2', '8', '8', '3', '7', '1', '5', '6', '2', '2', '9', '8', '9', '3', '3', '1', '5', '5', '4', '4', '3', '5', '4', '8', '4', '3', '0', '8', '1', '2', '3', '3', '1', '8', '4', '8', '1', '4', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '/', '6', '8', '8', '2', '4', '9', '3', '5', '3', '3', '2', '3', '5', '2', '4', '0', '7', '6', '9', '3', '5', '6', '9', '9', '1', '2', '0', '1', '8', '1', '0', '5', '2', '5', '7', '7', '8', '1', '8', '9', '5', '9', '6', '5', '1', '0', '7', '2', '6', '8', '0', '9', '5', '0', '0', '7', '9', '0', '7', '3', '3', '2', '7', '3', '0', '3', '0', '1', '8', '8', '3', '3', '6', '9', '9', '3', '7', '8', '8', '5', '9', '0', '8', '5', '4', '4', '5', '0', '4', '3', '8', '4', '9', '8', '1', '8', '3', '4', '6', '7', '9', '8', '0', '2', '4', '0', '3', '9', '7', '6', '7', '0', '2', '8', '4', '0', '7', '6', '7', '2', '7', '5', '9', '8', '7', '8', '3', '1', '0', '7', '4', '0', '0', '4', '1', '0', '3', '0', '7', '6', '2', '5', '2', '0', '7', '7', '0', '1', '6', '4', '2', '8', '2', '0', '5', '6', '4', '7', '7', '9', '2', '5', '7', '0', '5', '9', '8', '4', '9', '6', '5', '0', '1', '6', '5', '4', '0', '3', '7', '8', '4', '9', '4', '7', '1', '6', '2', '5', '9', '2', '1', '3'])
noncomputable def fragment0442020Acc00800 : List (String × SourceJson) := (fragment0442020Field007Key00, fragment0442020Field007Value00) :: fragment0442020Acc00700
noncomputable def fragment0442020Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '8', '2', '8', '0', '0', '1', '3', '2', '1', '9', '6', '0', '4', '6', '4', '8', '7', '5', '0', '5', '8', '1', '9', '1', '9', '2', '8', '1', '1', '9', '2', '6', '1', '8', '2', '7', '9', '1', '0', '1', '9', '6', '3', '4', '8', '9', '5', '9', '4', '6', '7', '6', '9', '8', '7', '8', '0', '7', '8', '5', '7', '6', '8', '5', '6', '8', '1', '9', '2', '2', '5', '6', '1', '0', '3', '6', '3', '8', '6', '4', '1', '1', '2', '1', '2', '9', '2', '5', '8', '7', '2', '4', '1', '7', '5', '8', '1', '5', '5', '2', '9', '2', '1', '4', '4', '3', '8', '3', '7', '6', '3', '2', '1', '9', '4', '1', '2', '0', '5', '6', '4', '9', '3', '7', '3', '6', '2', '8', '8', '3', '7', '1', '5', '6', '2', '2', '9', '8', '9', '3', '3', '1', '5', '5', '4', '4', '3', '5', '4', '8', '4', '3', '0', '8', '1', '2', '3', '3', '1', '8', '4', '8', '1', '4', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '/', '6', '8', '8', '2', '4', '9', '3', '5', '3', '3', '2', '3', '5', '2', '4', '0', '7', '6', '9', '3', '5', '6', '9', '9', '1', '2', '0', '1', '8', '1', '0', '5', '2', '5', '7', '7', '8', '1', '8', '9', '5', '9', '6', '5', '1', '0', '7', '2', '6', '8', '0', '9', '5', '0', '0', '7', '9', '0', '7', '3', '3', '2', '7', '3', '0', '3', '0', '1', '8', '8', '3', '3', '6', '9', '9', '3', '7', '8', '8', '5', '9', '0', '8', '5', '4', '4', '5', '0', '4', '3', '8', '4', '9', '8', '1', '8', '3', '4', '6', '7', '9', '8', '0', '2', '4', '0', '3', '9', '7', '6', '7', '0', '2', '8', '4', '0', '7', '6', '7', '2', '7', '5', '9', '8', '7', '8', '3', '1', '0', '7', '4', '0', '0', '4', '1', '0', '3', '0', '7', '6', '2', '5', '2', '0', '7', '7', '0', '1', '6', '4', '2', '8', '2', '0', '5', '6', '4', '7', '7', '9', '2', '5', '7', '0', '5', '9', '8', '4', '9', '6', '5', '0', '1', '6', '5', '4', '0', '3', '7', '8', '4', '9', '4', '7', '1', '6', '2', '5', '9', '2', '1', '3', '"', ',']

theorem object_fragment0442020_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 372) (SourceJson.white (fragment0442020Field007Chars00 ++ tail)) fragment0442020Acc00700 =
      SourceJson.object (fuel + 371) (SourceJson.white tail) fragment0442020Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0442020_object_field_007"
  err.flush

noncomputable def fragment0442020Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0442020Field008Value00 : SourceJson := .str (String.ofList ['1', '1', '7', '6', '7', '5', '5', '9', '5', '3', '0', '7', '9'])
noncomputable def fragment0442020Acc00900 : List (String × SourceJson) := (fragment0442020Field008Key00, fragment0442020Field008Value00) :: fragment0442020Acc00800
noncomputable def fragment0442020Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '7', '6', '7', '5', '5', '9', '5', '3', '0', '7', '9', '"', ',']

theorem object_fragment0442020_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 371) (SourceJson.white (fragment0442020Field008Chars00 ++ tail)) fragment0442020Acc00800 =
      SourceJson.object (fuel + 370) (SourceJson.white tail) fragment0442020Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0442020_object_field_008"
  err.flush

noncomputable def fragment0442020Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0442020Field009Value00 : SourceJson := .str (String.ofList ['1', '1', '3', '1', '3', '5', '5', '2', '0', '1', '6', '6', '7', '2'])
noncomputable def fragment0442020Acc01000 : List (String × SourceJson) := (fragment0442020Field009Key00, fragment0442020Field009Value00) :: fragment0442020Acc00900
noncomputable def fragment0442020Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '3', '1', '3', '5', '5', '2', '0', '1', '6', '6', '7', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0442020_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 370) (SourceJson.white (fragment0442020Field009Chars00 ++ tail)) fragment0442020Acc00900 =
      .ok (.obj (fragment0442020Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0442020_object_field_009"
  err.flush

noncomputable def fragment0442020Chars : List Char := '{' :: (fragment0442020Field000Chars00 ++ fragment0442020Field001Chars00 ++ fragment0442020Field002Chars00 ++ fragment0442020Field003Chars00 ++ fragment0442020Field004Chars00 ++ fragment0442020Field005Chars00 ++ fragment0442020Field006Chars00 ++ fragment0442020Field007Chars00 ++ fragment0442020Field008Chars00 ++ fragment0442020Field009Chars00)
noncomputable def fragment0442020Value : SourceJson := .obj (fragment0442020Acc01000.reverse)

theorem value_fragment0442020 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 380) (fragment0442020Chars ++ tail) =
      .ok (fragment0442020Value, tail) := by
  have hinput : fragment0442020Chars ++ tail = '{' :: (fragment0442020Field000Chars00 ++ (fragment0442020Field001Chars00 ++ (fragment0442020Field002Chars00 ++ (fragment0442020Field003Chars00 ++ (fragment0442020Field004Chars00 ++ (fragment0442020Field005Chars00 ++ (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0442020Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 380) (fragment0442020Chars ++ tail) =
        SourceJson.value (fuel + 380) ('{' :: (fragment0442020Field000Chars00 ++ (fragment0442020Field001Chars00 ++ (fragment0442020Field002Chars00 ++ (fragment0442020Field003Chars00 ++ (fragment0442020Field004Chars00 ++ (fragment0442020Field005Chars00 ++ (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 380)) hinput
    _ = SourceJson.object (fuel + 379) (SourceJson.white (fragment0442020Field000Chars00 ++ (fragment0442020Field001Chars00 ++ (fragment0442020Field002Chars00 ++ (fragment0442020Field003Chars00 ++ (fragment0442020Field004Chars00 ++ (fragment0442020Field005Chars00 ++ (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail)))))))))))) fragment0442020Acc00000 := by rfl
    _ = SourceJson.object (fuel + 378) (SourceJson.white (fragment0442020Field001Chars00 ++ (fragment0442020Field002Chars00 ++ (fragment0442020Field003Chars00 ++ (fragment0442020Field004Chars00 ++ (fragment0442020Field005Chars00 ++ (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail))))))))))) fragment0442020Acc00100 := object_fragment0442020_field_000 fuel (fragment0442020Field001Chars00 ++ (fragment0442020Field002Chars00 ++ (fragment0442020Field003Chars00 ++ (fragment0442020Field004Chars00 ++ (fragment0442020Field005Chars00 ++ (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 377) (SourceJson.white (fragment0442020Field002Chars00 ++ (fragment0442020Field003Chars00 ++ (fragment0442020Field004Chars00 ++ (fragment0442020Field005Chars00 ++ (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail)))))))))) fragment0442020Acc00200 := object_fragment0442020_field_001 fuel (fragment0442020Field002Chars00 ++ (fragment0442020Field003Chars00 ++ (fragment0442020Field004Chars00 ++ (fragment0442020Field005Chars00 ++ (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 376) (SourceJson.white (fragment0442020Field003Chars00 ++ (fragment0442020Field004Chars00 ++ (fragment0442020Field005Chars00 ++ (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail))))))))) fragment0442020Acc00300 := object_fragment0442020_field_002 fuel (fragment0442020Field003Chars00 ++ (fragment0442020Field004Chars00 ++ (fragment0442020Field005Chars00 ++ (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 375) (SourceJson.white (fragment0442020Field004Chars00 ++ (fragment0442020Field005Chars00 ++ (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail)))))))) fragment0442020Acc00400 := object_fragment0442020_field_003 fuel (fragment0442020Field004Chars00 ++ (fragment0442020Field005Chars00 ++ (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 374) (SourceJson.white (fragment0442020Field005Chars00 ++ (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail))))))) fragment0442020Acc00500 := object_fragment0442020_field_004 fuel (fragment0442020Field005Chars00 ++ (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 373) (SourceJson.white (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail)))))) fragment0442020Acc00600 := object_fragment0442020_field_005 fuel (fragment0442020Field006Chars00 ++ (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 372) (SourceJson.white (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail))))) fragment0442020Acc00700 := object_fragment0442020_field_006 fuel (fragment0442020Field007Chars00 ++ (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 371) (SourceJson.white (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail)))) fragment0442020Acc00800 := object_fragment0442020_field_007 fuel (fragment0442020Field008Chars00 ++ (fragment0442020Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 370) (SourceJson.white (fragment0442020Field009Chars00 ++ (tail))) fragment0442020Acc00900 := object_fragment0442020_field_008 fuel (fragment0442020Field009Chars00 ++ (tail))
    _ = .ok (fragment0442020Value, tail) := object_fragment0442020_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0126_before_reader"
  err.flush

noncomputable def chunk0126LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0126SuffixChars00 : List Char := [',']
noncomputable def chunk0126Chars00 : List Char := chunk0126LeadChars00 ++ fragment0440416Chars ++ chunk0126SuffixChars00
noncomputable def chunk0126Push00 (acc : List SourceJson) : List SourceJson := fragment0440416Value :: acc

noncomputable def chunk0126AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0126_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 478)
      (SourceJson.white (chunk0126LeadChars00 ++ (fragment0440416Chars ++ rest))) acc =
      (SourceJson.value (fuel + 477) (fragment0440416Chars ++ rest)).bind
        (chunk0126AfterValue00 (fuel + 477) acc) := by rfl

theorem array_chunk0126 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 478) (SourceJson.white (chunk0126Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 477) (SourceJson.white tail) (chunk0126Push00 acc) := by
  have hinput : chunk0126Chars00 ++ tail = chunk0126LeadChars00 ++ (fragment0440416Chars ++ (chunk0126SuffixChars00 ++ tail)) := by
    simp only [chunk0126Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 478) (SourceJson.white (chunk0126Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 478)
          (SourceJson.white (chunk0126LeadChars00 ++ (fragment0440416Chars ++ (chunk0126SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 478) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 477) (fragment0440416Chars ++ (chunk0126SuffixChars00 ++ tail))).bind
        (chunk0126AfterValue00 (fuel + 477) acc) := array_chunk0126_head fuel (chunk0126SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0440416Value, chunk0126SuffixChars00 ++ tail)).bind
        (chunk0126AfterValue00 (fuel + 477) acc) :=
      congrArg (fun result => result.bind (chunk0126AfterValue00 (fuel + 477) acc))
        (value_fragment0440416 (fuel + 240) (chunk0126SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 477) (SourceJson.white tail) (chunk0126Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0126_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0127_before_reader"
  err.flush

noncomputable def chunk0127LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0127SuffixChars00 : List Char := [',']
noncomputable def chunk0127Chars00 : List Char := chunk0127LeadChars00 ++ fragment0442020Chars ++ chunk0127SuffixChars00
noncomputable def chunk0127Push00 (acc : List SourceJson) : List SourceJson := fragment0442020Value :: acc

noncomputable def chunk0127AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0127_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 477)
      (SourceJson.white (chunk0127LeadChars00 ++ (fragment0442020Chars ++ rest))) acc =
      (SourceJson.value (fuel + 476) (fragment0442020Chars ++ rest)).bind
        (chunk0127AfterValue00 (fuel + 476) acc) := by rfl

theorem array_chunk0127 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 477) (SourceJson.white (chunk0127Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 476) (SourceJson.white tail) (chunk0127Push00 acc) := by
  have hinput : chunk0127Chars00 ++ tail = chunk0127LeadChars00 ++ (fragment0442020Chars ++ (chunk0127SuffixChars00 ++ tail)) := by
    simp only [chunk0127Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 477) (SourceJson.white (chunk0127Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 477)
          (SourceJson.white (chunk0127LeadChars00 ++ (fragment0442020Chars ++ (chunk0127SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 477) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 476) (fragment0442020Chars ++ (chunk0127SuffixChars00 ++ tail))).bind
        (chunk0127AfterValue00 (fuel + 476) acc) := array_chunk0127_head fuel (chunk0127SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0442020Value, chunk0127SuffixChars00 ++ tail)).bind
        (chunk0127AfterValue00 (fuel + 476) acc) :=
      congrArg (fun result => result.bind (chunk0127AfterValue00 (fuel + 476) acc))
        (value_fragment0442020 (fuel + 96) (chunk0127SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 476) (SourceJson.white tail) (chunk0127Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0127_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0126Chars00 ++ chunk0127Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0127Push00 (chunk0126Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 478) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 476) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0126Chars00 ++ (chunk0127Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 478) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 478) (SourceJson.white (chunk0126Chars00 ++ (chunk0127Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 478) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 477) (SourceJson.white (chunk0127Chars00 ++ (tail))) (chunk0126Push00 (acc)) := array_chunk0126 fuel (chunk0127Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 476) (SourceJson.white tail) (blockPush acc) := array_chunk0127 fuel (tail) (chunk0126Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 440410).take 3489 = blockChars := by rfl

theorem block_original_split : sourceRest 440410 = blockChars ++ sourceRest 443899 := by
  calc
    sourceRest 440410 = (sourceRest 440410).take 3489 ++ (sourceRest 440410).drop 3489 :=
      (List.take_append_drop 3489 (sourceRest 440410)).symm
    _ = blockChars ++ (sourceRest 440410).drop 3489 :=
      congrArg (fun part => part ++ (sourceRest 440410).drop 3489) block_original_prefix
    _ = blockChars ++ sourceRest 443899 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 440410 3489)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 478) (SourceJson.white (sourceRest 440410)) acc =
      SourceJson.array (fuel + 476) (SourceJson.white (sourceRest 443899)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 478) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 443899) acc)

#print axioms object_fragment0440416_field_000
#print axioms object_fragment0440416_field_001
#print axioms object_fragment0440416_field_002
#print axioms object_fragment0440416_field_003
#print axioms object_fragment0440416_field_004
#print axioms object_fragment0440416_field_005
#print axioms object_fragment0440416_field_006
#print axioms object_fragment0440416_field_007
#print axioms object_fragment0440416_field_008
#print axioms object_fragment0440416_field_009
#print axioms value_fragment0440416
#print axioms object_fragment0442020_field_000
#print axioms object_fragment0442020_field_001
#print axioms object_fragment0442020_field_002
#print axioms object_fragment0442020_field_003
#print axioms object_fragment0442020_field_004
#print axioms object_fragment0442020_field_005
#print axioms object_fragment0442020_field_006
#print axioms object_fragment0442020_field_007
#print axioms object_fragment0442020_field_008
#print axioms object_fragment0442020_field_009
#print axioms value_fragment0442020
#print axioms array_chunk0126_head
#print axioms array_chunk0126
#print axioms array_chunk0127_head
#print axioms array_chunk0127
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock064

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
