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

namespace SimplicesBlock006

noncomputable def fragment0187122Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0187122Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0187122Field000Value00 : SourceJson := .number (String.ofList ['4', '8'])
noncomputable def fragment0187122Acc00100 : List (String × SourceJson) := (fragment0187122Field000Key00, fragment0187122Field000Value00) :: fragment0187122Acc00000
noncomputable def fragment0187122Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '8', ',']

theorem object_fragment0187122_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 368) (SourceJson.white (fragment0187122Field000Chars00 ++ tail)) fragment0187122Acc00000 =
      SourceJson.object (fuel + 367) (SourceJson.white tail) fragment0187122Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0187122_object_field_000"
  err.flush

noncomputable def fragment0187122Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0187122Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['5'])]
noncomputable def fragment0187122Acc00200 : List (String × SourceJson) := (fragment0187122Field001Key00, fragment0187122Field001Value00) :: fragment0187122Acc00100
noncomputable def fragment0187122Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0187122_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 367) (SourceJson.white (fragment0187122Field001Chars00 ++ tail)) fragment0187122Acc00100 =
      SourceJson.object (fuel + 366) (SourceJson.white tail) fragment0187122Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0187122_object_field_001"
  err.flush

noncomputable def fragment0187122Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0187122Field002Value00 : SourceJson := .str (String.ofList ['1', '7', '9', '2', '9', '8', '8', '2', '5', '6', '6', '5', '4', '0', '1', '4', '2', '7', '0', '1', '8', '1', '4', '1', '5', '7', '2', '8', '2', '6', '1', '3', '1', '/', '5', '3', '7', '7', '6', '1', '7', '0', '3', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0187122Acc00300 : List (String × SourceJson) := (fragment0187122Field002Key00, fragment0187122Field002Value00) :: fragment0187122Acc00200
noncomputable def fragment0187122Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '7', '9', '2', '9', '8', '8', '2', '5', '6', '6', '5', '4', '0', '1', '4', '2', '7', '0', '1', '8', '1', '4', '1', '5', '7', '2', '8', '2', '6', '1', '3', '1', '/', '5', '3', '7', '7', '6', '1', '7', '0', '3', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0187122_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 366) (SourceJson.white (fragment0187122Field002Chars00 ++ tail)) fragment0187122Acc00200 =
      SourceJson.object (fuel + 365) (SourceJson.white tail) fragment0187122Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0187122_object_field_002"
  err.flush

noncomputable def fragment0187122Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0187122Field003Value00 : SourceJson := .str (String.ofList ['7', '9', '0', '5', '2', '7', '7', '/', '1', '5', '9', '1', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0187122Acc00400 : List (String × SourceJson) := (fragment0187122Field003Key00, fragment0187122Field003Value00) :: fragment0187122Acc00300
noncomputable def fragment0187122Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '7', '9', '0', '5', '2', '7', '7', '/', '1', '5', '9', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0187122_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 365) (SourceJson.white (fragment0187122Field003Chars00 ++ tail)) fragment0187122Acc00300 =
      SourceJson.object (fuel + 364) (SourceJson.white tail) fragment0187122Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0187122_object_field_003"
  err.flush

noncomputable def fragment0187122Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0187122Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '9', '8', '4', '4', '0', '3', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '2', '8', '1', '0', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '4', '6', '8', '7', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '8', '1', '1', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0187122Acc00500 : List (String × SourceJson) := (fragment0187122Field004Key00, fragment0187122Field004Value00) :: fragment0187122Acc00400
noncomputable def fragment0187122Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '8', '4', '4', '0', '3', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '8', '1', '0', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '4', '6', '8', '7', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '8', '1', '1', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0187122_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 364) (SourceJson.white (fragment0187122Field004Chars00 ++ tail)) fragment0187122Acc00400 =
      SourceJson.object (fuel + 363) (SourceJson.white tail) fragment0187122Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0187122_object_field_004"
  err.flush

noncomputable def fragment0187122Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0187122Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '6', '5', '4', '7', '8', '8', '0', '2', '6', '5', '7', '1', '6', '5', '8', '7', '5', '1', '9', '1', '/', '3', '1', '1', '0', '1', '2', '7', '2', '7', '9', '5', '0', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '7', '2', '7', '7', '9', '5', '1', '2', '7', '1', '2', '8', '7', '6', '5', '6', '9', '/', '2', '9', '9', '0', '5', '0', '6', '9', '9', '9', '5', '2', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '5', '5', '3', '4', '6', '3', '6', '2', '0', '1', '8', '6', '4', '3', '1', '/', '1', '7', '2', '7', '8', '4', '8', '4', '8', '8', '6', '1', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '0', '7', '7', '9', '4', '4', '3', '0', '2', '0', '4', '8', '4', '1', '2', '9', '1', '5', '9', '/', '1', '5', '5', '5', '0', '6', '3', '6', '3', '9', '7', '5', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '5', '3', '9', '6', '2', '8', '3', '5', '0', '4', '8', '4', '7', '3', '4', '6', '5', '7', '1', '/', '1', '5', '5', '5', '0', '6', '3', '6', '3', '9', '7', '5', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '5', '2', '2', '5', '0', '8', '1', '9', '0', '3', '7', '9', '4', '6', '8', '9', '7', '/', '3', '4', '5', '5', '6', '9', '6', '9', '7', '7', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '5', '7', '6', '3', '8', '6', '3', '6', '6', '1', '6', '8', '2', '7', '9', '6', '7', '/', '7', '7', '7', '5', '3', '1', '8', '1', '9', '8', '7', '5', '8', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '7', '4', '8', '1', '6', '7', '1', '2', '0', '4', '5', '0', '2', '2', '0', '5', '7', '1', '/', '1', '5', '5', '5', '0', '6', '3', '6', '3', '9', '7', '5', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '4', '7', '7', '8', '6', '1', '9', '4', '2', '0', '2', '1', '1', '8', '9', '7', '/', '7', '4', '7', '6', '2', '6', '7', '4', '9', '8', '8', '0', '6', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '9', '5', '5', '5', '2', '4', '5', '1', '6', '9', '0', '9', '0', '7', '7', '9', '/', '1', '4', '9', '5', '2', '5', '3', '4', '9', '9', '7', '6', '1', '2', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0187122Acc00600 : List (String × SourceJson) := (fragment0187122Field005Key00, fragment0187122Field005Value00) :: fragment0187122Acc00500
noncomputable def fragment0187122Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '5', '4', '7', '8', '8', '0', '2', '6', '5', '7', '1', '6', '5', '8', '7', '5', '1', '9', '1', '/', '3', '1', '1', '0', '1', '2', '7', '2', '7', '9', '5', '0', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '7', '2', '7', '7', '9', '5', '1', '2', '7', '1', '2', '8', '7', '6', '5', '6', '9', '/', '2', '9', '9', '0', '5', '0', '6', '9', '9', '9', '5', '2', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '5', '5', '3', '4', '6', '3', '6', '2', '0', '1', '8', '6', '4', '3', '1', '/', '1', '7', '2', '7', '8', '4', '8', '4', '8', '8', '6', '1', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '0', '7', '7', '9', '4', '4', '3', '0', '2', '0', '4', '8', '4', '1', '2', '9', '1', '5', '9', '/', '1', '5', '5', '5', '0', '6', '3', '6', '3', '9', '7', '5', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '3', '9', '6', '2', '8', '3', '5', '0', '4', '8', '4', '7', '3', '4', '6', '5', '7', '1', '/', '1', '5', '5', '5', '0', '6', '3', '6', '3', '9', '7', '5', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '5', '2', '2', '5', '0', '8', '1', '9', '0', '3', '7', '9', '4', '6', '8', '9', '7', '/', '3', '4', '5', '5', '6', '9', '6', '9', '7', '7', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '5', '7', '6', '3', '8', '6', '3', '6', '6', '1', '6', '8', '2', '7', '9', '6', '7', '/', '7', '7', '7', '5', '3', '1', '8', '1', '9', '8', '7', '5', '8', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '7', '4', '8', '1', '6', '7', '1', '2', '0', '4', '5', '0', '2', '2', '0', '5', '7', '1', '/', '1', '5', '5', '5', '0', '6', '3', '6', '3', '9', '7', '5', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '4', '7', '7', '8', '6', '1', '9', '4', '2', '0', '2', '1', '1', '8', '9', '7', '/', '7', '4', '7', '6', '2', '6', '7', '4', '9', '8', '8', '0', '6', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '9', '5', '5', '5', '2', '4', '5', '1', '6', '9', '0', '9', '0', '7', '7', '9', '/', '1', '4', '9', '5', '2', '5', '3', '4', '9', '9', '7', '6', '1', '2', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0187122_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 363) (SourceJson.white (fragment0187122Field005Chars00 ++ tail)) fragment0187122Acc00500 =
      SourceJson.object (fuel + 362) (SourceJson.white tail) fragment0187122Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0187122_object_field_005"
  err.flush

noncomputable def fragment0187122Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0187122Field006Value00 : SourceJson := .str (String.ofList ['1', '2', '0', '9', '5', '7', '9', '5', '2', '5', '2', '3', '3', '8', '7', '2', '6', '5', '1', '3', '8', '1', '9', '1', '3', '0', '3', '5', '9', '8', '3', '0', '5', '3', '5', '8', '8', '3', '6', '3', '3', '4', '5', '9', '2', '0', '0', '0', '0', '0', '/', '2', '5', '9', '1', '1', '6', '2', '2', '6', '9', '5', '9', '6', '1', '0', '6', '0', '6', '3', '0', '3', '8', '9', '2', '5', '1', '9', '6', '1', '2', '7', '4', '1', '4', '6', '4', '7', '9', '1', '5', '0', '6', '4', '8', '0', '4', '1', '9', '6', '8', '5', '4', '1', '2', '2', '1', '1', '4', '8', '7', '5', '5', '7', '0', '6', '1', '1'])
noncomputable def fragment0187122Acc00700 : List (String × SourceJson) := (fragment0187122Field006Key00, fragment0187122Field006Value00) :: fragment0187122Acc00600
noncomputable def fragment0187122Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '0', '9', '5', '7', '9', '5', '2', '5', '2', '3', '3', '8', '7', '2', '6', '5', '1', '3', '8', '1', '9', '1', '3', '0', '3', '5', '9', '8', '3', '0', '5', '3', '5', '8', '8', '3', '6', '3', '3', '4', '5', '9', '2', '0', '0', '0', '0', '0', '/', '2', '5', '9', '1', '1', '6', '2', '2', '6', '9', '5', '9', '6', '1', '0', '6', '0', '6', '3', '0', '3', '8', '9', '2', '5', '1', '9', '6', '1', '2', '7', '4', '1', '4', '6', '4', '7', '9', '1', '5', '0', '6', '4', '8', '0', '4', '1', '9', '6', '8', '5', '4', '1', '2', '2', '1', '1', '4', '8', '7', '5', '5', '7', '0', '6', '1', '1', '"', ',']

theorem object_fragment0187122_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 362) (SourceJson.white (fragment0187122Field006Chars00 ++ tail)) fragment0187122Acc00600 =
      SourceJson.object (fuel + 361) (SourceJson.white tail) fragment0187122Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0187122_object_field_006"
  err.flush

noncomputable def fragment0187122Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0187122Field007Value00 : SourceJson := .str (String.ofList ['2', '4', '7', '9', '3', '3', '5', '1', '6', '8', '9', '6', '4', '1', '3', '9', '6', '0', '5', '2', '0', '8', '5', '9', '3', '9', '2', '6', '4', '3', '0', '0', '0', '0', '1', '0', '8', '0', '7', '6', '9', '0', '6', '5', '7', '1', '6', '7', '0', '1', '6', '7', '3', '7', '2', '8', '2', '9', '5', '1', '3', '3', '9', '6', '7', '2', '4', '2', '1', '3', '1', '9', '2', '0', '4', '7', '7', '7', '7', '1', '3', '9', '0', '8', '2', '9', '2', '1', '9', '1', '3', '3', '5', '2', '6', '7', '9', '9', '1', '1', '3', '4', '2', '7', '4', '3', '5', '1', '5', '2', '8', '9', '2', '7', '9', '8', '7', '3', '6', '7', '7', '0', '3', '6', '7', '6', '2', '3', '0', '7', '0', '6', '6', '3', '9', '0', '3', '7', '8', '9', '1', '7', '1', '3', '8', '4', '0', '7', '8', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '1', '6', '3', '6', '7', '1', '8', '7', '4', '3', '7', '0', '7', '2', '6', '5', '2', '8', '8', '6', '7', '5', '0', '2', '0', '1', '4', '7', '5', '2', '5', '4', '0', '9', '4', '5', '2', '4', '8', '1', '8', '3', '1', '8', '4', '7', '2', '6', '5', '8', '5', '6', '0', '3', '2', '8', '9', '3', '3', '9', '1', '4', '9', '8', '9', '1', '9', '5', '3', '3', '7', '5', '4', '8', '5', '7', '3', '2', '1', '6', '4', '7', '6', '4', '0', '3', '3', '7', '9', '5', '3', '1', '7', '8', '1', '5', '0', '3', '4', '1', '1', '5', '9', '1', '5', '7', '1', '1', '8', '7', '8', '1', '5', '0', '4', '5', '0', '0', '9', '4', '5', '4', '7', '1', '5', '7', '3', '2', '9', '7', '4', '2', '8', '0', '6', '2', '6', '5', '2', '0', '9', '7', '4', '4', '9', '8', '6', '2', '3', '2', '0', '1', '0', '0', '6', '5', '8', '1', '2', '4', '2', '1', '8', '0', '2', '1', '1', '0', '1', '2', '7', '2', '9', '1', '0', '1', '5', '1', '3', '0', '3', '8', '9', '6', '9', '7'])
noncomputable def fragment0187122Acc00800 : List (String × SourceJson) := (fragment0187122Field007Key00, fragment0187122Field007Value00) :: fragment0187122Acc00700
noncomputable def fragment0187122Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '4', '7', '9', '3', '3', '5', '1', '6', '8', '9', '6', '4', '1', '3', '9', '6', '0', '5', '2', '0', '8', '5', '9', '3', '9', '2', '6', '4', '3', '0', '0', '0', '0', '1', '0', '8', '0', '7', '6', '9', '0', '6', '5', '7', '1', '6', '7', '0', '1', '6', '7', '3', '7', '2', '8', '2', '9', '5', '1', '3', '3', '9', '6', '7', '2', '4', '2', '1', '3', '1', '9', '2', '0', '4', '7', '7', '7', '7', '1', '3', '9', '0', '8', '2', '9', '2', '1', '9', '1', '3', '3', '5', '2', '6', '7', '9', '9', '1', '1', '3', '4', '2', '7', '4', '3', '5', '1', '5', '2', '8', '9', '2', '7', '9', '8', '7', '3', '6', '7', '7', '0', '3', '6', '7', '6', '2', '3', '0', '7', '0', '6', '6', '3', '9', '0', '3', '7', '8', '9', '1', '7', '1', '3', '8', '4', '0', '7', '8', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '1', '6', '3', '6', '7', '1', '8', '7', '4', '3', '7', '0', '7', '2', '6', '5', '2', '8', '8', '6', '7', '5', '0', '2', '0', '1', '4', '7', '5', '2', '5', '4', '0', '9', '4', '5', '2', '4', '8', '1', '8', '3', '1', '8', '4', '7', '2', '6', '5', '8', '5', '6', '0', '3', '2', '8', '9', '3', '3', '9', '1', '4', '9', '8', '9', '1', '9', '5', '3', '3', '7', '5', '4', '8', '5', '7', '3', '2', '1', '6', '4', '7', '6', '4', '0', '3', '3', '7', '9', '5', '3', '1', '7', '8', '1', '5', '0', '3', '4', '1', '1', '5', '9', '1', '5', '7', '1', '1', '8', '7', '8', '1', '5', '0', '4', '5', '0', '0', '9', '4', '5', '4', '7', '1', '5', '7', '3', '2', '9', '7', '4', '2', '8', '0', '6', '2', '6', '5', '2', '0', '9', '7', '4', '4', '9', '8', '6', '2', '3', '2', '0', '1', '0', '0', '6', '5', '8', '1', '2', '4', '2', '1', '8', '0', '2', '1', '1', '0', '1', '2', '7', '2', '9', '1', '0', '1', '5', '1', '3', '0', '3', '8', '9', '6', '9', '7', '"', ',']

theorem object_fragment0187122_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 361) (SourceJson.white (fragment0187122Field007Chars00 ++ tail)) fragment0187122Acc00700 =
      SourceJson.object (fuel + 360) (SourceJson.white tail) fragment0187122Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0187122_object_field_007"
  err.flush

noncomputable def fragment0187122Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0187122Field008Value00 : SourceJson := .str (String.ofList ['3', '6', '9', '8', '4', '4', '6', '9', '9', '9', '0', '0'])
noncomputable def fragment0187122Acc00900 : List (String × SourceJson) := (fragment0187122Field008Key00, fragment0187122Field008Value00) :: fragment0187122Acc00800
noncomputable def fragment0187122Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '6', '9', '8', '4', '4', '6', '9', '9', '9', '0', '0', '"', ',']

theorem object_fragment0187122_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 360) (SourceJson.white (fragment0187122Field008Chars00 ++ tail)) fragment0187122Acc00800 =
      SourceJson.object (fuel + 359) (SourceJson.white tail) fragment0187122Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0187122_object_field_008"
  err.flush

noncomputable def fragment0187122Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0187122Field009Value00 : SourceJson := .str (String.ofList ['9', '0', '7', '8', '6', '9', '4', '9', '7', '3', '1', '5'])
noncomputable def fragment0187122Acc01000 : List (String × SourceJson) := (fragment0187122Field009Key00, fragment0187122Field009Value00) :: fragment0187122Acc00900
noncomputable def fragment0187122Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '0', '7', '8', '6', '9', '4', '9', '7', '3', '1', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0187122_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 359) (SourceJson.white (fragment0187122Field009Chars00 ++ tail)) fragment0187122Acc00900 =
      .ok (.obj (fragment0187122Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0187122_object_field_009"
  err.flush

noncomputable def fragment0187122Chars : List Char := '{' :: (fragment0187122Field000Chars00 ++ fragment0187122Field001Chars00 ++ fragment0187122Field002Chars00 ++ fragment0187122Field003Chars00 ++ fragment0187122Field004Chars00 ++ fragment0187122Field005Chars00 ++ fragment0187122Field006Chars00 ++ fragment0187122Field007Chars00 ++ fragment0187122Field008Chars00 ++ fragment0187122Field009Chars00)
noncomputable def fragment0187122Value : SourceJson := .obj (fragment0187122Acc01000.reverse)

theorem value_fragment0187122 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 369) (fragment0187122Chars ++ tail) =
      .ok (fragment0187122Value, tail) := by
  have hinput : fragment0187122Chars ++ tail = '{' :: (fragment0187122Field000Chars00 ++ (fragment0187122Field001Chars00 ++ (fragment0187122Field002Chars00 ++ (fragment0187122Field003Chars00 ++ (fragment0187122Field004Chars00 ++ (fragment0187122Field005Chars00 ++ (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0187122Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 369) (fragment0187122Chars ++ tail) =
        SourceJson.value (fuel + 369) ('{' :: (fragment0187122Field000Chars00 ++ (fragment0187122Field001Chars00 ++ (fragment0187122Field002Chars00 ++ (fragment0187122Field003Chars00 ++ (fragment0187122Field004Chars00 ++ (fragment0187122Field005Chars00 ++ (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 369)) hinput
    _ = SourceJson.object (fuel + 368) (SourceJson.white (fragment0187122Field000Chars00 ++ (fragment0187122Field001Chars00 ++ (fragment0187122Field002Chars00 ++ (fragment0187122Field003Chars00 ++ (fragment0187122Field004Chars00 ++ (fragment0187122Field005Chars00 ++ (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail)))))))))))) fragment0187122Acc00000 := by rfl
    _ = SourceJson.object (fuel + 367) (SourceJson.white (fragment0187122Field001Chars00 ++ (fragment0187122Field002Chars00 ++ (fragment0187122Field003Chars00 ++ (fragment0187122Field004Chars00 ++ (fragment0187122Field005Chars00 ++ (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail))))))))))) fragment0187122Acc00100 := object_fragment0187122_field_000 fuel (fragment0187122Field001Chars00 ++ (fragment0187122Field002Chars00 ++ (fragment0187122Field003Chars00 ++ (fragment0187122Field004Chars00 ++ (fragment0187122Field005Chars00 ++ (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 366) (SourceJson.white (fragment0187122Field002Chars00 ++ (fragment0187122Field003Chars00 ++ (fragment0187122Field004Chars00 ++ (fragment0187122Field005Chars00 ++ (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail)))))))))) fragment0187122Acc00200 := object_fragment0187122_field_001 fuel (fragment0187122Field002Chars00 ++ (fragment0187122Field003Chars00 ++ (fragment0187122Field004Chars00 ++ (fragment0187122Field005Chars00 ++ (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 365) (SourceJson.white (fragment0187122Field003Chars00 ++ (fragment0187122Field004Chars00 ++ (fragment0187122Field005Chars00 ++ (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail))))))))) fragment0187122Acc00300 := object_fragment0187122_field_002 fuel (fragment0187122Field003Chars00 ++ (fragment0187122Field004Chars00 ++ (fragment0187122Field005Chars00 ++ (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 364) (SourceJson.white (fragment0187122Field004Chars00 ++ (fragment0187122Field005Chars00 ++ (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail)))))))) fragment0187122Acc00400 := object_fragment0187122_field_003 fuel (fragment0187122Field004Chars00 ++ (fragment0187122Field005Chars00 ++ (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 363) (SourceJson.white (fragment0187122Field005Chars00 ++ (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail))))))) fragment0187122Acc00500 := object_fragment0187122_field_004 fuel (fragment0187122Field005Chars00 ++ (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 362) (SourceJson.white (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail)))))) fragment0187122Acc00600 := object_fragment0187122_field_005 fuel (fragment0187122Field006Chars00 ++ (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 361) (SourceJson.white (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail))))) fragment0187122Acc00700 := object_fragment0187122_field_006 fuel (fragment0187122Field007Chars00 ++ (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 360) (SourceJson.white (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail)))) fragment0187122Acc00800 := object_fragment0187122_field_007 fuel (fragment0187122Field008Chars00 ++ (fragment0187122Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 359) (SourceJson.white (fragment0187122Field009Chars00 ++ (tail))) fragment0187122Acc00900 := object_fragment0187122_field_008 fuel (fragment0187122Field009Chars00 ++ (tail))
    _ = .ok (fragment0187122Value, tail) := object_fragment0187122_field_009 fuel (tail)

noncomputable def fragment0188995Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0188995Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0188995Field000Value00 : SourceJson := .number (String.ofList ['4', '9'])
noncomputable def fragment0188995Acc00100 : List (String × SourceJson) := (fragment0188995Field000Key00, fragment0188995Field000Value00) :: fragment0188995Acc00000
noncomputable def fragment0188995Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '9', ',']

theorem object_fragment0188995_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0188995Field000Chars00 ++ tail)) fragment0188995Acc00000 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0188995Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188995_object_field_000"
  err.flush

noncomputable def fragment0188995Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0188995Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0188995Acc00200 : List (String × SourceJson) := (fragment0188995Field001Key00, fragment0188995Field001Value00) :: fragment0188995Acc00100
noncomputable def fragment0188995Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0188995_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0188995Field001Chars00 ++ tail)) fragment0188995Acc00100 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0188995Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188995_object_field_001"
  err.flush

noncomputable def fragment0188995Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0188995Field002Value00 : SourceJson := .str (String.ofList ['6', '3', '6', '1', '4', '0', '6', '6', '8', '2', '3', '7', '1', '3', '7', '8', '3', '1', '8', '5', '3', '8', '0', '3', '9', '7', '8', '6', '3', '5', '1', '0', '1', '5', '8', '1', '2', '6', '0', '3', '/', '3', '2', '7', '2', '0', '5', '5', '3', '0', '9', '4', '4', '6', '6', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0188995Acc00300 : List (String × SourceJson) := (fragment0188995Field002Key00, fragment0188995Field002Value00) :: fragment0188995Acc00200
noncomputable def fragment0188995Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '3', '6', '1', '4', '0', '6', '6', '8', '2', '3', '7', '1', '3', '7', '8', '3', '1', '8', '5', '3', '8', '0', '3', '9', '7', '8', '6', '3', '5', '1', '0', '1', '5', '8', '1', '2', '6', '0', '3', '/', '3', '2', '7', '2', '0', '5', '5', '3', '0', '9', '4', '4', '6', '6', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0188995_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0188995Field002Chars00 ++ tail)) fragment0188995Acc00200 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0188995Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188995_object_field_002"
  err.flush

noncomputable def fragment0188995Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0188995Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0188995Acc00400 : List (String × SourceJson) := (fragment0188995Field003Key00, fragment0188995Field003Value00) :: fragment0188995Acc00300
noncomputable def fragment0188995Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0188995_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0188995Field003Chars00 ++ tail)) fragment0188995Acc00300 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0188995Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188995_object_field_003"
  err.flush

noncomputable def fragment0188995Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0188995Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '2', '8', '0', '3', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0188995Acc00500 : List (String × SourceJson) := (fragment0188995Field004Key00, fragment0188995Field004Value00) :: fragment0188995Acc00400
noncomputable def fragment0188995Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '2', '8', '0', '3', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0188995_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0188995Field004Chars00 ++ tail)) fragment0188995Acc00400 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0188995Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188995_object_field_004"
  err.flush

noncomputable def fragment0188995Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0188995Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '1', '3', '2', '6', '9', '4', '4', '4', '5', '6', '4', '2', '1', '/', '2', '2', '6', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '4', '3', '6', '1', '8', '8', '4', '6', '9', '4', '8', '1', '/', '2', '2', '6', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '1', '6', '6', '8', '3', '2', '5', '0', '9', '9', '2', '9', '/', '1', '3', '5', '8', '8', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '1', '4', '7', '3', '4', '2', '2', '7', '2', '4', '9', '/', '4', '2', '4', '6', '5', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '2', '2', '8', '8', '0', '1', '7', '2', '0', '9', '9', '/', '7', '5', '4', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '4', '1', '1', '9', '7', '5', '1', '6', '8', '1', '1', '/', '2', '7', '1', '7', '7', '6', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '3', '7', '0', '4', '9', '9', '0', '9', '2', '4', '7', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '9', '1', '0', '1', '3', '1', '7', '1', '3', '0', '3', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '5', '5', '2', '8', '3', '1', '7', '2', '9', '8', '1', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '5', '5', '2', '3', '7', '8', '7', '6', '8', '2', '1', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0188995Acc00600 : List (String × SourceJson) := (fragment0188995Field005Key00, fragment0188995Field005Value00) :: fragment0188995Acc00500
noncomputable def fragment0188995Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '3', '2', '6', '9', '4', '4', '4', '5', '6', '4', '2', '1', '/', '2', '2', '6', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '4', '3', '6', '1', '8', '8', '4', '6', '9', '4', '8', '1', '/', '2', '2', '6', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '6', '6', '8', '3', '2', '5', '0', '9', '9', '2', '9', '/', '1', '3', '5', '8', '8', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '1', '4', '7', '3', '4', '2', '2', '7', '2', '4', '9', '/', '4', '2', '4', '6', '5', '1', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '2', '2', '8', '8', '0', '1', '7', '2', '0', '9', '9', '/', '7', '5', '4', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '1', '1', '9', '7', '5', '1', '6', '8', '1', '1', '/', '2', '7', '1', '7', '7', '6', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '6', '3', '7', '0', '4', '9', '9', '0', '9', '2', '4', '7', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '9', '1', '0', '1', '3', '1', '7', '1', '3', '0', '3', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '0', '5', '5', '2', '8', '3', '1', '7', '2', '9', '8', '1', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '0', '5', '5', '2', '3', '7', '8', '7', '6', '8', '2', '1', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0188995_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0188995Field005Chars00 ++ tail)) fragment0188995Acc00500 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0188995Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188995_object_field_005"
  err.flush

noncomputable def fragment0188995Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0188995Field006Value00 : SourceJson := .str (String.ofList ['8', '1', '5', '0', '5', '7', '7', '1', '6', '1', '0', '3', '3', '1', '8', '1', '4', '8', '3', '8', '2', '3', '4', '2', '0', '2', '6', '5', '4', '8', '0', '1', '5', '4', '4', '4', '3', '5', '5', '3', '1', '1', '1', '7', '3', '0', '4', '6', '8', '7', '5', '/', '1', '2', '8', '9', '2', '9', '8', '2', '1', '7', '1', '6', '3', '6', '9', '7', '1', '7', '0', '9', '9', '2', '9', '8', '9', '1', '1', '1', '7', '5', '1', '6', '6', '6', '6', '1', '7', '4', '0', '9', '3', '0', '6', '3', '6', '5', '3', '7', '2', '7', '2', '7', '5', '6', '4', '7', '1', '3', '0', '7', '6', '3', '2', '3', '4', '6', '1', '2', '6'])
noncomputable def fragment0188995Acc00700 : List (String × SourceJson) := (fragment0188995Field006Key00, fragment0188995Field006Value00) :: fragment0188995Acc00600
noncomputable def fragment0188995Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '1', '5', '0', '5', '7', '7', '1', '6', '1', '0', '3', '3', '1', '8', '1', '4', '8', '3', '8', '2', '3', '4', '2', '0', '2', '6', '5', '4', '8', '0', '1', '5', '4', '4', '4', '3', '5', '5', '3', '1', '1', '1', '7', '3', '0', '4', '6', '8', '7', '5', '/', '1', '2', '8', '9', '2', '9', '8', '2', '1', '7', '1', '6', '3', '6', '9', '7', '1', '7', '0', '9', '9', '2', '9', '8', '9', '1', '1', '1', '7', '5', '1', '6', '6', '6', '6', '1', '7', '4', '0', '9', '3', '0', '6', '3', '6', '5', '3', '7', '2', '7', '2', '7', '5', '6', '4', '7', '1', '3', '0', '7', '6', '3', '2', '3', '4', '6', '1', '2', '6', '"', ',']

theorem object_fragment0188995_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0188995Field006Chars00 ++ tail)) fragment0188995Acc00600 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0188995Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188995_object_field_006"
  err.flush

noncomputable def fragment0188995Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0188995Field007Value00 : SourceJson := .str (String.ofList ['6', '7', '4', '2', '7', '6', '0', '1', '4', '9', '1', '5', '5', '1', '3', '7', '8', '1', '8', '7', '8', '5', '3', '2', '2', '0', '6', '4', '6', '3', '2', '1', '5', '0', '6', '6', '1', '2', '7', '3', '7', '4', '1', '7', '0', '3', '1', '8', '7', '7', '1', '8', '7', '7', '2', '6', '9', '1', '3', '9', '6', '8', '5', '5', '0', '3', '1', '8', '8', '9', '7', '5', '7', '6', '6', '3', '1', '7', '9', '9', '5', '3', '8', '9', '2', '9', '0', '1', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '6', '5', '8', '3', '2', '7', '5', '8', '1', '8', '8', '8', '6', '2', '1', '3', '8', '0', '9', '2', '3', '6', '2', '8', '9', '0', '9', '9', '2', '7', '9', '3', '4', '8', '5', '2', '4', '0', '8', '6', '9', '2', '8', '9', '3', '9', '5', '7', '4', '7', '1', '4', '4', '8', '8', '3', '0', '4', '6', '3', '7', '1', '1', '4', '1', '4', '2', '6', '2', '9', '1', '5', '2', '4', '2', '1', '9', '1', '8', '2', '7', '1', '4', '5', '0', '2', '3', '3', '5', '7', '7', '5', '9', '2', '1', '7', '0', '9', '0', '3', '8', '0', '3', '0', '4', '4', '9', '3', '4', '4', '5', '1', '1', '5', '4', '5', '7', '3', '7', '4', '5', '8', '3', '3', '3', '4', '7', '8', '2', '9'])
noncomputable def fragment0188995Acc00800 : List (String × SourceJson) := (fragment0188995Field007Key00, fragment0188995Field007Value00) :: fragment0188995Acc00700
noncomputable def fragment0188995Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '7', '4', '2', '7', '6', '0', '1', '4', '9', '1', '5', '5', '1', '3', '7', '8', '1', '8', '7', '8', '5', '3', '2', '2', '0', '6', '4', '6', '3', '2', '1', '5', '0', '6', '6', '1', '2', '7', '3', '7', '4', '1', '7', '0', '3', '1', '8', '7', '7', '1', '8', '7', '7', '2', '6', '9', '1', '3', '9', '6', '8', '5', '5', '0', '3', '1', '8', '8', '9', '7', '5', '7', '6', '6', '3', '1', '7', '9', '9', '5', '3', '8', '9', '2', '9', '0', '1', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '6', '5', '8', '3', '2', '7', '5', '8', '1', '8', '8', '8', '6', '2', '1', '3', '8', '0', '9', '2', '3', '6', '2', '8', '9', '0', '9', '9', '2', '7', '9', '3', '4', '8', '5', '2', '4', '0', '8', '6', '9', '2', '8', '9', '3', '9', '5', '7', '4', '7', '1', '4', '4', '8', '8', '3', '0', '4', '6', '3', '7', '1', '1', '4', '1', '4', '2', '6', '2', '9', '1', '5', '2', '4', '2', '1', '9', '1', '8', '2', '7', '1', '4', '5', '0', '2', '3', '3', '5', '7', '7', '5', '9', '2', '1', '7', '0', '9', '0', '3', '8', '0', '3', '0', '4', '4', '9', '3', '4', '4', '5', '1', '1', '5', '4', '5', '7', '3', '7', '4', '5', '8', '3', '3', '3', '4', '7', '8', '2', '9', '"', ',']

theorem object_fragment0188995_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0188995Field007Chars00 ++ tail)) fragment0188995Acc00700 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0188995Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188995_object_field_007"
  err.flush

noncomputable def fragment0188995Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0188995Field008Value00 : SourceJson := .str (String.ofList ['5', '0', '0', '8', '5', '7', '9', '4', '2', '1', '7', '5'])
noncomputable def fragment0188995Acc00900 : List (String × SourceJson) := (fragment0188995Field008Key00, fragment0188995Field008Value00) :: fragment0188995Acc00800
noncomputable def fragment0188995Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '0', '0', '8', '5', '7', '9', '4', '2', '1', '7', '5', '"', ',']

theorem object_fragment0188995_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0188995Field008Chars00 ++ tail)) fragment0188995Acc00800 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0188995Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188995_object_field_008"
  err.flush

noncomputable def fragment0188995Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0188995Field009Value00 : SourceJson := .str (String.ofList ['2', '0', '0', '9', '5', '9', '6', '1', '8', '5', '7', '0', '5'])
noncomputable def fragment0188995Acc01000 : List (String × SourceJson) := (fragment0188995Field009Key00, fragment0188995Field009Value00) :: fragment0188995Acc00900
noncomputable def fragment0188995Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '0', '9', '5', '9', '6', '1', '8', '5', '7', '0', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0188995_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0188995Field009Chars00 ++ tail)) fragment0188995Acc00900 =
      .ok (.obj (fragment0188995Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188995_object_field_009"
  err.flush

noncomputable def fragment0188995Chars : List Char := '{' :: (fragment0188995Field000Chars00 ++ fragment0188995Field001Chars00 ++ fragment0188995Field002Chars00 ++ fragment0188995Field003Chars00 ++ fragment0188995Field004Chars00 ++ fragment0188995Field005Chars00 ++ fragment0188995Field006Chars00 ++ fragment0188995Field007Chars00 ++ fragment0188995Field008Chars00 ++ fragment0188995Field009Chars00)
noncomputable def fragment0188995Value : SourceJson := .obj (fragment0188995Acc01000.reverse)

theorem value_fragment0188995 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 257) (fragment0188995Chars ++ tail) =
      .ok (fragment0188995Value, tail) := by
  have hinput : fragment0188995Chars ++ tail = '{' :: (fragment0188995Field000Chars00 ++ (fragment0188995Field001Chars00 ++ (fragment0188995Field002Chars00 ++ (fragment0188995Field003Chars00 ++ (fragment0188995Field004Chars00 ++ (fragment0188995Field005Chars00 ++ (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0188995Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 257) (fragment0188995Chars ++ tail) =
        SourceJson.value (fuel + 257) ('{' :: (fragment0188995Field000Chars00 ++ (fragment0188995Field001Chars00 ++ (fragment0188995Field002Chars00 ++ (fragment0188995Field003Chars00 ++ (fragment0188995Field004Chars00 ++ (fragment0188995Field005Chars00 ++ (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 257)) hinput
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0188995Field000Chars00 ++ (fragment0188995Field001Chars00 ++ (fragment0188995Field002Chars00 ++ (fragment0188995Field003Chars00 ++ (fragment0188995Field004Chars00 ++ (fragment0188995Field005Chars00 ++ (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail)))))))))))) fragment0188995Acc00000 := by rfl
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0188995Field001Chars00 ++ (fragment0188995Field002Chars00 ++ (fragment0188995Field003Chars00 ++ (fragment0188995Field004Chars00 ++ (fragment0188995Field005Chars00 ++ (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail))))))))))) fragment0188995Acc00100 := object_fragment0188995_field_000 fuel (fragment0188995Field001Chars00 ++ (fragment0188995Field002Chars00 ++ (fragment0188995Field003Chars00 ++ (fragment0188995Field004Chars00 ++ (fragment0188995Field005Chars00 ++ (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0188995Field002Chars00 ++ (fragment0188995Field003Chars00 ++ (fragment0188995Field004Chars00 ++ (fragment0188995Field005Chars00 ++ (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail)))))))))) fragment0188995Acc00200 := object_fragment0188995_field_001 fuel (fragment0188995Field002Chars00 ++ (fragment0188995Field003Chars00 ++ (fragment0188995Field004Chars00 ++ (fragment0188995Field005Chars00 ++ (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0188995Field003Chars00 ++ (fragment0188995Field004Chars00 ++ (fragment0188995Field005Chars00 ++ (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail))))))))) fragment0188995Acc00300 := object_fragment0188995_field_002 fuel (fragment0188995Field003Chars00 ++ (fragment0188995Field004Chars00 ++ (fragment0188995Field005Chars00 ++ (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0188995Field004Chars00 ++ (fragment0188995Field005Chars00 ++ (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail)))))))) fragment0188995Acc00400 := object_fragment0188995_field_003 fuel (fragment0188995Field004Chars00 ++ (fragment0188995Field005Chars00 ++ (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0188995Field005Chars00 ++ (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail))))))) fragment0188995Acc00500 := object_fragment0188995_field_004 fuel (fragment0188995Field005Chars00 ++ (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail)))))) fragment0188995Acc00600 := object_fragment0188995_field_005 fuel (fragment0188995Field006Chars00 ++ (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail))))) fragment0188995Acc00700 := object_fragment0188995_field_006 fuel (fragment0188995Field007Chars00 ++ (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail)))) fragment0188995Acc00800 := object_fragment0188995_field_007 fuel (fragment0188995Field008Chars00 ++ (fragment0188995Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0188995Field009Chars00 ++ (tail))) fragment0188995Acc00900 := object_fragment0188995_field_008 fuel (fragment0188995Field009Chars00 ++ (tail))
    _ = .ok (fragment0188995Value, tail) := object_fragment0188995_field_009 fuel (tail)

noncomputable def fragment0190642Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0190642Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0190642Field000Value00 : SourceJson := .number (String.ofList ['5', '0'])
noncomputable def fragment0190642Acc00100 : List (String × SourceJson) := (fragment0190642Field000Key00, fragment0190642Field000Value00) :: fragment0190642Acc00000
noncomputable def fragment0190642Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '0', ',']

theorem object_fragment0190642_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0190642Field000Chars00 ++ tail)) fragment0190642Acc00000 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0190642Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190642_object_field_000"
  err.flush

noncomputable def fragment0190642Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0190642Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0190642Acc00200 : List (String × SourceJson) := (fragment0190642Field001Key00, fragment0190642Field001Value00) :: fragment0190642Acc00100
noncomputable def fragment0190642Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0190642_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0190642Field001Chars00 ++ tail)) fragment0190642Acc00100 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0190642Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190642_object_field_001"
  err.flush

noncomputable def fragment0190642Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0190642Field002Value00 : SourceJson := .str (String.ofList ['1', '1', '9', '0', '9', '3', '7', '1', '6', '4', '6', '0', '8', '3', '9', '6', '8', '9', '0', '5', '1', '2', '9', '8', '6', '0', '2', '2', '1', '7', '3', '6', '0', '6', '9', '0', '9', '7', '/', '6', '7', '4', '1', '8', '7', '2', '2', '0', '3', '5', '3', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0190642Acc00300 : List (String × SourceJson) := (fragment0190642Field002Key00, fragment0190642Field002Value00) :: fragment0190642Acc00200
noncomputable def fragment0190642Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '1', '9', '0', '9', '3', '7', '1', '6', '4', '6', '0', '8', '3', '9', '6', '8', '9', '0', '5', '1', '2', '9', '8', '6', '0', '2', '2', '1', '7', '3', '6', '0', '6', '9', '0', '9', '7', '/', '6', '7', '4', '1', '8', '7', '2', '2', '0', '3', '5', '3', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0190642_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0190642Field002Chars00 ++ tail)) fragment0190642Acc00200 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0190642Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190642_object_field_002"
  err.flush

noncomputable def fragment0190642Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0190642Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0190642Acc00400 : List (String × SourceJson) := (fragment0190642Field003Key00, fragment0190642Field003Value00) :: fragment0190642Acc00300
noncomputable def fragment0190642Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0190642_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0190642Field003Chars00 ++ tail)) fragment0190642Acc00300 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0190642Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190642_object_field_003"
  err.flush

noncomputable def fragment0190642Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0190642Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0190642Acc00500 : List (String × SourceJson) := (fragment0190642Field004Key00, fragment0190642Field004Value00) :: fragment0190642Acc00400
noncomputable def fragment0190642Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0190642_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0190642Field004Chars00 ++ tail)) fragment0190642Acc00400 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0190642Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190642_object_field_004"
  err.flush

noncomputable def fragment0190642Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0190642Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '8', '0', '9', '6', '0', '6', '0', '4', '6', '7', '7', '1', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '3', '4', '8', '1', '6', '2', '0', '3', '6', '3', '1', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '5', '0', '1', '2', '7', '6', '2', '0', '4', '9', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '5', '2', '1', '2', '3', '5', '0', '4', '7', '/', '1', '3', '0', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '1', '2', '4', '4', '1', '5', '3', '1', '0', '3', '/', '5', '8', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '3', '6', '6', '5', '7', '0', '6', '7', '1', '9', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '2', '1', '0', '0', '4', '7', '0', '9', '1', '4', '9', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '4', '4', '6', '5', '8', '5', '5', '6', '3', '7', '/', '8', '7', '1', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '8', '3', '8', '9', '6', '8', '8', '6', '3', '3', '/', '5', '8', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '5', '1', '6', '7', '9', '0', '4', '4', '5', '9', '/', '1', '7', '4', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0190642Acc00600 : List (String × SourceJson) := (fragment0190642Field005Key00, fragment0190642Field005Value00) :: fragment0190642Acc00500
noncomputable def fragment0190642Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '0', '9', '6', '0', '6', '0', '4', '6', '7', '7', '1', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '3', '4', '8', '1', '6', '2', '0', '3', '6', '3', '1', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '5', '0', '1', '2', '7', '6', '2', '0', '4', '9', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '5', '2', '1', '2', '3', '5', '0', '4', '7', '/', '1', '3', '0', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '1', '2', '4', '4', '1', '5', '3', '1', '0', '3', '/', '5', '8', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '3', '6', '6', '5', '7', '0', '6', '7', '1', '9', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '1', '0', '0', '4', '7', '0', '9', '1', '4', '9', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '4', '4', '6', '5', '8', '5', '5', '6', '3', '7', '/', '8', '7', '1', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '8', '3', '8', '9', '6', '8', '8', '6', '3', '3', '/', '5', '8', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '5', '1', '6', '7', '9', '0', '4', '4', '5', '9', '/', '1', '7', '4', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0190642_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0190642Field005Chars00 ++ tail)) fragment0190642Acc00500 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0190642Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190642_object_field_005"
  err.flush

noncomputable def fragment0190642Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0190642Field006Value00 : SourceJson := .str (String.ofList ['2', '2', '1', '9', '4', '8', '0', '5', '7', '3', '4', '5', '8', '6', '2', '9', '4', '8', '0', '0', '2', '9', '2', '6', '0', '9', '5', '6', '0', '1', '6', '8', '4', '7', '9', '5', '4', '4', '8', '0', '1', '6', '8', '7', '5', '0', '0', '0', '/', '4', '0', '3', '6', '1', '6', '9', '3', '1', '1', '3', '2', '8', '5', '1', '9', '0', '9', '3', '7', '0', '5', '0', '0', '7', '6', '5', '3', '7', '5', '7', '6', '1', '9', '8', '8', '2', '0', '2', '2', '4', '4', '5', '8', '0', '8', '7', '6', '5', '7', '3', '2', '6', '9', '7', '0', '1', '7', '5', '3', '0', '5', '5', '5', '3'])
noncomputable def fragment0190642Acc00700 : List (String × SourceJson) := (fragment0190642Field006Key00, fragment0190642Field006Value00) :: fragment0190642Acc00600
noncomputable def fragment0190642Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '2', '1', '9', '4', '8', '0', '5', '7', '3', '4', '5', '8', '6', '2', '9', '4', '8', '0', '0', '2', '9', '2', '6', '0', '9', '5', '6', '0', '1', '6', '8', '4', '7', '9', '5', '4', '4', '8', '0', '1', '6', '8', '7', '5', '0', '0', '0', '/', '4', '0', '3', '6', '1', '6', '9', '3', '1', '1', '3', '2', '8', '5', '1', '9', '0', '9', '3', '7', '0', '5', '0', '0', '7', '6', '5', '3', '7', '5', '7', '6', '1', '9', '8', '8', '2', '0', '2', '2', '4', '4', '5', '8', '0', '8', '7', '6', '5', '7', '3', '2', '6', '9', '7', '0', '1', '7', '5', '3', '0', '5', '5', '5', '3', '"', ',']

theorem object_fragment0190642_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0190642Field006Chars00 ++ tail)) fragment0190642Acc00600 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0190642Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190642_object_field_006"
  err.flush

noncomputable def fragment0190642Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0190642Field007Value00 : SourceJson := .str (String.ofList ['8', '9', '7', '7', '9', '0', '0', '6', '8', '8', '9', '9', '6', '2', '1', '3', '2', '1', '1', '1', '4', '0', '6', '9', '8', '5', '7', '3', '9', '8', '8', '7', '3', '1', '7', '1', '3', '7', '1', '6', '6', '7', '8', '2', '6', '7', '4', '4', '8', '2', '0', '6', '2', '5', '7', '3', '2', '1', '8', '1', '4', '9', '1', '3', '5', '7', '9', '3', '9', '1', '6', '4', '1', '6', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '3', '6', '1', '2', '9', '7', '2', '4', '0', '2', '8', '2', '4', '9', '7', '4', '3', '2', '3', '0', '5', '8', '7', '3', '6', '4', '9', '0', '8', '2', '1', '6', '4', '9', '7', '4', '7', '3', '9', '3', '5', '0', '7', '5', '6', '2', '2', '1', '4', '8', '2', '4', '7', '7', '5', '0', '9', '1', '5', '6', '5', '0', '1', '8', '1', '5', '8', '5', '7', '2', '6', '2', '9', '6', '7', '2', '0', '9', '1', '5', '1', '3', '4', '2', '3', '5', '3', '3', '1', '8', '1', '2', '2', '5', '7', '8', '3', '2', '9', '8', '8', '2', '7', '2', '9', '1', '6', '8', '3', '5', '0', '7', '7', '1', '1', '7', '1'])
noncomputable def fragment0190642Acc00800 : List (String × SourceJson) := (fragment0190642Field007Key00, fragment0190642Field007Value00) :: fragment0190642Acc00700
noncomputable def fragment0190642Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '9', '7', '7', '9', '0', '0', '6', '8', '8', '9', '9', '6', '2', '1', '3', '2', '1', '1', '1', '4', '0', '6', '9', '8', '5', '7', '3', '9', '8', '8', '7', '3', '1', '7', '1', '3', '7', '1', '6', '6', '7', '8', '2', '6', '7', '4', '4', '8', '2', '0', '6', '2', '5', '7', '3', '2', '1', '8', '1', '4', '9', '1', '3', '5', '7', '9', '3', '9', '1', '6', '4', '1', '6', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '3', '6', '1', '2', '9', '7', '2', '4', '0', '2', '8', '2', '4', '9', '7', '4', '3', '2', '3', '0', '5', '8', '7', '3', '6', '4', '9', '0', '8', '2', '1', '6', '4', '9', '7', '4', '7', '3', '9', '3', '5', '0', '7', '5', '6', '2', '2', '1', '4', '8', '2', '4', '7', '7', '5', '0', '9', '1', '5', '6', '5', '0', '1', '8', '1', '5', '8', '5', '7', '2', '6', '2', '9', '6', '7', '2', '0', '9', '1', '5', '1', '3', '4', '2', '3', '5', '3', '3', '1', '8', '1', '2', '2', '5', '7', '8', '3', '2', '9', '8', '8', '2', '7', '2', '9', '1', '6', '8', '3', '5', '0', '7', '7', '1', '1', '7', '1', '"', ',']

theorem object_fragment0190642_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0190642Field007Chars00 ++ tail)) fragment0190642Acc00700 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0190642Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190642_object_field_007"
  err.flush

noncomputable def fragment0190642Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0190642Field008Value00 : SourceJson := .str (String.ofList ['4', '3', '5', '6', '7', '3', '9', '1', '2', '5', '8', '2'])
noncomputable def fragment0190642Acc00900 : List (String × SourceJson) := (fragment0190642Field008Key00, fragment0190642Field008Value00) :: fragment0190642Acc00800
noncomputable def fragment0190642Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '3', '5', '6', '7', '3', '9', '1', '2', '5', '8', '2', '"', ',']

theorem object_fragment0190642_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0190642Field008Chars00 ++ tail)) fragment0190642Acc00800 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0190642Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190642_object_field_008"
  err.flush

noncomputable def fragment0190642Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0190642Field009Value00 : SourceJson := .str (String.ofList ['1', '9', '0', '3', '8', '4', '8', '7', '0', '8', '0', '6', '3'])
noncomputable def fragment0190642Acc01000 : List (String × SourceJson) := (fragment0190642Field009Key00, fragment0190642Field009Value00) :: fragment0190642Acc00900
noncomputable def fragment0190642Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '0', '3', '8', '4', '8', '7', '0', '8', '0', '6', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0190642_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0190642Field009Chars00 ++ tail)) fragment0190642Acc00900 =
      .ok (.obj (fragment0190642Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190642_object_field_009"
  err.flush

noncomputable def fragment0190642Chars : List Char := '{' :: (fragment0190642Field000Chars00 ++ fragment0190642Field001Chars00 ++ fragment0190642Field002Chars00 ++ fragment0190642Field003Chars00 ++ fragment0190642Field004Chars00 ++ fragment0190642Field005Chars00 ++ fragment0190642Field006Chars00 ++ fragment0190642Field007Chars00 ++ fragment0190642Field008Chars00 ++ fragment0190642Field009Chars00)
noncomputable def fragment0190642Value : SourceJson := .obj (fragment0190642Acc01000.reverse)

theorem value_fragment0190642 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 233) (fragment0190642Chars ++ tail) =
      .ok (fragment0190642Value, tail) := by
  have hinput : fragment0190642Chars ++ tail = '{' :: (fragment0190642Field000Chars00 ++ (fragment0190642Field001Chars00 ++ (fragment0190642Field002Chars00 ++ (fragment0190642Field003Chars00 ++ (fragment0190642Field004Chars00 ++ (fragment0190642Field005Chars00 ++ (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0190642Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 233) (fragment0190642Chars ++ tail) =
        SourceJson.value (fuel + 233) ('{' :: (fragment0190642Field000Chars00 ++ (fragment0190642Field001Chars00 ++ (fragment0190642Field002Chars00 ++ (fragment0190642Field003Chars00 ++ (fragment0190642Field004Chars00 ++ (fragment0190642Field005Chars00 ++ (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 233)) hinput
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0190642Field000Chars00 ++ (fragment0190642Field001Chars00 ++ (fragment0190642Field002Chars00 ++ (fragment0190642Field003Chars00 ++ (fragment0190642Field004Chars00 ++ (fragment0190642Field005Chars00 ++ (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail)))))))))))) fragment0190642Acc00000 := by rfl
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0190642Field001Chars00 ++ (fragment0190642Field002Chars00 ++ (fragment0190642Field003Chars00 ++ (fragment0190642Field004Chars00 ++ (fragment0190642Field005Chars00 ++ (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail))))))))))) fragment0190642Acc00100 := object_fragment0190642_field_000 fuel (fragment0190642Field001Chars00 ++ (fragment0190642Field002Chars00 ++ (fragment0190642Field003Chars00 ++ (fragment0190642Field004Chars00 ++ (fragment0190642Field005Chars00 ++ (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0190642Field002Chars00 ++ (fragment0190642Field003Chars00 ++ (fragment0190642Field004Chars00 ++ (fragment0190642Field005Chars00 ++ (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail)))))))))) fragment0190642Acc00200 := object_fragment0190642_field_001 fuel (fragment0190642Field002Chars00 ++ (fragment0190642Field003Chars00 ++ (fragment0190642Field004Chars00 ++ (fragment0190642Field005Chars00 ++ (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0190642Field003Chars00 ++ (fragment0190642Field004Chars00 ++ (fragment0190642Field005Chars00 ++ (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail))))))))) fragment0190642Acc00300 := object_fragment0190642_field_002 fuel (fragment0190642Field003Chars00 ++ (fragment0190642Field004Chars00 ++ (fragment0190642Field005Chars00 ++ (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0190642Field004Chars00 ++ (fragment0190642Field005Chars00 ++ (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail)))))))) fragment0190642Acc00400 := object_fragment0190642_field_003 fuel (fragment0190642Field004Chars00 ++ (fragment0190642Field005Chars00 ++ (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0190642Field005Chars00 ++ (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail))))))) fragment0190642Acc00500 := object_fragment0190642_field_004 fuel (fragment0190642Field005Chars00 ++ (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail)))))) fragment0190642Acc00600 := object_fragment0190642_field_005 fuel (fragment0190642Field006Chars00 ++ (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail))))) fragment0190642Acc00700 := object_fragment0190642_field_006 fuel (fragment0190642Field007Chars00 ++ (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail)))) fragment0190642Acc00800 := object_fragment0190642_field_007 fuel (fragment0190642Field008Chars00 ++ (fragment0190642Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0190642Field009Chars00 ++ (tail))) fragment0190642Acc00900 := object_fragment0190642_field_008 fuel (fragment0190642Field009Chars00 ++ (tail))
    _ = .ok (fragment0190642Value, tail) := object_fragment0190642_field_009 fuel (tail)

noncomputable def fragment0192229Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0192229Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0192229Field000Value00 : SourceJson := .number (String.ofList ['5', '1'])
noncomputable def fragment0192229Acc00100 : List (String × SourceJson) := (fragment0192229Field000Key00, fragment0192229Field000Value00) :: fragment0192229Acc00000
noncomputable def fragment0192229Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '1', ',']

theorem object_fragment0192229_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0192229Field000Chars00 ++ tail)) fragment0192229Acc00000 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0192229Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0192229_object_field_000"
  err.flush

noncomputable def fragment0192229Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0192229Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0192229Acc00200 : List (String × SourceJson) := (fragment0192229Field001Key00, fragment0192229Field001Value00) :: fragment0192229Acc00100
noncomputable def fragment0192229Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0192229_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0192229Field001Chars00 ++ tail)) fragment0192229Acc00100 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0192229Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0192229_object_field_001"
  err.flush

noncomputable def fragment0192229Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0192229Field002Value00 : SourceJson := .str (String.ofList ['1', '0', '6', '9', '3', '9', '2', '5', '3', '1', '4', '3', '3', '0', '2', '0', '3', '3', '9', '3', '2', '0', '8', '5', '4', '2', '2', '5', '2', '6', '1', '7', '6', '8', '1', '8', '1', '/', '9', '2', '2', '9', '9', '4', '4', '0', '8', '8', '1', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0192229Acc00300 : List (String × SourceJson) := (fragment0192229Field002Key00, fragment0192229Field002Value00) :: fragment0192229Acc00200
noncomputable def fragment0192229Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '0', '6', '9', '3', '9', '2', '5', '3', '1', '4', '3', '3', '0', '2', '0', '3', '3', '9', '3', '2', '0', '8', '5', '4', '2', '2', '5', '2', '6', '1', '7', '6', '8', '1', '8', '1', '/', '9', '2', '2', '9', '9', '4', '4', '0', '8', '8', '1', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0192229_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0192229Field002Chars00 ++ tail)) fragment0192229Acc00200 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0192229Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0192229_object_field_002"
  err.flush

noncomputable def fragment0192229Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0192229Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0192229Acc00400 : List (String × SourceJson) := (fragment0192229Field003Key00, fragment0192229Field003Value00) :: fragment0192229Acc00300
noncomputable def fragment0192229Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0192229_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0192229Field003Chars00 ++ tail)) fragment0192229Acc00300 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0192229Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0192229_object_field_003"
  err.flush

noncomputable def fragment0192229Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0192229Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0192229Acc00500 : List (String × SourceJson) := (fragment0192229Field004Key00, fragment0192229Field004Value00) :: fragment0192229Acc00400
noncomputable def fragment0192229Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0192229_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0192229Field004Chars00 ++ tail)) fragment0192229Acc00400 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0192229Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0192229_object_field_004"
  err.flush

noncomputable def fragment0192229Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0192229Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '9', '9', '2', '6', '7', '1', '0', '0', '9', '2', '7', '3', '3', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '5', '0', '6', '5', '4', '3', '7', '0', '0', '5', '1', '3', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '1', '3', '4', '7', '4', '4', '1', '8', '0', '8', '7', '9', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '4', '5', '7', '3', '2', '2', '2', '6', '6', '5', '3', '/', '1', '5', '0', '2', '6', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '2', '3', '1', '5', '7', '7', '3', '2', '8', '2', '9', '/', '1', '3', '3', '5', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '0', '4', '9', '7', '2', '1', '2', '0', '1', '5', '7', '/', '4', '8', '0', '8', '3', '6', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '4', '6', '2', '9', '4', '9', '9', '3', '2', '3', '7', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '6', '0', '4', '4', '3', '5', '7', '3', '9', '2', '1', '/', '2', '0', '0', '3', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '5', '6', '6', '7', '1', '5', '4', '2', '2', '9', '7', '/', '4', '0', '0', '6', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '5', '6', '6', '4', '4', '8', '2', '9', '1', '7', '7', '/', '4', '0', '0', '6', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0192229Acc00600 : List (String × SourceJson) := (fragment0192229Field005Key00, fragment0192229Field005Value00) :: fragment0192229Acc00500
noncomputable def fragment0192229Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '9', '2', '6', '7', '1', '0', '0', '9', '2', '7', '3', '3', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '5', '0', '6', '5', '4', '3', '7', '0', '0', '5', '1', '3', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '1', '3', '4', '7', '4', '4', '1', '8', '0', '8', '7', '9', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '6', '4', '5', '7', '3', '2', '2', '2', '6', '6', '5', '3', '/', '1', '5', '0', '2', '6', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '2', '3', '1', '5', '7', '7', '3', '2', '8', '2', '9', '/', '1', '3', '3', '5', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '0', '4', '9', '7', '2', '1', '2', '0', '1', '5', '7', '/', '4', '8', '0', '8', '3', '6', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '1', '4', '6', '2', '9', '4', '9', '9', '3', '2', '3', '7', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '6', '0', '4', '4', '3', '5', '7', '3', '9', '2', '1', '/', '2', '0', '0', '3', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '5', '6', '6', '7', '1', '5', '4', '2', '2', '9', '7', '/', '4', '0', '0', '6', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '5', '6', '6', '4', '4', '8', '2', '9', '1', '7', '7', '/', '4', '0', '0', '6', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0192229_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0192229Field005Chars00 ++ tail)) fragment0192229Acc00500 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0192229Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0192229_object_field_005"
  err.flush

noncomputable def fragment0192229Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0192229Field006Value00 : SourceJson := .str (String.ofList ['6', '9', '5', '7', '2', '5', '9', '2', '3', '3', '7', '6', '9', '8', '2', '6', '8', '6', '2', '4', '9', '7', '4', '4', '4', '7', '6', '1', '7', '8', '6', '8', '1', '4', '3', '8', '2', '8', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '0', '5', '2', '5', '8', '9', '9', '4', '8', '2', '3', '2', '2', '0', '4', '5', '6', '7', '9', '9', '2', '7', '1', '6', '1', '8', '3', '7', '4', '2', '7', '5', '3', '4', '1', '2', '4', '2', '8', '1', '0', '3', '0', '3', '0', '2', '8', '2', '4', '7', '4', '3', '3', '5', '2', '8', '5', '5', '3', '0', '5', '1', '0', '7'])
noncomputable def fragment0192229Acc00700 : List (String × SourceJson) := (fragment0192229Field006Key00, fragment0192229Field006Value00) :: fragment0192229Acc00600
noncomputable def fragment0192229Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '9', '5', '7', '2', '5', '9', '2', '3', '3', '7', '6', '9', '8', '2', '6', '8', '6', '2', '4', '9', '7', '4', '4', '4', '7', '6', '1', '7', '8', '6', '8', '1', '4', '3', '8', '2', '8', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '0', '5', '2', '5', '8', '9', '9', '4', '8', '2', '3', '2', '2', '0', '4', '5', '6', '7', '9', '9', '2', '7', '1', '6', '1', '8', '3', '7', '4', '2', '7', '5', '3', '4', '1', '2', '4', '2', '8', '1', '0', '3', '0', '3', '0', '2', '8', '2', '4', '7', '4', '3', '3', '5', '2', '8', '5', '5', '3', '0', '5', '1', '0', '7', '"', ',']

theorem object_fragment0192229_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0192229Field006Chars00 ++ tail)) fragment0192229Acc00600 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0192229Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0192229_object_field_006"
  err.flush

noncomputable def fragment0192229Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0192229Field007Value00 : SourceJson := .str (String.ofList ['8', '0', '5', '0', '0', '1', '7', '8', '1', '2', '7', '1', '0', '3', '2', '0', '1', '1', '1', '4', '9', '9', '1', '6', '4', '9', '7', '3', '0', '3', '5', '2', '5', '0', '1', '5', '9', '8', '5', '2', '8', '8', '1', '2', '4', '4', '8', '9', '6', '0', '0', '9', '5', '8', '7', '6', '3', '1', '4', '1', '6', '6', '5', '0', '0', '0', '1', '8', '1', '2', '5', '0', '4', '5', '2', '5', '9', '3', '0', '0', '2', '3', '9', '9', '1', '8', '8', '9', '6', '9', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '7', '4', '1', '1', '9', '8', '4', '7', '5', '5', '3', '1', '2', '7', '5', '5', '5', '8', '4', '5', '0', '3', '4', '3', '1', '2', '9', '8', '1', '2', '6', '7', '7', '9', '4', '1', '3', '2', '5', '9', '8', '8', '6', '4', '6', '2', '7', '1', '9', '1', '4', '2', '1', '2', '2', '2', '2', '8', '6', '3', '9', '9', '6', '7', '7', '2', '8', '4', '9', '3', '8', '1', '7', '0', '6', '2', '3', '4', '3', '4', '8', '2', '6', '0', '8', '7', '6', '6', '2', '6', '4', '3', '3', '2', '9', '2', '1', '3', '4', '3', '2', '7', '1', '1', '8', '0', '5', '7', '1', '8', '1', '6', '7', '1', '1', '5', '1', '4', '2', '9', '4', '4', '4', '8', '2', '8', '2', '2', '3', '5', '4', '7'])
noncomputable def fragment0192229Acc00800 : List (String × SourceJson) := (fragment0192229Field007Key00, fragment0192229Field007Value00) :: fragment0192229Acc00700
noncomputable def fragment0192229Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '0', '5', '0', '0', '1', '7', '8', '1', '2', '7', '1', '0', '3', '2', '0', '1', '1', '1', '4', '9', '9', '1', '6', '4', '9', '7', '3', '0', '3', '5', '2', '5', '0', '1', '5', '9', '8', '5', '2', '8', '8', '1', '2', '4', '4', '8', '9', '6', '0', '0', '9', '5', '8', '7', '6', '3', '1', '4', '1', '6', '6', '5', '0', '0', '0', '1', '8', '1', '2', '5', '0', '4', '5', '2', '5', '9', '3', '0', '0', '2', '3', '9', '9', '1', '8', '8', '9', '6', '9', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '7', '4', '1', '1', '9', '8', '4', '7', '5', '5', '3', '1', '2', '7', '5', '5', '5', '8', '4', '5', '0', '3', '4', '3', '1', '2', '9', '8', '1', '2', '6', '7', '7', '9', '4', '1', '3', '2', '5', '9', '8', '8', '6', '4', '6', '2', '7', '1', '9', '1', '4', '2', '1', '2', '2', '2', '2', '8', '6', '3', '9', '9', '6', '7', '7', '2', '8', '4', '9', '3', '8', '1', '7', '0', '6', '2', '3', '4', '3', '4', '8', '2', '6', '0', '8', '7', '6', '6', '2', '6', '4', '3', '3', '2', '9', '2', '1', '3', '4', '3', '2', '7', '1', '1', '8', '0', '5', '7', '1', '8', '1', '6', '7', '1', '1', '5', '1', '4', '2', '9', '4', '4', '4', '8', '2', '8', '2', '2', '3', '5', '4', '7', '"', ',']

theorem object_fragment0192229_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0192229Field007Chars00 ++ tail)) fragment0192229Acc00700 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0192229Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0192229_object_field_007"
  err.flush

noncomputable def fragment0192229Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0192229Field008Value00 : SourceJson := .str (String.ofList ['3', '6', '6', '1', '9', '0', '0', '4', '9', '1', '0', '2'])
noncomputable def fragment0192229Acc00900 : List (String × SourceJson) := (fragment0192229Field008Key00, fragment0192229Field008Value00) :: fragment0192229Acc00800
noncomputable def fragment0192229Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '6', '6', '1', '9', '0', '0', '4', '9', '1', '0', '2', '"', ',']

theorem object_fragment0192229_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0192229Field008Chars00 ++ tail)) fragment0192229Acc00800 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0192229Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0192229_object_field_008"
  err.flush

noncomputable def fragment0192229Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0192229Field009Value00 : SourceJson := .str (String.ofList ['1', '3', '4', '5', '2', '0', '4', '4', '3', '0', '4', '8', '2'])
noncomputable def fragment0192229Acc01000 : List (String × SourceJson) := (fragment0192229Field009Key00, fragment0192229Field009Value00) :: fragment0192229Acc00900
noncomputable def fragment0192229Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '4', '5', '2', '0', '4', '4', '3', '0', '4', '8', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0192229_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0192229Field009Chars00 ++ tail)) fragment0192229Acc00900 =
      .ok (.obj (fragment0192229Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0192229_object_field_009"
  err.flush

noncomputable def fragment0192229Chars : List Char := '{' :: (fragment0192229Field000Chars00 ++ fragment0192229Field001Chars00 ++ fragment0192229Field002Chars00 ++ fragment0192229Field003Chars00 ++ fragment0192229Field004Chars00 ++ fragment0192229Field005Chars00 ++ fragment0192229Field006Chars00 ++ fragment0192229Field007Chars00 ++ fragment0192229Field008Chars00 ++ fragment0192229Field009Chars00)
noncomputable def fragment0192229Value : SourceJson := .obj (fragment0192229Acc01000.reverse)

theorem value_fragment0192229 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 261) (fragment0192229Chars ++ tail) =
      .ok (fragment0192229Value, tail) := by
  have hinput : fragment0192229Chars ++ tail = '{' :: (fragment0192229Field000Chars00 ++ (fragment0192229Field001Chars00 ++ (fragment0192229Field002Chars00 ++ (fragment0192229Field003Chars00 ++ (fragment0192229Field004Chars00 ++ (fragment0192229Field005Chars00 ++ (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0192229Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 261) (fragment0192229Chars ++ tail) =
        SourceJson.value (fuel + 261) ('{' :: (fragment0192229Field000Chars00 ++ (fragment0192229Field001Chars00 ++ (fragment0192229Field002Chars00 ++ (fragment0192229Field003Chars00 ++ (fragment0192229Field004Chars00 ++ (fragment0192229Field005Chars00 ++ (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 261)) hinput
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0192229Field000Chars00 ++ (fragment0192229Field001Chars00 ++ (fragment0192229Field002Chars00 ++ (fragment0192229Field003Chars00 ++ (fragment0192229Field004Chars00 ++ (fragment0192229Field005Chars00 ++ (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail)))))))))))) fragment0192229Acc00000 := by rfl
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0192229Field001Chars00 ++ (fragment0192229Field002Chars00 ++ (fragment0192229Field003Chars00 ++ (fragment0192229Field004Chars00 ++ (fragment0192229Field005Chars00 ++ (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail))))))))))) fragment0192229Acc00100 := object_fragment0192229_field_000 fuel (fragment0192229Field001Chars00 ++ (fragment0192229Field002Chars00 ++ (fragment0192229Field003Chars00 ++ (fragment0192229Field004Chars00 ++ (fragment0192229Field005Chars00 ++ (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0192229Field002Chars00 ++ (fragment0192229Field003Chars00 ++ (fragment0192229Field004Chars00 ++ (fragment0192229Field005Chars00 ++ (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail)))))))))) fragment0192229Acc00200 := object_fragment0192229_field_001 fuel (fragment0192229Field002Chars00 ++ (fragment0192229Field003Chars00 ++ (fragment0192229Field004Chars00 ++ (fragment0192229Field005Chars00 ++ (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0192229Field003Chars00 ++ (fragment0192229Field004Chars00 ++ (fragment0192229Field005Chars00 ++ (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail))))))))) fragment0192229Acc00300 := object_fragment0192229_field_002 fuel (fragment0192229Field003Chars00 ++ (fragment0192229Field004Chars00 ++ (fragment0192229Field005Chars00 ++ (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0192229Field004Chars00 ++ (fragment0192229Field005Chars00 ++ (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail)))))))) fragment0192229Acc00400 := object_fragment0192229_field_003 fuel (fragment0192229Field004Chars00 ++ (fragment0192229Field005Chars00 ++ (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0192229Field005Chars00 ++ (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail))))))) fragment0192229Acc00500 := object_fragment0192229_field_004 fuel (fragment0192229Field005Chars00 ++ (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail)))))) fragment0192229Acc00600 := object_fragment0192229_field_005 fuel (fragment0192229Field006Chars00 ++ (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail))))) fragment0192229Acc00700 := object_fragment0192229_field_006 fuel (fragment0192229Field007Chars00 ++ (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail)))) fragment0192229Acc00800 := object_fragment0192229_field_007 fuel (fragment0192229Field008Chars00 ++ (fragment0192229Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0192229Field009Chars00 ++ (tail))) fragment0192229Acc00900 := object_fragment0192229_field_008 fuel (fragment0192229Field009Chars00 ++ (tail))
    _ = .ok (fragment0192229Value, tail) := object_fragment0192229_field_009 fuel (tail)

noncomputable def fragment0193877Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0193877Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0193877Field000Value00 : SourceJson := .number (String.ofList ['5', '2'])
noncomputable def fragment0193877Acc00100 : List (String × SourceJson) := (fragment0193877Field000Key00, fragment0193877Field000Value00) :: fragment0193877Acc00000
noncomputable def fragment0193877Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '2', ',']

theorem object_fragment0193877_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0193877Field000Chars00 ++ tail)) fragment0193877Acc00000 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0193877Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193877_object_field_000"
  err.flush

noncomputable def fragment0193877Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0193877Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0193877Acc00200 : List (String × SourceJson) := (fragment0193877Field001Key00, fragment0193877Field001Value00) :: fragment0193877Acc00100
noncomputable def fragment0193877Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0193877_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0193877Field001Chars00 ++ tail)) fragment0193877Acc00100 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0193877Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193877_object_field_001"
  err.flush

noncomputable def fragment0193877Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0193877Field002Value00 : SourceJson := .str (String.ofList ['2', '1', '0', '2', '9', '1', '5', '4', '6', '4', '2', '9', '7', '8', '9', '2', '5', '4', '3', '8', '2', '0', '1', '6', '9', '2', '0', '8', '5', '2', '0', '4', '7', '5', '1', '3', '/', '2', '1', '6', '3', '2', '6', '8', '1', '4', '5', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0193877Acc00300 : List (String × SourceJson) := (fragment0193877Field002Key00, fragment0193877Field002Value00) :: fragment0193877Acc00200
noncomputable def fragment0193877Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '1', '0', '2', '9', '1', '5', '4', '6', '4', '2', '9', '7', '8', '9', '2', '5', '4', '3', '8', '2', '0', '1', '6', '9', '2', '0', '8', '5', '2', '0', '4', '7', '5', '1', '3', '/', '2', '1', '6', '3', '2', '6', '8', '1', '4', '5', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0193877_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0193877Field002Chars00 ++ tail)) fragment0193877Acc00200 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0193877Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193877_object_field_002"
  err.flush

noncomputable def fragment0193877Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0193877Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0193877Acc00400 : List (String × SourceJson) := (fragment0193877Field003Key00, fragment0193877Field003Value00) :: fragment0193877Acc00300
noncomputable def fragment0193877Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0193877_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0193877Field003Chars00 ++ tail)) fragment0193877Acc00300 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0193877Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193877_object_field_003"
  err.flush

noncomputable def fragment0193877Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0193877Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0193877Acc00500 : List (String × SourceJson) := (fragment0193877Field004Key00, fragment0193877Field004Value00) :: fragment0193877Acc00400
noncomputable def fragment0193877Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0193877_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0193877Field004Chars00 ++ tail)) fragment0193877Acc00400 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0193877Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193877_object_field_004"
  err.flush

noncomputable def fragment0193877Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0193877Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '4', '4', '8', '5', '3', '9', '2', '6', '3', '3', '7', '2', '9', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '7', '7', '5', '3', '0', '9', '4', '3', '7', '6', '1', '9', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '3', '7', '6', '2', '0', '8', '0', '7', '9', '5', '2', '7', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '6', '9', '1', '8', '1', '8', '9', '1', '4', '8', '8', '9', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '3', '5', '1', '9', '3', '7', '2', '1', '3', '8', '2', '7', '/', '4', '0', '0', '6', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '2', '8', '3', '3', '9', '6', '7', '0', '2', '1', '3', '7', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '5', '7', '6', '2', '5', '8', '7', '1', '6', '8', '4', '7', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '7', '0', '4', '3', '1', '4', '8', '1', '7', '9', '1', '/', '2', '0', '0', '3', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '2', '5', '2', '2', '8', '8', '3', '6', '4', '1', '1', '/', '2', '0', '0', '3', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '7', '5', '0', '7', '1', '8', '2', '6', '6', '1', '7', '/', '6', '6', '7', '8', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0193877Acc00600 : List (String × SourceJson) := (fragment0193877Field005Key00, fragment0193877Field005Value00) :: fragment0193877Acc00500
noncomputable def fragment0193877Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '4', '8', '5', '3', '9', '2', '6', '3', '3', '7', '2', '9', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '7', '7', '5', '3', '0', '9', '4', '3', '7', '6', '1', '9', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '3', '7', '6', '2', '0', '8', '0', '7', '9', '5', '2', '7', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '6', '9', '1', '8', '1', '8', '9', '1', '4', '8', '8', '9', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '3', '5', '1', '9', '3', '7', '2', '1', '3', '8', '2', '7', '/', '4', '0', '0', '6', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '8', '3', '3', '9', '6', '7', '0', '2', '1', '3', '7', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '5', '7', '6', '2', '5', '8', '7', '1', '6', '8', '4', '7', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '7', '0', '4', '3', '1', '4', '8', '1', '7', '9', '1', '/', '2', '0', '0', '3', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '2', '5', '2', '2', '8', '8', '3', '6', '4', '1', '1', '/', '2', '0', '0', '3', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '5', '0', '7', '1', '8', '2', '6', '6', '1', '7', '/', '6', '6', '7', '8', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0193877_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0193877Field005Chars00 ++ tail)) fragment0193877Acc00500 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0193877Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193877_object_field_005"
  err.flush

noncomputable def fragment0193877Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0193877Field006Value00 : SourceJson := .str (String.ofList ['4', '1', '6', '9', '4', '9', '5', '7', '2', '7', '3', '3', '2', '3', '3', '2', '9', '7', '2', '3', '7', '2', '6', '8', '4', '4', '4', '0', '7', '1', '6', '9', '9', '2', '6', '0', '8', '2', '0', '4', '8', '0', '0', '0', '0', '0', '/', '1', '0', '0', '1', '1', '8', '0', '0', '5', '2', '3', '1', '7', '3', '0', '7', '1', '4', '1', '2', '0', '2', '6', '4', '3', '4', '4', '2', '3', '5', '1', '8', '9', '4', '9', '8', '0', '2', '0', '4', '1', '0', '4', '4', '3', '9', '0', '8', '6', '1', '4', '5', '4', '1', '2', '4', '7', '6', '0', '7', '7', '9', '4', '9'])
noncomputable def fragment0193877Acc00700 : List (String × SourceJson) := (fragment0193877Field006Key00, fragment0193877Field006Value00) :: fragment0193877Acc00600
noncomputable def fragment0193877Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '1', '6', '9', '4', '9', '5', '7', '2', '7', '3', '3', '2', '3', '3', '2', '9', '7', '2', '3', '7', '2', '6', '8', '4', '4', '4', '0', '7', '1', '6', '9', '9', '2', '6', '0', '8', '2', '0', '4', '8', '0', '0', '0', '0', '0', '/', '1', '0', '0', '1', '1', '8', '0', '0', '5', '2', '3', '1', '7', '3', '0', '7', '1', '4', '1', '2', '0', '2', '6', '4', '3', '4', '4', '2', '3', '5', '1', '8', '9', '4', '9', '8', '0', '2', '0', '4', '1', '0', '4', '4', '3', '9', '0', '8', '6', '1', '4', '5', '4', '1', '2', '4', '7', '6', '0', '7', '7', '9', '4', '9', '"', ',']

theorem object_fragment0193877_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0193877Field006Chars00 ++ tail)) fragment0193877Acc00600 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0193877Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193877_object_field_006"
  err.flush

noncomputable def fragment0193877Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0193877Field007Value00 : SourceJson := .str (String.ofList ['2', '1', '0', '2', '7', '8', '4', '1', '1', '5', '5', '5', '4', '3', '4', '7', '6', '9', '8', '0', '4', '5', '7', '1', '8', '3', '5', '3', '2', '8', '2', '4', '8', '9', '0', '4', '0', '3', '2', '8', '4', '1', '5', '0', '1', '1', '5', '5', '9', '0', '2', '0', '5', '2', '6', '6', '2', '0', '3', '7', '1', '7', '2', '9', '8', '3', '3', '9', '4', '2', '8', '8', '7', '7', '8', '2', '4', '2', '2', '9', '4', '3', '4', '0', '8', '6', '5', '2', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '9', '3', '4', '0', '2', '6', '2', '6', '9', '6', '6', '8', '9', '8', '3', '1', '0', '7', '9', '4', '6', '7', '6', '2', '5', '9', '4', '0', '3', '7', '7', '3', '9', '0', '2', '7', '8', '2', '3', '6', '2', '1', '9', '6', '1', '0', '1', '2', '1', '3', '8', '6', '4', '7', '1', '5', '0', '9', '2', '7', '8', '1', '7', '7', '5', '5', '0', '3', '0', '4', '7', '0', '5', '0', '7', '0', '9', '7', '1', '5', '3', '5', '4', '8', '7', '2', '4', '7', '2', '4', '5', '5', '9', '8', '0', '4', '8', '9', '1', '0', '2', '4', '0', '4', '2', '1', '4', '1', '3', '2', '3', '3', '7', '8', '2', '8', '1', '9', '8', '2', '4', '6', '5', '4', '9', '2', '3', '5', '1'])
noncomputable def fragment0193877Acc00800 : List (String × SourceJson) := (fragment0193877Field007Key00, fragment0193877Field007Value00) :: fragment0193877Acc00700
noncomputable def fragment0193877Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '0', '2', '7', '8', '4', '1', '1', '5', '5', '5', '4', '3', '4', '7', '6', '9', '8', '0', '4', '5', '7', '1', '8', '3', '5', '3', '2', '8', '2', '4', '8', '9', '0', '4', '0', '3', '2', '8', '4', '1', '5', '0', '1', '1', '5', '5', '9', '0', '2', '0', '5', '2', '6', '6', '2', '0', '3', '7', '1', '7', '2', '9', '8', '3', '3', '9', '4', '2', '8', '8', '7', '7', '8', '2', '4', '2', '2', '9', '4', '3', '4', '0', '8', '6', '5', '2', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '9', '3', '4', '0', '2', '6', '2', '6', '9', '6', '6', '8', '9', '8', '3', '1', '0', '7', '9', '4', '6', '7', '6', '2', '5', '9', '4', '0', '3', '7', '7', '3', '9', '0', '2', '7', '8', '2', '3', '6', '2', '1', '9', '6', '1', '0', '1', '2', '1', '3', '8', '6', '4', '7', '1', '5', '0', '9', '2', '7', '8', '1', '7', '7', '5', '5', '0', '3', '0', '4', '7', '0', '5', '0', '7', '0', '9', '7', '1', '5', '3', '5', '4', '8', '7', '2', '4', '7', '2', '4', '5', '5', '9', '8', '0', '4', '8', '9', '1', '0', '2', '4', '0', '4', '2', '1', '4', '1', '3', '2', '3', '3', '7', '8', '2', '8', '1', '9', '8', '2', '4', '6', '5', '4', '9', '2', '3', '5', '1', '"', ',']

theorem object_fragment0193877_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0193877Field007Chars00 ++ tail)) fragment0193877Acc00700 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0193877Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193877_object_field_007"
  err.flush

noncomputable def fragment0193877Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0193877Field008Value00 : SourceJson := .str (String.ofList ['3', '2', '9', '9', '5', '2', '1', '2', '4', '3', '1', '8'])
noncomputable def fragment0193877Acc00900 : List (String × SourceJson) := (fragment0193877Field008Key00, fragment0193877Field008Value00) :: fragment0193877Acc00800
noncomputable def fragment0193877Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '9', '9', '5', '2', '1', '2', '4', '3', '1', '8', '"', ',']

theorem object_fragment0193877_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0193877Field008Chars00 ++ tail)) fragment0193877Acc00800 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0193877Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193877_object_field_008"
  err.flush

noncomputable def fragment0193877Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0193877Field009Value00 : SourceJson := .str (String.ofList ['1', '1', '9', '5', '6', '3', '2', '3', '2', '0', '5', '8', '9'])
noncomputable def fragment0193877Acc01000 : List (String × SourceJson) := (fragment0193877Field009Key00, fragment0193877Field009Value00) :: fragment0193877Acc00900
noncomputable def fragment0193877Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '9', '5', '6', '3', '2', '3', '2', '0', '5', '8', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0193877_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0193877Field009Chars00 ++ tail)) fragment0193877Acc00900 =
      .ok (.obj (fragment0193877Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193877_object_field_009"
  err.flush

noncomputable def fragment0193877Chars : List Char := '{' :: (fragment0193877Field000Chars00 ++ fragment0193877Field001Chars00 ++ fragment0193877Field002Chars00 ++ fragment0193877Field003Chars00 ++ fragment0193877Field004Chars00 ++ fragment0193877Field005Chars00 ++ fragment0193877Field006Chars00 ++ fragment0193877Field007Chars00 ++ fragment0193877Field008Chars00 ++ fragment0193877Field009Chars00)
noncomputable def fragment0193877Value : SourceJson := .obj (fragment0193877Acc01000.reverse)

theorem value_fragment0193877 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 257) (fragment0193877Chars ++ tail) =
      .ok (fragment0193877Value, tail) := by
  have hinput : fragment0193877Chars ++ tail = '{' :: (fragment0193877Field000Chars00 ++ (fragment0193877Field001Chars00 ++ (fragment0193877Field002Chars00 ++ (fragment0193877Field003Chars00 ++ (fragment0193877Field004Chars00 ++ (fragment0193877Field005Chars00 ++ (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0193877Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 257) (fragment0193877Chars ++ tail) =
        SourceJson.value (fuel + 257) ('{' :: (fragment0193877Field000Chars00 ++ (fragment0193877Field001Chars00 ++ (fragment0193877Field002Chars00 ++ (fragment0193877Field003Chars00 ++ (fragment0193877Field004Chars00 ++ (fragment0193877Field005Chars00 ++ (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 257)) hinput
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0193877Field000Chars00 ++ (fragment0193877Field001Chars00 ++ (fragment0193877Field002Chars00 ++ (fragment0193877Field003Chars00 ++ (fragment0193877Field004Chars00 ++ (fragment0193877Field005Chars00 ++ (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail)))))))))))) fragment0193877Acc00000 := by rfl
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0193877Field001Chars00 ++ (fragment0193877Field002Chars00 ++ (fragment0193877Field003Chars00 ++ (fragment0193877Field004Chars00 ++ (fragment0193877Field005Chars00 ++ (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail))))))))))) fragment0193877Acc00100 := object_fragment0193877_field_000 fuel (fragment0193877Field001Chars00 ++ (fragment0193877Field002Chars00 ++ (fragment0193877Field003Chars00 ++ (fragment0193877Field004Chars00 ++ (fragment0193877Field005Chars00 ++ (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0193877Field002Chars00 ++ (fragment0193877Field003Chars00 ++ (fragment0193877Field004Chars00 ++ (fragment0193877Field005Chars00 ++ (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail)))))))))) fragment0193877Acc00200 := object_fragment0193877_field_001 fuel (fragment0193877Field002Chars00 ++ (fragment0193877Field003Chars00 ++ (fragment0193877Field004Chars00 ++ (fragment0193877Field005Chars00 ++ (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0193877Field003Chars00 ++ (fragment0193877Field004Chars00 ++ (fragment0193877Field005Chars00 ++ (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail))))))))) fragment0193877Acc00300 := object_fragment0193877_field_002 fuel (fragment0193877Field003Chars00 ++ (fragment0193877Field004Chars00 ++ (fragment0193877Field005Chars00 ++ (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0193877Field004Chars00 ++ (fragment0193877Field005Chars00 ++ (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail)))))))) fragment0193877Acc00400 := object_fragment0193877_field_003 fuel (fragment0193877Field004Chars00 ++ (fragment0193877Field005Chars00 ++ (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0193877Field005Chars00 ++ (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail))))))) fragment0193877Acc00500 := object_fragment0193877_field_004 fuel (fragment0193877Field005Chars00 ++ (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail)))))) fragment0193877Acc00600 := object_fragment0193877_field_005 fuel (fragment0193877Field006Chars00 ++ (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail))))) fragment0193877Acc00700 := object_fragment0193877_field_006 fuel (fragment0193877Field007Chars00 ++ (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail)))) fragment0193877Acc00800 := object_fragment0193877_field_007 fuel (fragment0193877Field008Chars00 ++ (fragment0193877Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0193877Field009Chars00 ++ (tail))) fragment0193877Acc00900 := object_fragment0193877_field_008 fuel (fragment0193877Field009Chars00 ++ (tail))
    _ = .ok (fragment0193877Value, tail) := object_fragment0193877_field_009 fuel (tail)

noncomputable def fragment0195514Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0195514Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0195514Field000Value00 : SourceJson := .number (String.ofList ['5', '3'])
noncomputable def fragment0195514Acc00100 : List (String × SourceJson) := (fragment0195514Field000Key00, fragment0195514Field000Value00) :: fragment0195514Acc00000
noncomputable def fragment0195514Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '3', ',']

theorem object_fragment0195514_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 282) (SourceJson.white (fragment0195514Field000Chars00 ++ tail)) fragment0195514Acc00000 =
      SourceJson.object (fuel + 281) (SourceJson.white tail) fragment0195514Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195514_object_field_000"
  err.flush

noncomputable def fragment0195514Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0195514Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['1'])]
noncomputable def fragment0195514Acc00200 : List (String × SourceJson) := (fragment0195514Field001Key00, fragment0195514Field001Value00) :: fragment0195514Acc00100
noncomputable def fragment0195514Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0195514_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 281) (SourceJson.white (fragment0195514Field001Chars00 ++ tail)) fragment0195514Acc00100 =
      SourceJson.object (fuel + 280) (SourceJson.white tail) fragment0195514Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195514_object_field_001"
  err.flush

noncomputable def fragment0195514Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0195514Field002Value00 : SourceJson := .str (String.ofList ['4', '3', '0', '7', '7', '7', '1', '5', '5', '2', '7', '7', '7', '6', '2', '3', '0', '7', '5', '7', '0', '2', '2', '5', '0', '0', '1', '8', '9', '9', '1', '2', '8', '1', '/', '6', '4', '5', '9', '7', '5', '9', '0', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0195514Acc00300 : List (String × SourceJson) := (fragment0195514Field002Key00, fragment0195514Field002Value00) :: fragment0195514Acc00200
noncomputable def fragment0195514Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '3', '0', '7', '7', '7', '1', '5', '5', '2', '7', '7', '7', '6', '2', '3', '0', '7', '5', '7', '0', '2', '2', '5', '0', '0', '1', '8', '9', '9', '1', '2', '8', '1', '/', '6', '4', '5', '9', '7', '5', '9', '0', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0195514_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 280) (SourceJson.white (fragment0195514Field002Chars00 ++ tail)) fragment0195514Acc00200 =
      SourceJson.object (fuel + 279) (SourceJson.white tail) fragment0195514Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195514_object_field_002"
  err.flush

noncomputable def fragment0195514Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0195514Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0195514Acc00400 : List (String × SourceJson) := (fragment0195514Field003Key00, fragment0195514Field003Value00) :: fragment0195514Acc00300
noncomputable def fragment0195514Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0195514_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 279) (SourceJson.white (fragment0195514Field003Chars00 ++ tail)) fragment0195514Acc00300 =
      SourceJson.object (fuel + 278) (SourceJson.white tail) fragment0195514Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195514_object_field_003"
  err.flush

noncomputable def fragment0195514Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0195514Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0195514Acc00500 : List (String × SourceJson) := (fragment0195514Field004Key00, fragment0195514Field004Value00) :: fragment0195514Acc00400
noncomputable def fragment0195514Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0195514_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 278) (SourceJson.white (fragment0195514Field004Chars00 ++ tail)) fragment0195514Acc00400 =
      SourceJson.object (fuel + 277) (SourceJson.white tail) fragment0195514Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195514_object_field_004"
  err.flush

noncomputable def fragment0195514Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0195514Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '1', '4', '9', '3', '1', '2', '0', '4', '5', '0', '6', '7', '0', '0', '1', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '8', '8', '8', '6', '3', '1', '4', '0', '8', '7', '6', '5', '9', '/', '3', '2', '3', '0', '6', '1', '7', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '4', '3', '0', '1', '5', '3', '7', '0', '8', '9', '9', '3', '/', '2', '8', '7', '1', '6', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '1', '2', '6', '9', '7', '4', '1', '8', '1', '5', '1', '2', '2', '3', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '9', '1', '0', '5', '4', '5', '0', '3', '1', '8', '9', '6', '7', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '2', '3', '9', '5', '7', '0', '5', '0', '8', '3', '8', '7', '/', '2', '8', '7', '1', '6', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '5', '5', '2', '4', '7', '0', '9', '5', '1', '2', '3', '9', '3', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '8', '6', '1', '5', '4', '4', '0', '1', '6', '2', '9', '1', '/', '6', '4', '6', '1', '2', '3', '5', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '5', '3', '8', '1', '5', '6', '9', '4', '0', '6', '1', '3', '/', '3', '2', '3', '0', '6', '1', '7', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '5', '3', '7', '9', '4', '1', '5', '6', '6', '0', '8', '3', '/', '3', '2', '3', '0', '6', '1', '7', '9', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0195514Acc00600 : List (String × SourceJson) := (fragment0195514Field005Key00, fragment0195514Field005Value00) :: fragment0195514Acc00500
noncomputable def fragment0195514Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '9', '3', '1', '2', '0', '4', '5', '0', '6', '7', '0', '0', '1', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '8', '8', '8', '6', '3', '1', '4', '0', '8', '7', '6', '5', '9', '/', '3', '2', '3', '0', '6', '1', '7', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '4', '3', '0', '1', '5', '3', '7', '0', '8', '9', '9', '3', '/', '2', '8', '7', '1', '6', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '2', '6', '9', '7', '4', '1', '8', '1', '5', '1', '2', '2', '3', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '9', '1', '0', '5', '4', '5', '0', '3', '1', '8', '9', '6', '7', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '2', '3', '9', '5', '7', '0', '5', '0', '8', '3', '8', '7', '/', '2', '8', '7', '1', '6', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '5', '5', '2', '4', '7', '0', '9', '5', '1', '2', '3', '9', '3', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '8', '6', '1', '5', '4', '4', '0', '1', '6', '2', '9', '1', '/', '6', '4', '6', '1', '2', '3', '5', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '5', '3', '8', '1', '5', '6', '9', '4', '0', '6', '1', '3', '/', '3', '2', '3', '0', '6', '1', '7', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '5', '3', '7', '9', '4', '1', '5', '6', '6', '0', '8', '3', '/', '3', '2', '3', '0', '6', '1', '7', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0195514_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 277) (SourceJson.white (fragment0195514Field005Chars00 ++ tail)) fragment0195514Acc00500 =
      SourceJson.object (fuel + 276) (SourceJson.white tail) fragment0195514Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195514_object_field_005"
  err.flush

noncomputable def fragment0195514Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0195514Field006Value00 : SourceJson := .str (String.ofList ['9', '9', '0', '3', '0', '2', '5', '4', '3', '5', '6', '9', '6', '7', '6', '0', '0', '1', '0', '5', '8', '7', '6', '0', '6', '6', '6', '9', '6', '9', '3', '3', '5', '4', '2', '0', '5', '8', '0', '3', '9', '4', '2', '3', '1', '1', '2', '5', '0', '0', '0', '/', '2', '8', '2', '5', '9', '5', '7', '3', '6', '2', '7', '9', '0', '3', '3', '3', '7', '6', '6', '4', '9', '1', '7', '7', '8', '9', '4', '2', '7', '0', '9', '0', '0', '9', '8', '6', '5', '9', '1', '8', '7', '3', '8', '6', '9', '3', '2', '9', '2', '2', '8', '3', '4', '8', '7', '3', '8', '3', '9', '3', '5', '3', '2', '2', '0', '1', '1', '6', '9'])
noncomputable def fragment0195514Acc00700 : List (String × SourceJson) := (fragment0195514Field006Key00, fragment0195514Field006Value00) :: fragment0195514Acc00600
noncomputable def fragment0195514Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '9', '0', '3', '0', '2', '5', '4', '3', '5', '6', '9', '6', '7', '6', '0', '0', '1', '0', '5', '8', '7', '6', '0', '6', '6', '6', '9', '6', '9', '3', '3', '5', '4', '2', '0', '5', '8', '0', '3', '9', '4', '2', '3', '1', '1', '2', '5', '0', '0', '0', '/', '2', '8', '2', '5', '9', '5', '7', '3', '6', '2', '7', '9', '0', '3', '3', '3', '7', '6', '6', '4', '9', '1', '7', '7', '8', '9', '4', '2', '7', '0', '9', '0', '0', '9', '8', '6', '5', '9', '1', '8', '7', '3', '8', '6', '9', '3', '2', '9', '2', '2', '8', '3', '4', '8', '7', '3', '8', '3', '9', '3', '5', '3', '2', '2', '0', '1', '1', '6', '9', '"', ',']

theorem object_fragment0195514_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 276) (SourceJson.white (fragment0195514Field006Chars00 ++ tail)) fragment0195514Acc00600 =
      SourceJson.object (fuel + 275) (SourceJson.white tail) fragment0195514Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195514_object_field_006"
  err.flush

noncomputable def fragment0195514Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0195514Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '9', '3', '6', '8', '5', '0', '8', '0', '0', '3', '5', '2', '7', '5', '1', '3', '9', '7', '6', '0', '8', '5', '9', '1', '0', '6', '4', '8', '9', '9', '7', '4', '9', '1', '5', '3', '2', '3', '2', '1', '9', '2', '5', '5', '8', '3', '0', '5', '3', '8', '7', '8', '0', '2', '8', '2', '0', '9', '4', '7', '5', '9', '4', '2', '7', '6', '0', '8', '4', '5', '9', '4', '8', '0', '5', '3', '3', '3', '0', '2', '8', '1', '0', '4', '1', '9', '7', '3', '4', '6', '8', '8', '0', '6', '3', '8', '2', '4', '1', '4', '0', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '8', '7', '9', '0', '8', '6', '2', '7', '1', '2', '9', '4', '4', '1', '0', '6', '4', '1', '3', '0', '1', '9', '6', '6', '2', '2', '8', '9', '5', '7', '6', '2', '3', '9', '1', '5', '1', '4', '5', '6', '7', '4', '9', '1', '5', '9', '1', '5', '3', '6', '8', '2', '1', '6', '4', '5', '2', '2', '6', '1', '5', '0', '7', '0', '9', '0', '5', '6', '4', '7', '6', '9', '2', '3', '9', '4', '1', '6', '9', '1', '2', '9', '2', '3', '8', '3', '5', '8', '1', '0', '8', '0', '6', '2', '3', '0', '6', '3', '1', '7', '6', '9', '1', '8', '7', '8', '4', '7', '9', '4', '9', '7', '6', '2', '9', '8', '9', '0', '8', '4', '5', '4', '7', '6', '9', '4', '6', '6', '8', '6', '3', '8', '1', '8', '0', '1', '4', '6', '4', '5', '1', '1'])
noncomputable def fragment0195514Acc00800 : List (String × SourceJson) := (fragment0195514Field007Key00, fragment0195514Field007Value00) :: fragment0195514Acc00700
noncomputable def fragment0195514Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '9', '3', '6', '8', '5', '0', '8', '0', '0', '3', '5', '2', '7', '5', '1', '3', '9', '7', '6', '0', '8', '5', '9', '1', '0', '6', '4', '8', '9', '9', '7', '4', '9', '1', '5', '3', '2', '3', '2', '1', '9', '2', '5', '5', '8', '3', '0', '5', '3', '8', '7', '8', '0', '2', '8', '2', '0', '9', '4', '7', '5', '9', '4', '2', '7', '6', '0', '8', '4', '5', '9', '4', '8', '0', '5', '3', '3', '3', '0', '2', '8', '1', '0', '4', '1', '9', '7', '3', '4', '6', '8', '8', '0', '6', '3', '8', '2', '4', '1', '4', '0', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '8', '7', '9', '0', '8', '6', '2', '7', '1', '2', '9', '4', '4', '1', '0', '6', '4', '1', '3', '0', '1', '9', '6', '6', '2', '2', '8', '9', '5', '7', '6', '2', '3', '9', '1', '5', '1', '4', '5', '6', '7', '4', '9', '1', '5', '9', '1', '5', '3', '6', '8', '2', '1', '6', '4', '5', '2', '2', '6', '1', '5', '0', '7', '0', '9', '0', '5', '6', '4', '7', '6', '9', '2', '3', '9', '4', '1', '6', '9', '1', '2', '9', '2', '3', '8', '3', '5', '8', '1', '0', '8', '0', '6', '2', '3', '0', '6', '3', '1', '7', '6', '9', '1', '8', '7', '8', '4', '7', '9', '4', '9', '7', '6', '2', '9', '8', '9', '0', '8', '4', '5', '4', '7', '6', '9', '4', '6', '6', '8', '6', '3', '8', '1', '8', '0', '1', '4', '6', '4', '5', '1', '1', '"', ',']

theorem object_fragment0195514_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 275) (SourceJson.white (fragment0195514Field007Chars00 ++ tail)) fragment0195514Acc00700 =
      SourceJson.object (fuel + 274) (SourceJson.white tail) fragment0195514Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195514_object_field_007"
  err.flush

noncomputable def fragment0195514Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0195514Field008Value00 : SourceJson := .str (String.ofList ['2', '7', '7', '6', '3', '9', '8', '9', '6', '1', '0', '5'])
noncomputable def fragment0195514Acc00900 : List (String × SourceJson) := (fragment0195514Field008Key00, fragment0195514Field008Value00) :: fragment0195514Acc00800
noncomputable def fragment0195514Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '7', '6', '3', '9', '8', '9', '6', '1', '0', '5', '"', ',']

theorem object_fragment0195514_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 274) (SourceJson.white (fragment0195514Field008Chars00 ++ tail)) fragment0195514Acc00800 =
      SourceJson.object (fuel + 273) (SourceJson.white tail) fragment0195514Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195514_object_field_008"
  err.flush

noncomputable def fragment0195514Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0195514Field009Value00 : SourceJson := .str (String.ofList ['8', '6', '9', '3', '1', '4', '5', '1', '0', '0', '0', '0'])
noncomputable def fragment0195514Acc01000 : List (String × SourceJson) := (fragment0195514Field009Key00, fragment0195514Field009Value00) :: fragment0195514Acc00900
noncomputable def fragment0195514Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '6', '9', '3', '1', '4', '5', '1', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0195514_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 273) (SourceJson.white (fragment0195514Field009Chars00 ++ tail)) fragment0195514Acc00900 =
      .ok (.obj (fragment0195514Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195514_object_field_009"
  err.flush

noncomputable def fragment0195514Chars : List Char := '{' :: (fragment0195514Field000Chars00 ++ fragment0195514Field001Chars00 ++ fragment0195514Field002Chars00 ++ fragment0195514Field003Chars00 ++ fragment0195514Field004Chars00 ++ fragment0195514Field005Chars00 ++ fragment0195514Field006Chars00 ++ fragment0195514Field007Chars00 ++ fragment0195514Field008Chars00 ++ fragment0195514Field009Chars00)
noncomputable def fragment0195514Value : SourceJson := .obj (fragment0195514Acc01000.reverse)

theorem value_fragment0195514 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 283) (fragment0195514Chars ++ tail) =
      .ok (fragment0195514Value, tail) := by
  have hinput : fragment0195514Chars ++ tail = '{' :: (fragment0195514Field000Chars00 ++ (fragment0195514Field001Chars00 ++ (fragment0195514Field002Chars00 ++ (fragment0195514Field003Chars00 ++ (fragment0195514Field004Chars00 ++ (fragment0195514Field005Chars00 ++ (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0195514Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 283) (fragment0195514Chars ++ tail) =
        SourceJson.value (fuel + 283) ('{' :: (fragment0195514Field000Chars00 ++ (fragment0195514Field001Chars00 ++ (fragment0195514Field002Chars00 ++ (fragment0195514Field003Chars00 ++ (fragment0195514Field004Chars00 ++ (fragment0195514Field005Chars00 ++ (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 283)) hinput
    _ = SourceJson.object (fuel + 282) (SourceJson.white (fragment0195514Field000Chars00 ++ (fragment0195514Field001Chars00 ++ (fragment0195514Field002Chars00 ++ (fragment0195514Field003Chars00 ++ (fragment0195514Field004Chars00 ++ (fragment0195514Field005Chars00 ++ (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail)))))))))))) fragment0195514Acc00000 := by rfl
    _ = SourceJson.object (fuel + 281) (SourceJson.white (fragment0195514Field001Chars00 ++ (fragment0195514Field002Chars00 ++ (fragment0195514Field003Chars00 ++ (fragment0195514Field004Chars00 ++ (fragment0195514Field005Chars00 ++ (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail))))))))))) fragment0195514Acc00100 := object_fragment0195514_field_000 fuel (fragment0195514Field001Chars00 ++ (fragment0195514Field002Chars00 ++ (fragment0195514Field003Chars00 ++ (fragment0195514Field004Chars00 ++ (fragment0195514Field005Chars00 ++ (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 280) (SourceJson.white (fragment0195514Field002Chars00 ++ (fragment0195514Field003Chars00 ++ (fragment0195514Field004Chars00 ++ (fragment0195514Field005Chars00 ++ (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail)))))))))) fragment0195514Acc00200 := object_fragment0195514_field_001 fuel (fragment0195514Field002Chars00 ++ (fragment0195514Field003Chars00 ++ (fragment0195514Field004Chars00 ++ (fragment0195514Field005Chars00 ++ (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 279) (SourceJson.white (fragment0195514Field003Chars00 ++ (fragment0195514Field004Chars00 ++ (fragment0195514Field005Chars00 ++ (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail))))))))) fragment0195514Acc00300 := object_fragment0195514_field_002 fuel (fragment0195514Field003Chars00 ++ (fragment0195514Field004Chars00 ++ (fragment0195514Field005Chars00 ++ (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 278) (SourceJson.white (fragment0195514Field004Chars00 ++ (fragment0195514Field005Chars00 ++ (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail)))))))) fragment0195514Acc00400 := object_fragment0195514_field_003 fuel (fragment0195514Field004Chars00 ++ (fragment0195514Field005Chars00 ++ (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 277) (SourceJson.white (fragment0195514Field005Chars00 ++ (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail))))))) fragment0195514Acc00500 := object_fragment0195514_field_004 fuel (fragment0195514Field005Chars00 ++ (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 276) (SourceJson.white (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail)))))) fragment0195514Acc00600 := object_fragment0195514_field_005 fuel (fragment0195514Field006Chars00 ++ (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 275) (SourceJson.white (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail))))) fragment0195514Acc00700 := object_fragment0195514_field_006 fuel (fragment0195514Field007Chars00 ++ (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 274) (SourceJson.white (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail)))) fragment0195514Acc00800 := object_fragment0195514_field_007 fuel (fragment0195514Field008Chars00 ++ (fragment0195514Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 273) (SourceJson.white (fragment0195514Field009Chars00 ++ (tail))) fragment0195514Acc00900 := object_fragment0195514_field_008 fuel (fragment0195514Field009Chars00 ++ (tail))
    _ = .ok (fragment0195514Value, tail) := object_fragment0195514_field_009 fuel (tail)

noncomputable def fragment0197204Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0197204Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0197204Field000Value00 : SourceJson := .number (String.ofList ['5', '4'])
noncomputable def fragment0197204Acc00100 : List (String × SourceJson) := (fragment0197204Field000Key00, fragment0197204Field000Value00) :: fragment0197204Acc00000
noncomputable def fragment0197204Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '4', ',']

theorem object_fragment0197204_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0197204Field000Chars00 ++ tail)) fragment0197204Acc00000 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0197204Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197204_object_field_000"
  err.flush

noncomputable def fragment0197204Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0197204Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['5']), .number (String.ofList ['1'])]
noncomputable def fragment0197204Acc00200 : List (String × SourceJson) := (fragment0197204Field001Key00, fragment0197204Field001Value00) :: fragment0197204Acc00100
noncomputable def fragment0197204Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0197204_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0197204Field001Chars00 ++ tail)) fragment0197204Acc00100 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0197204Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197204_object_field_001"
  err.flush

noncomputable def fragment0197204Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0197204Field002Value00 : SourceJson := .str (String.ofList ['2', '2', '6', '7', '0', '7', '5', '5', '7', '1', '4', '2', '7', '0', '2', '2', '2', '5', '8', '4', '9', '5', '1', '2', '0', '5', '4', '5', '1', '2', '1', '7', '9', '7', '/', '3', '9', '7', '1', '1', '6', '3', '3', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0197204Acc00300 : List (String × SourceJson) := (fragment0197204Field002Key00, fragment0197204Field002Value00) :: fragment0197204Acc00200
noncomputable def fragment0197204Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '2', '6', '7', '0', '7', '5', '5', '7', '1', '4', '2', '7', '0', '2', '2', '2', '5', '8', '4', '9', '5', '1', '2', '0', '5', '4', '5', '1', '2', '1', '7', '9', '7', '/', '3', '9', '7', '1', '1', '6', '3', '3', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0197204_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0197204Field002Chars00 ++ tail)) fragment0197204Acc00200 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0197204Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197204_object_field_002"
  err.flush

noncomputable def fragment0197204Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0197204Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0197204Acc00400 : List (String × SourceJson) := (fragment0197204Field003Key00, fragment0197204Field003Value00) :: fragment0197204Acc00300
noncomputable def fragment0197204Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0197204_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0197204Field003Chars00 ++ tail)) fragment0197204Acc00300 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0197204Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197204_object_field_003"
  err.flush

noncomputable def fragment0197204Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0197204Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '9', '8', '4', '4', '0', '3', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '2', '8', '1', '0', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '8', '1', '1', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0197204Acc00500 : List (String × SourceJson) := (fragment0197204Field004Key00, fragment0197204Field004Value00) :: fragment0197204Acc00400
noncomputable def fragment0197204Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '8', '4', '4', '0', '3', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '8', '1', '0', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '8', '1', '1', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0197204_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0197204Field004Chars00 ++ tail)) fragment0197204Acc00400 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0197204Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197204_object_field_004"
  err.flush

noncomputable def fragment0197204Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0197204Field005Value00 : SourceJson := .arr [.str (String.ofList ['9', '2', '4', '7', '6', '6', '2', '2', '2', '2', '3', '4', '3', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '5', '9', '7', '5', '0', '8', '2', '3', '6', '2', '2', '1', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '5', '4', '7', '6', '5', '5', '3', '6', '1', '6', '9', '/', '1', '4', '1', '2', '2', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '9', '0', '0', '2', '7', '7', '4', '4', '4', '3', '9', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '6', '8', '8', '7', '1', '9', '2', '5', '3', '0', '5', '1', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '6', '8', '8', '6', '7', '4', '6', '5', '5', '7', '/', '1', '4', '1', '2', '2', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '1', '1', '5', '5', '8', '6', '8', '5', '2', '2', '9', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '9', '1', '1', '2', '0', '2', '9', '7', '8', '5', '7', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '4', '6', '2', '3', '2', '9', '4', '7', '2', '4', '7', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '4', '6', '2', '1', '8', '8', '2', '4', '3', '2', '7', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0197204Acc00600 : List (String × SourceJson) := (fragment0197204Field005Key00, fragment0197204Field005Value00) :: fragment0197204Acc00500
noncomputable def fragment0197204Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '4', '7', '6', '6', '2', '2', '2', '2', '3', '4', '3', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '5', '9', '7', '5', '0', '8', '2', '3', '6', '2', '2', '1', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '4', '7', '6', '5', '5', '3', '6', '1', '6', '9', '/', '1', '4', '1', '2', '2', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '9', '0', '0', '2', '7', '7', '4', '4', '4', '3', '9', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '8', '8', '7', '1', '9', '2', '5', '3', '0', '5', '1', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '6', '8', '8', '6', '7', '4', '6', '5', '5', '7', '/', '1', '4', '1', '2', '2', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '1', '1', '5', '5', '8', '6', '8', '5', '2', '2', '9', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '9', '1', '1', '2', '0', '2', '9', '7', '8', '5', '7', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '4', '6', '2', '3', '2', '9', '4', '7', '2', '4', '7', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '4', '6', '2', '1', '8', '8', '2', '4', '3', '2', '7', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0197204_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0197204Field005Chars00 ++ tail)) fragment0197204Acc00500 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0197204Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197204_object_field_005"
  err.flush

noncomputable def fragment0197204Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0197204Field006Value00 : SourceJson := .str (String.ofList ['1', '0', '3', '9', '2', '3', '9', '2', '6', '1', '0', '9', '8', '4', '0', '6', '8', '3', '2', '6', '2', '7', '0', '7', '4', '4', '9', '3', '1', '5', '8', '4', '2', '0', '1', '7', '2', '5', '5', '0', '1', '4', '4', '0', '0', '0', '0', '0', '/', '3', '1', '1', '9', '5', '7', '5', '4', '9', '7', '7', '5', '4', '3', '3', '7', '1', '3', '7', '0', '6', '0', '1', '5', '6', '7', '0', '7', '2', '7', '8', '2', '9', '7', '4', '3', '6', '8', '6', '0', '2', '3', '8', '9', '4', '9', '6', '6', '0', '4', '0', '1', '2', '5', '7', '8', '6', '1', '0', '0', '6', '4', '5', '4', '3'])
noncomputable def fragment0197204Acc00700 : List (String × SourceJson) := (fragment0197204Field006Key00, fragment0197204Field006Value00) :: fragment0197204Acc00600
noncomputable def fragment0197204Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '3', '9', '2', '3', '9', '2', '6', '1', '0', '9', '8', '4', '0', '6', '8', '3', '2', '6', '2', '7', '0', '7', '4', '4', '9', '3', '1', '5', '8', '4', '2', '0', '1', '7', '2', '5', '5', '0', '1', '4', '4', '0', '0', '0', '0', '0', '/', '3', '1', '1', '9', '5', '7', '5', '4', '9', '7', '7', '5', '4', '3', '3', '7', '1', '3', '7', '0', '6', '0', '1', '5', '6', '7', '0', '7', '2', '7', '8', '2', '9', '7', '4', '3', '6', '8', '6', '0', '2', '3', '8', '9', '4', '9', '6', '6', '0', '4', '0', '1', '2', '5', '7', '8', '6', '1', '0', '0', '6', '4', '5', '4', '3', '"', ',']

theorem object_fragment0197204_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0197204Field006Chars00 ++ tail)) fragment0197204Acc00600 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0197204Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197204_object_field_006"
  err.flush

noncomputable def fragment0197204Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0197204Field007Value00 : SourceJson := .str (String.ofList ['3', '0', '9', '4', '2', '6', '1', '8', '8', '1', '4', '7', '9', '3', '8', '3', '7', '3', '9', '3', '0', '4', '7', '1', '3', '5', '3', '6', '3', '7', '8', '0', '7', '3', '9', '7', '0', '1', '8', '6', '9', '2', '6', '1', '7', '4', '9', '3', '7', '5', '2', '6', '3', '1', '4', '4', '7', '5', '6', '3', '9', '2', '4', '8', '2', '7', '6', '7', '4', '8', '6', '4', '4', '7', '1', '2', '2', '2', '9', '0', '5', '8', '2', '7', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '0', '0', '5', '2', '5', '4', '7', '2', '1', '7', '5', '5', '4', '5', '1', '5', '7', '3', '9', '0', '3', '5', '7', '9', '6', '1', '1', '2', '9', '9', '6', '7', '9', '8', '8', '8', '2', '0', '5', '1', '5', '3', '2', '4', '1', '3', '3', '0', '3', '0', '1', '1', '9', '5', '2', '1', '8', '0', '8', '8', '4', '1', '5', '9', '3', '2', '4', '0', '3', '5', '3', '9', '3', '4', '0', '8', '6', '1', '2', '5', '4', '9', '7', '6', '9', '7', '9', '5', '7', '0', '9', '1', '9', '5', '7', '5', '2', '8', '3', '2', '3', '4', '6', '0', '5', '0', '8', '0', '9', '8', '2', '6', '1', '6', '6', '3', '0', '7', '0', '1', '2', '3', '4', '7', '2', '7'])
noncomputable def fragment0197204Acc00800 : List (String × SourceJson) := (fragment0197204Field007Key00, fragment0197204Field007Value00) :: fragment0197204Acc00700
noncomputable def fragment0197204Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '9', '4', '2', '6', '1', '8', '8', '1', '4', '7', '9', '3', '8', '3', '7', '3', '9', '3', '0', '4', '7', '1', '3', '5', '3', '6', '3', '7', '8', '0', '7', '3', '9', '7', '0', '1', '8', '6', '9', '2', '6', '1', '7', '4', '9', '3', '7', '5', '2', '6', '3', '1', '4', '4', '7', '5', '6', '3', '9', '2', '4', '8', '2', '7', '6', '7', '4', '8', '6', '4', '4', '7', '1', '2', '2', '2', '9', '0', '5', '8', '2', '7', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '0', '0', '5', '2', '5', '4', '7', '2', '1', '7', '5', '5', '4', '5', '1', '5', '7', '3', '9', '0', '3', '5', '7', '9', '6', '1', '1', '2', '9', '9', '6', '7', '9', '8', '8', '8', '2', '0', '5', '1', '5', '3', '2', '4', '1', '3', '3', '0', '3', '0', '1', '1', '9', '5', '2', '1', '8', '0', '8', '8', '4', '1', '5', '9', '3', '2', '4', '0', '3', '5', '3', '9', '3', '4', '0', '8', '6', '1', '2', '5', '4', '9', '7', '6', '9', '7', '9', '5', '7', '0', '9', '1', '9', '5', '7', '5', '2', '8', '3', '2', '3', '4', '6', '0', '5', '0', '8', '0', '9', '8', '2', '6', '1', '6', '6', '3', '0', '7', '0', '1', '2', '3', '4', '7', '2', '7', '"', ',']

theorem object_fragment0197204_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0197204Field007Chars00 ++ tail)) fragment0197204Acc00700 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0197204Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197204_object_field_007"
  err.flush

noncomputable def fragment0197204Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0197204Field008Value00 : SourceJson := .str (String.ofList ['2', '6', '3', '9', '3', '6', '6', '0', '6', '5', '3', '1'])
noncomputable def fragment0197204Acc00900 : List (String × SourceJson) := (fragment0197204Field008Key00, fragment0197204Field008Value00) :: fragment0197204Acc00800
noncomputable def fragment0197204Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '6', '3', '9', '3', '6', '6', '0', '6', '5', '3', '1', '"', ',']

theorem object_fragment0197204_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0197204Field008Chars00 ++ tail)) fragment0197204Acc00800 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0197204Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197204_object_field_008"
  err.flush

noncomputable def fragment0197204Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0197204Field009Value00 : SourceJson := .str (String.ofList ['7', '9', '0', '6', '8', '1', '0', '8', '1', '0', '2', '1'])
noncomputable def fragment0197204Acc01000 : List (String × SourceJson) := (fragment0197204Field009Key00, fragment0197204Field009Value00) :: fragment0197204Acc00900
noncomputable def fragment0197204Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '9', '0', '6', '8', '1', '0', '8', '1', '0', '2', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0197204_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0197204Field009Chars00 ++ tail)) fragment0197204Acc00900 =
      .ok (.obj (fragment0197204Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197204_object_field_009"
  err.flush

noncomputable def fragment0197204Chars : List Char := '{' :: (fragment0197204Field000Chars00 ++ fragment0197204Field001Chars00 ++ fragment0197204Field002Chars00 ++ fragment0197204Field003Chars00 ++ fragment0197204Field004Chars00 ++ fragment0197204Field005Chars00 ++ fragment0197204Field006Chars00 ++ fragment0197204Field007Chars00 ++ fragment0197204Field008Chars00 ++ fragment0197204Field009Chars00)
noncomputable def fragment0197204Value : SourceJson := .obj (fragment0197204Acc01000.reverse)

theorem value_fragment0197204 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 251) (fragment0197204Chars ++ tail) =
      .ok (fragment0197204Value, tail) := by
  have hinput : fragment0197204Chars ++ tail = '{' :: (fragment0197204Field000Chars00 ++ (fragment0197204Field001Chars00 ++ (fragment0197204Field002Chars00 ++ (fragment0197204Field003Chars00 ++ (fragment0197204Field004Chars00 ++ (fragment0197204Field005Chars00 ++ (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0197204Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 251) (fragment0197204Chars ++ tail) =
        SourceJson.value (fuel + 251) ('{' :: (fragment0197204Field000Chars00 ++ (fragment0197204Field001Chars00 ++ (fragment0197204Field002Chars00 ++ (fragment0197204Field003Chars00 ++ (fragment0197204Field004Chars00 ++ (fragment0197204Field005Chars00 ++ (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 251)) hinput
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0197204Field000Chars00 ++ (fragment0197204Field001Chars00 ++ (fragment0197204Field002Chars00 ++ (fragment0197204Field003Chars00 ++ (fragment0197204Field004Chars00 ++ (fragment0197204Field005Chars00 ++ (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail)))))))))))) fragment0197204Acc00000 := by rfl
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0197204Field001Chars00 ++ (fragment0197204Field002Chars00 ++ (fragment0197204Field003Chars00 ++ (fragment0197204Field004Chars00 ++ (fragment0197204Field005Chars00 ++ (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail))))))))))) fragment0197204Acc00100 := object_fragment0197204_field_000 fuel (fragment0197204Field001Chars00 ++ (fragment0197204Field002Chars00 ++ (fragment0197204Field003Chars00 ++ (fragment0197204Field004Chars00 ++ (fragment0197204Field005Chars00 ++ (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0197204Field002Chars00 ++ (fragment0197204Field003Chars00 ++ (fragment0197204Field004Chars00 ++ (fragment0197204Field005Chars00 ++ (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail)))))))))) fragment0197204Acc00200 := object_fragment0197204_field_001 fuel (fragment0197204Field002Chars00 ++ (fragment0197204Field003Chars00 ++ (fragment0197204Field004Chars00 ++ (fragment0197204Field005Chars00 ++ (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0197204Field003Chars00 ++ (fragment0197204Field004Chars00 ++ (fragment0197204Field005Chars00 ++ (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail))))))))) fragment0197204Acc00300 := object_fragment0197204_field_002 fuel (fragment0197204Field003Chars00 ++ (fragment0197204Field004Chars00 ++ (fragment0197204Field005Chars00 ++ (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0197204Field004Chars00 ++ (fragment0197204Field005Chars00 ++ (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail)))))))) fragment0197204Acc00400 := object_fragment0197204_field_003 fuel (fragment0197204Field004Chars00 ++ (fragment0197204Field005Chars00 ++ (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0197204Field005Chars00 ++ (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail))))))) fragment0197204Acc00500 := object_fragment0197204_field_004 fuel (fragment0197204Field005Chars00 ++ (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail)))))) fragment0197204Acc00600 := object_fragment0197204_field_005 fuel (fragment0197204Field006Chars00 ++ (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail))))) fragment0197204Acc00700 := object_fragment0197204_field_006 fuel (fragment0197204Field007Chars00 ++ (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail)))) fragment0197204Acc00800 := object_fragment0197204_field_007 fuel (fragment0197204Field008Chars00 ++ (fragment0197204Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0197204Field009Chars00 ++ (tail))) fragment0197204Acc00900 := object_fragment0197204_field_008 fuel (fragment0197204Field009Chars00 ++ (tail))
    _ = .ok (fragment0197204Value, tail) := object_fragment0197204_field_009 fuel (tail)

noncomputable def fragment0198830Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0198830Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0198830Field000Value00 : SourceJson := .number (String.ofList ['5', '5'])
noncomputable def fragment0198830Acc00100 : List (String × SourceJson) := (fragment0198830Field000Key00, fragment0198830Field000Value00) :: fragment0198830Acc00000
noncomputable def fragment0198830Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '5', ',']

theorem object_fragment0198830_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 364) (SourceJson.white (fragment0198830Field000Chars00 ++ tail)) fragment0198830Acc00000 =
      SourceJson.object (fuel + 363) (SourceJson.white tail) fragment0198830Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198830_object_field_000"
  err.flush

noncomputable def fragment0198830Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0198830Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['5'])]
noncomputable def fragment0198830Acc00200 : List (String × SourceJson) := (fragment0198830Field001Key00, fragment0198830Field001Value00) :: fragment0198830Acc00100
noncomputable def fragment0198830Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0198830_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 363) (SourceJson.white (fragment0198830Field001Chars00 ++ tail)) fragment0198830Acc00100 =
      SourceJson.object (fuel + 362) (SourceJson.white tail) fragment0198830Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198830_object_field_001"
  err.flush

noncomputable def fragment0198830Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0198830Field002Value00 : SourceJson := .str (String.ofList ['2', '8', '6', '8', '6', '8', '9', '3', '7', '2', '4', '2', '2', '5', '8', '8', '7', '5', '2', '6', '7', '9', '3', '6', '2', '9', '2', '4', '3', '5', '7', '8', '4', '7', '/', '8', '6', '0', '4', '1', '8', '7', '2', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0198830Acc00300 : List (String × SourceJson) := (fragment0198830Field002Key00, fragment0198830Field002Value00) :: fragment0198830Acc00200
noncomputable def fragment0198830Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '8', '6', '8', '6', '8', '9', '3', '7', '2', '4', '2', '2', '5', '8', '8', '7', '5', '2', '6', '7', '9', '3', '6', '2', '9', '2', '4', '3', '5', '7', '8', '4', '7', '/', '8', '6', '0', '4', '1', '8', '7', '2', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0198830_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 362) (SourceJson.white (fragment0198830Field002Chars00 ++ tail)) fragment0198830Acc00200 =
      SourceJson.object (fuel + 361) (SourceJson.white tail) fragment0198830Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198830_object_field_002"
  err.flush

noncomputable def fragment0198830Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0198830Field003Value00 : SourceJson := .str (String.ofList ['7', '9', '0', '5', '2', '7', '7', '/', '1', '5', '9', '1', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0198830Acc00400 : List (String × SourceJson) := (fragment0198830Field003Key00, fragment0198830Field003Value00) :: fragment0198830Acc00300
noncomputable def fragment0198830Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '7', '9', '0', '5', '2', '7', '7', '/', '1', '5', '9', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0198830_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 361) (SourceJson.white (fragment0198830Field003Chars00 ++ tail)) fragment0198830Acc00300 =
      SourceJson.object (fuel + 360) (SourceJson.white tail) fragment0198830Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198830_object_field_003"
  err.flush

noncomputable def fragment0198830Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0198830Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '9', '8', '4', '4', '0', '3', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '2', '8', '1', '0', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '4', '6', '8', '7', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '8', '1', '1', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0198830Acc00500 : List (String × SourceJson) := (fragment0198830Field004Key00, fragment0198830Field004Value00) :: fragment0198830Acc00400
noncomputable def fragment0198830Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '8', '4', '4', '0', '3', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '8', '1', '0', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '4', '6', '8', '7', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '8', '1', '1', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0198830_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 360) (SourceJson.white (fragment0198830Field004Chars00 ++ tail)) fragment0198830Acc00400 =
      SourceJson.object (fuel + 359) (SourceJson.white tail) fragment0198830Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198830_object_field_004"
  err.flush

noncomputable def fragment0198830Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0198830Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '6', '8', '0', '6', '9', '6', '4', '9', '2', '6', '3', '2', '9', '5', '4', '7', '8', '6', '2', '3', '/', '3', '1', '1', '0', '1', '2', '7', '2', '7', '9', '5', '0', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '8', '8', '4', '5', '7', '4', '9', '6', '5', '5', '1', '3', '8', '3', '0', '1', '/', '1', '4', '9', '5', '2', '5', '3', '4', '9', '9', '7', '6', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '5', '5', '3', '4', '6', '3', '6', '2', '0', '1', '8', '6', '4', '3', '1', '/', '1', '7', '2', '7', '8', '4', '8', '4', '8', '8', '6', '1', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '1', '4', '2', '7', '1', '0', '2', '8', '3', '6', '5', '6', '1', '8', '7', '1', '6', '2', '7', '/', '1', '5', '5', '5', '0', '6', '3', '6', '3', '9', '7', '5', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '4', '7', '4', '8', '6', '2', '3', '6', '8', '8', '7', '6', '9', '6', '0', '4', '1', '0', '3', '/', '1', '5', '5', '5', '0', '6', '3', '6', '3', '9', '7', '5', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '5', '2', '2', '5', '0', '8', '1', '9', '0', '3', '7', '9', '4', '6', '8', '9', '7', '/', '3', '4', '5', '5', '6', '9', '6', '9', '7', '7', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '1', '8', '1', '4', '6', '8', '5', '4', '4', '6', '5', '5', '6', '9', '9', '2', '0', '1', '/', '7', '7', '7', '5', '3', '1', '8', '1', '9', '8', '7', '5', '8', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '1', '0', '0', '5', '0', '7', '3', '0', '4', '3', '7', '2', '4', '7', '8', '1', '0', '3', '/', '1', '5', '5', '5', '0', '6', '3', '6', '3', '9', '7', '5', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '8', '3', '2', '1', '8', '5', '9', '4', '3', '3', '1', '0', '1', '3', '3', '/', '3', '7', '3', '8', '1', '3', '3', '7', '4', '9', '4', '0', '3', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['8', '8', '6', '6', '5', '5', '4', '9', '3', '8', '7', '5', '1', '4', '8', '0', '4', '9', '/', '2', '9', '9', '0', '5', '0', '6', '9', '9', '9', '5', '2', '2', '5', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0198830Acc00600 : List (String × SourceJson) := (fragment0198830Field005Key00, fragment0198830Field005Value00) :: fragment0198830Acc00500
noncomputable def fragment0198830Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '8', '0', '6', '9', '6', '4', '9', '2', '6', '3', '2', '9', '5', '4', '7', '8', '6', '2', '3', '/', '3', '1', '1', '0', '1', '2', '7', '2', '7', '9', '5', '0', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '8', '8', '4', '5', '7', '4', '9', '6', '5', '5', '1', '3', '8', '3', '0', '1', '/', '1', '4', '9', '5', '2', '5', '3', '4', '9', '9', '7', '6', '1', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '5', '5', '3', '4', '6', '3', '6', '2', '0', '1', '8', '6', '4', '3', '1', '/', '1', '7', '2', '7', '8', '4', '8', '4', '8', '8', '6', '1', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '4', '2', '7', '1', '0', '2', '8', '3', '6', '5', '6', '1', '8', '7', '1', '6', '2', '7', '/', '1', '5', '5', '5', '0', '6', '3', '6', '3', '9', '7', '5', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '7', '4', '8', '6', '2', '3', '6', '8', '8', '7', '6', '9', '6', '0', '4', '1', '0', '3', '/', '1', '5', '5', '5', '0', '6', '3', '6', '3', '9', '7', '5', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '5', '2', '2', '5', '0', '8', '1', '9', '0', '3', '7', '9', '4', '6', '8', '9', '7', '/', '3', '4', '5', '5', '6', '9', '6', '9', '7', '7', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '1', '8', '1', '4', '6', '8', '5', '4', '4', '6', '5', '5', '6', '9', '9', '2', '0', '1', '/', '7', '7', '7', '5', '3', '1', '8', '1', '9', '8', '7', '5', '8', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '1', '0', '0', '5', '0', '7', '3', '0', '4', '3', '7', '2', '4', '7', '8', '1', '0', '3', '/', '1', '5', '5', '5', '0', '6', '3', '6', '3', '9', '7', '5', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '8', '3', '2', '1', '8', '5', '9', '4', '3', '3', '1', '0', '1', '3', '3', '/', '3', '7', '3', '8', '1', '3', '3', '7', '4', '9', '4', '0', '3', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '6', '6', '5', '5', '4', '9', '3', '8', '7', '5', '1', '4', '8', '0', '4', '9', '/', '2', '9', '9', '0', '5', '0', '6', '9', '9', '9', '5', '2', '2', '5', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0198830_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 359) (SourceJson.white (fragment0198830Field005Chars00 ++ tail)) fragment0198830Acc00500 =
      SourceJson.object (fuel + 358) (SourceJson.white tail) fragment0198830Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198830_object_field_005"
  err.flush

noncomputable def fragment0198830Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0198830Field006Value00 : SourceJson := .str (String.ofList ['1', '2', '0', '9', '5', '4', '0', '8', '0', '2', '9', '9', '3', '6', '5', '0', '4', '6', '4', '0', '6', '3', '8', '0', '9', '2', '1', '0', '0', '1', '5', '1', '0', '9', '7', '9', '0', '7', '6', '2', '5', '5', '7', '4', '4', '0', '0', '0', '0', '0', '/', '2', '5', '9', '1', '1', '6', '2', '2', '6', '9', '5', '9', '6', '1', '0', '6', '0', '6', '3', '0', '3', '8', '9', '2', '5', '1', '9', '6', '1', '2', '7', '4', '1', '4', '6', '4', '7', '9', '1', '5', '0', '6', '4', '8', '0', '4', '1', '9', '6', '8', '5', '4', '1', '2', '2', '1', '1', '4', '8', '7', '5', '5', '7', '0', '6', '1', '1'])
noncomputable def fragment0198830Acc00700 : List (String × SourceJson) := (fragment0198830Field006Key00, fragment0198830Field006Value00) :: fragment0198830Acc00600
noncomputable def fragment0198830Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '0', '9', '5', '4', '0', '8', '0', '2', '9', '9', '3', '6', '5', '0', '4', '6', '4', '0', '6', '3', '8', '0', '9', '2', '1', '0', '0', '1', '5', '1', '0', '9', '7', '9', '0', '7', '6', '2', '5', '5', '7', '4', '4', '0', '0', '0', '0', '0', '/', '2', '5', '9', '1', '1', '6', '2', '2', '6', '9', '5', '9', '6', '1', '0', '6', '0', '6', '3', '0', '3', '8', '9', '2', '5', '1', '9', '6', '1', '2', '7', '4', '1', '4', '6', '4', '7', '9', '1', '5', '0', '6', '4', '8', '0', '4', '1', '9', '6', '8', '5', '4', '1', '2', '2', '1', '1', '4', '8', '7', '5', '5', '7', '0', '6', '1', '1', '"', ',']

theorem object_fragment0198830_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 358) (SourceJson.white (fragment0198830Field006Chars00 ++ tail)) fragment0198830Acc00600 =
      SourceJson.object (fuel + 357) (SourceJson.white tail) fragment0198830Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198830_object_field_006"
  err.flush

noncomputable def fragment0198830Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0198830Field007Value00 : SourceJson := .str (String.ofList ['1', '3', '6', '2', '2', '2', '8', '4', '6', '0', '4', '7', '6', '4', '0', '7', '9', '5', '0', '9', '9', '4', '1', '8', '5', '4', '1', '3', '1', '2', '8', '2', '0', '9', '9', '7', '5', '8', '5', '1', '7', '7', '2', '8', '7', '3', '4', '7', '4', '3', '9', '8', '2', '6', '3', '5', '8', '6', '1', '7', '1', '3', '7', '2', '9', '2', '7', '6', '5', '4', '0', '3', '9', '9', '5', '3', '1', '6', '2', '2', '4', '8', '3', '6', '5', '8', '2', '2', '7', '6', '8', '5', '3', '3', '5', '5', '6', '4', '1', '0', '6', '8', '6', '4', '7', '7', '5', '3', '1', '7', '8', '2', '2', '1', '9', '4', '0', '4', '9', '9', '0', '1', '8', '6', '4', '2', '7', '8', '5', '2', '7', '9', '5', '2', '1', '5', '7', '8', '3', '9', '7', '9', '8', '7', '4', '9', '9', '6', '1', '4', '2', '5', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '7', '6', '3', '5', '6', '2', '2', '0', '3', '3', '2', '3', '5', '7', '0', '7', '7', '5', '6', '8', '6', '9', '5', '2', '6', '3', '7', '9', '8', '7', '8', '2', '0', '9', '8', '8', '2', '7', '5', '8', '1', '8', '0', '2', '9', '7', '1', '4', '9', '4', '7', '3', '8', '7', '8', '2', '3', '4', '8', '5', '8', '1', '6', '5', '7', '7', '2', '6', '2', '8', '8', '0', '3', '2', '7', '9', '0', '8', '8', '7', '1', '6', '0', '1', '3', '9', '6', '3', '5', '5', '1', '3', '5', '4', '7', '7', '8', '1', '1', '6', '6', '9', '1', '6', '3', '4', '0', '2', '1', '2', '6', '9', '9', '0', '7', '8', '0', '8', '6', '1', '3', '9', '7', '2', '5', '2', '0', '9', '5', '4', '1', '9', '9', '0', '3', '6', '0', '0', '0', '4', '1', '2', '5', '6', '1', '4', '9', '2', '0', '7', '0', '4', '1', '8', '6', '5', '4', '2', '9', '1', '0', '5', '9', '8', '0', '9', '2', '0', '3', '6', '7', '6', '2', '6', '0', '4', '1', '2', '9', '5', '8', '5', '1'])
noncomputable def fragment0198830Acc00800 : List (String × SourceJson) := (fragment0198830Field007Key00, fragment0198830Field007Value00) :: fragment0198830Acc00700
noncomputable def fragment0198830Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '6', '2', '2', '2', '8', '4', '6', '0', '4', '7', '6', '4', '0', '7', '9', '5', '0', '9', '9', '4', '1', '8', '5', '4', '1', '3', '1', '2', '8', '2', '0', '9', '9', '7', '5', '8', '5', '1', '7', '7', '2', '8', '7', '3', '4', '7', '4', '3', '9', '8', '2', '6', '3', '5', '8', '6', '1', '7', '1', '3', '7', '2', '9', '2', '7', '6', '5', '4', '0', '3', '9', '9', '5', '3', '1', '6', '2', '2', '4', '8', '3', '6', '5', '8', '2', '2', '7', '6', '8', '5', '3', '3', '5', '5', '6', '4', '1', '0', '6', '8', '6', '4', '7', '7', '5', '3', '1', '7', '8', '2', '2', '1', '9', '4', '0', '4', '9', '9', '0', '1', '8', '6', '4', '2', '7', '8', '5', '2', '7', '9', '5', '2', '1', '5', '7', '8', '3', '9', '7', '9', '8', '7', '4', '9', '9', '6', '1', '4', '2', '5', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '7', '6', '3', '5', '6', '2', '2', '0', '3', '3', '2', '3', '5', '7', '0', '7', '7', '5', '6', '8', '6', '9', '5', '2', '6', '3', '7', '9', '8', '7', '8', '2', '0', '9', '8', '8', '2', '7', '5', '8', '1', '8', '0', '2', '9', '7', '1', '4', '9', '4', '7', '3', '8', '7', '8', '2', '3', '4', '8', '5', '8', '1', '6', '5', '7', '7', '2', '6', '2', '8', '8', '0', '3', '2', '7', '9', '0', '8', '8', '7', '1', '6', '0', '1', '3', '9', '6', '3', '5', '5', '1', '3', '5', '4', '7', '7', '8', '1', '1', '6', '6', '9', '1', '6', '3', '4', '0', '2', '1', '2', '6', '9', '9', '0', '7', '8', '0', '8', '6', '1', '3', '9', '7', '2', '5', '2', '0', '9', '5', '4', '1', '9', '9', '0', '3', '6', '0', '0', '0', '4', '1', '2', '5', '6', '1', '4', '9', '2', '0', '7', '0', '4', '1', '8', '6', '5', '4', '2', '9', '1', '0', '5', '9', '8', '0', '9', '2', '0', '3', '6', '7', '6', '2', '6', '0', '4', '1', '2', '9', '5', '8', '5', '1', '"', ',']

theorem object_fragment0198830_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 357) (SourceJson.white (fragment0198830Field007Chars00 ++ tail)) fragment0198830Acc00700 =
      SourceJson.object (fuel + 356) (SourceJson.white tail) fragment0198830Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198830_object_field_007"
  err.flush

noncomputable def fragment0198830Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0198830Field008Value00 : SourceJson := .str (String.ofList ['3', '6', '9', '8', '3', '2', '8', '6', '0', '0', '7', '0'])
noncomputable def fragment0198830Acc00900 : List (String × SourceJson) := (fragment0198830Field008Key00, fragment0198830Field008Value00) :: fragment0198830Acc00800
noncomputable def fragment0198830Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '6', '9', '8', '3', '2', '8', '6', '0', '0', '7', '0', '"', ',']

theorem object_fragment0198830_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 356) (SourceJson.white (fragment0198830Field008Chars00 ++ tail)) fragment0198830Acc00800 =
      SourceJson.object (fuel + 355) (SourceJson.white tail) fragment0198830Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198830_object_field_008"
  err.flush

noncomputable def fragment0198830Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0198830Field009Value00 : SourceJson := .str (String.ofList ['9', '1', '7', '4', '6', '7', '4', '8', '1', '2', '1', '6'])
noncomputable def fragment0198830Acc01000 : List (String × SourceJson) := (fragment0198830Field009Key00, fragment0198830Field009Value00) :: fragment0198830Acc00900
noncomputable def fragment0198830Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '1', '7', '4', '6', '7', '4', '8', '1', '2', '1', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0198830_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 355) (SourceJson.white (fragment0198830Field009Chars00 ++ tail)) fragment0198830Acc00900 =
      .ok (.obj (fragment0198830Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198830_object_field_009"
  err.flush

noncomputable def fragment0198830Chars : List Char := '{' :: (fragment0198830Field000Chars00 ++ fragment0198830Field001Chars00 ++ fragment0198830Field002Chars00 ++ fragment0198830Field003Chars00 ++ fragment0198830Field004Chars00 ++ fragment0198830Field005Chars00 ++ fragment0198830Field006Chars00 ++ fragment0198830Field007Chars00 ++ fragment0198830Field008Chars00 ++ fragment0198830Field009Chars00)
noncomputable def fragment0198830Value : SourceJson := .obj (fragment0198830Acc01000.reverse)

theorem value_fragment0198830 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 365) (fragment0198830Chars ++ tail) =
      .ok (fragment0198830Value, tail) := by
  have hinput : fragment0198830Chars ++ tail = '{' :: (fragment0198830Field000Chars00 ++ (fragment0198830Field001Chars00 ++ (fragment0198830Field002Chars00 ++ (fragment0198830Field003Chars00 ++ (fragment0198830Field004Chars00 ++ (fragment0198830Field005Chars00 ++ (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0198830Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 365) (fragment0198830Chars ++ tail) =
        SourceJson.value (fuel + 365) ('{' :: (fragment0198830Field000Chars00 ++ (fragment0198830Field001Chars00 ++ (fragment0198830Field002Chars00 ++ (fragment0198830Field003Chars00 ++ (fragment0198830Field004Chars00 ++ (fragment0198830Field005Chars00 ++ (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 365)) hinput
    _ = SourceJson.object (fuel + 364) (SourceJson.white (fragment0198830Field000Chars00 ++ (fragment0198830Field001Chars00 ++ (fragment0198830Field002Chars00 ++ (fragment0198830Field003Chars00 ++ (fragment0198830Field004Chars00 ++ (fragment0198830Field005Chars00 ++ (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail)))))))))))) fragment0198830Acc00000 := by rfl
    _ = SourceJson.object (fuel + 363) (SourceJson.white (fragment0198830Field001Chars00 ++ (fragment0198830Field002Chars00 ++ (fragment0198830Field003Chars00 ++ (fragment0198830Field004Chars00 ++ (fragment0198830Field005Chars00 ++ (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail))))))))))) fragment0198830Acc00100 := object_fragment0198830_field_000 fuel (fragment0198830Field001Chars00 ++ (fragment0198830Field002Chars00 ++ (fragment0198830Field003Chars00 ++ (fragment0198830Field004Chars00 ++ (fragment0198830Field005Chars00 ++ (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 362) (SourceJson.white (fragment0198830Field002Chars00 ++ (fragment0198830Field003Chars00 ++ (fragment0198830Field004Chars00 ++ (fragment0198830Field005Chars00 ++ (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail)))))))))) fragment0198830Acc00200 := object_fragment0198830_field_001 fuel (fragment0198830Field002Chars00 ++ (fragment0198830Field003Chars00 ++ (fragment0198830Field004Chars00 ++ (fragment0198830Field005Chars00 ++ (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 361) (SourceJson.white (fragment0198830Field003Chars00 ++ (fragment0198830Field004Chars00 ++ (fragment0198830Field005Chars00 ++ (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail))))))))) fragment0198830Acc00300 := object_fragment0198830_field_002 fuel (fragment0198830Field003Chars00 ++ (fragment0198830Field004Chars00 ++ (fragment0198830Field005Chars00 ++ (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 360) (SourceJson.white (fragment0198830Field004Chars00 ++ (fragment0198830Field005Chars00 ++ (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail)))))))) fragment0198830Acc00400 := object_fragment0198830_field_003 fuel (fragment0198830Field004Chars00 ++ (fragment0198830Field005Chars00 ++ (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 359) (SourceJson.white (fragment0198830Field005Chars00 ++ (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail))))))) fragment0198830Acc00500 := object_fragment0198830_field_004 fuel (fragment0198830Field005Chars00 ++ (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 358) (SourceJson.white (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail)))))) fragment0198830Acc00600 := object_fragment0198830_field_005 fuel (fragment0198830Field006Chars00 ++ (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 357) (SourceJson.white (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail))))) fragment0198830Acc00700 := object_fragment0198830_field_006 fuel (fragment0198830Field007Chars00 ++ (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 356) (SourceJson.white (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail)))) fragment0198830Acc00800 := object_fragment0198830_field_007 fuel (fragment0198830Field008Chars00 ++ (fragment0198830Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 355) (SourceJson.white (fragment0198830Field009Chars00 ++ (tail))) fragment0198830Acc00900 := object_fragment0198830_field_008 fuel (fragment0198830Field009Chars00 ++ (tail))
    _ = .ok (fragment0198830Value, tail) := object_fragment0198830_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0048_before_reader"
  err.flush

noncomputable def chunk0048LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0048SuffixChars00 : List Char := [',']
noncomputable def chunk0048Chars00 : List Char := chunk0048LeadChars00 ++ fragment0187122Chars ++ chunk0048SuffixChars00
noncomputable def chunk0048Push00 (acc : List SourceJson) : List SourceJson := fragment0187122Value :: acc

noncomputable def chunk0048AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0048_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 425)
      (SourceJson.white (chunk0048LeadChars00 ++ (fragment0187122Chars ++ rest))) acc =
      (SourceJson.value (fuel + 424) (fragment0187122Chars ++ rest)).bind
        (chunk0048AfterValue00 (fuel + 424) acc) := by rfl

theorem array_chunk0048 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 425) (SourceJson.white (chunk0048Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 424) (SourceJson.white tail) (chunk0048Push00 acc) := by
  have hinput : chunk0048Chars00 ++ tail = chunk0048LeadChars00 ++ (fragment0187122Chars ++ (chunk0048SuffixChars00 ++ tail)) := by
    simp only [chunk0048Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 425) (SourceJson.white (chunk0048Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 425)
          (SourceJson.white (chunk0048LeadChars00 ++ (fragment0187122Chars ++ (chunk0048SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 425) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 424) (fragment0187122Chars ++ (chunk0048SuffixChars00 ++ tail))).bind
        (chunk0048AfterValue00 (fuel + 424) acc) := array_chunk0048_head fuel (chunk0048SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0187122Value, chunk0048SuffixChars00 ++ tail)).bind
        (chunk0048AfterValue00 (fuel + 424) acc) :=
      congrArg (fun result => result.bind (chunk0048AfterValue00 (fuel + 424) acc))
        (value_fragment0187122 (fuel + 55) (chunk0048SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 424) (SourceJson.white tail) (chunk0048Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0048_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0049_before_reader"
  err.flush

noncomputable def chunk0049LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0049SuffixChars00 : List Char := [',']
noncomputable def chunk0049Chars00 : List Char := chunk0049LeadChars00 ++ fragment0188995Chars ++ chunk0049SuffixChars00
noncomputable def chunk0049Push00 (acc : List SourceJson) : List SourceJson := fragment0188995Value :: acc

noncomputable def chunk0049AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0049_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 424)
      (SourceJson.white (chunk0049LeadChars00 ++ (fragment0188995Chars ++ rest))) acc =
      (SourceJson.value (fuel + 423) (fragment0188995Chars ++ rest)).bind
        (chunk0049AfterValue00 (fuel + 423) acc) := by rfl

theorem array_chunk0049 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 424) (SourceJson.white (chunk0049Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 423) (SourceJson.white tail) (chunk0049Push00 acc) := by
  have hinput : chunk0049Chars00 ++ tail = chunk0049LeadChars00 ++ (fragment0188995Chars ++ (chunk0049SuffixChars00 ++ tail)) := by
    simp only [chunk0049Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 424) (SourceJson.white (chunk0049Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 424)
          (SourceJson.white (chunk0049LeadChars00 ++ (fragment0188995Chars ++ (chunk0049SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 424) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 423) (fragment0188995Chars ++ (chunk0049SuffixChars00 ++ tail))).bind
        (chunk0049AfterValue00 (fuel + 423) acc) := array_chunk0049_head fuel (chunk0049SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0188995Value, chunk0049SuffixChars00 ++ tail)).bind
        (chunk0049AfterValue00 (fuel + 423) acc) :=
      congrArg (fun result => result.bind (chunk0049AfterValue00 (fuel + 423) acc))
        (value_fragment0188995 (fuel + 166) (chunk0049SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 423) (SourceJson.white tail) (chunk0049Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0049_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0050_before_reader"
  err.flush

noncomputable def chunk0050LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0050SuffixChars00 : List Char := [',']
noncomputable def chunk0050Chars00 : List Char := chunk0050LeadChars00 ++ fragment0190642Chars ++ chunk0050SuffixChars00
noncomputable def chunk0050Push00 (acc : List SourceJson) : List SourceJson := fragment0190642Value :: acc

noncomputable def chunk0050AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0050_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 423)
      (SourceJson.white (chunk0050LeadChars00 ++ (fragment0190642Chars ++ rest))) acc =
      (SourceJson.value (fuel + 422) (fragment0190642Chars ++ rest)).bind
        (chunk0050AfterValue00 (fuel + 422) acc) := by rfl

theorem array_chunk0050 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 423) (SourceJson.white (chunk0050Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 422) (SourceJson.white tail) (chunk0050Push00 acc) := by
  have hinput : chunk0050Chars00 ++ tail = chunk0050LeadChars00 ++ (fragment0190642Chars ++ (chunk0050SuffixChars00 ++ tail)) := by
    simp only [chunk0050Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 423) (SourceJson.white (chunk0050Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 423)
          (SourceJson.white (chunk0050LeadChars00 ++ (fragment0190642Chars ++ (chunk0050SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 423) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 422) (fragment0190642Chars ++ (chunk0050SuffixChars00 ++ tail))).bind
        (chunk0050AfterValue00 (fuel + 422) acc) := array_chunk0050_head fuel (chunk0050SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0190642Value, chunk0050SuffixChars00 ++ tail)).bind
        (chunk0050AfterValue00 (fuel + 422) acc) :=
      congrArg (fun result => result.bind (chunk0050AfterValue00 (fuel + 422) acc))
        (value_fragment0190642 (fuel + 189) (chunk0050SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 422) (SourceJson.white tail) (chunk0050Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0050_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0051_before_reader"
  err.flush

noncomputable def chunk0051LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0051SuffixChars00 : List Char := [',']
noncomputable def chunk0051Chars00 : List Char := chunk0051LeadChars00 ++ fragment0192229Chars ++ chunk0051SuffixChars00
noncomputable def chunk0051Push00 (acc : List SourceJson) : List SourceJson := fragment0192229Value :: acc

noncomputable def chunk0051AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0051_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 422)
      (SourceJson.white (chunk0051LeadChars00 ++ (fragment0192229Chars ++ rest))) acc =
      (SourceJson.value (fuel + 421) (fragment0192229Chars ++ rest)).bind
        (chunk0051AfterValue00 (fuel + 421) acc) := by rfl

theorem array_chunk0051 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 422) (SourceJson.white (chunk0051Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 421) (SourceJson.white tail) (chunk0051Push00 acc) := by
  have hinput : chunk0051Chars00 ++ tail = chunk0051LeadChars00 ++ (fragment0192229Chars ++ (chunk0051SuffixChars00 ++ tail)) := by
    simp only [chunk0051Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 422) (SourceJson.white (chunk0051Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 422)
          (SourceJson.white (chunk0051LeadChars00 ++ (fragment0192229Chars ++ (chunk0051SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 422) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 421) (fragment0192229Chars ++ (chunk0051SuffixChars00 ++ tail))).bind
        (chunk0051AfterValue00 (fuel + 421) acc) := array_chunk0051_head fuel (chunk0051SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0192229Value, chunk0051SuffixChars00 ++ tail)).bind
        (chunk0051AfterValue00 (fuel + 421) acc) :=
      congrArg (fun result => result.bind (chunk0051AfterValue00 (fuel + 421) acc))
        (value_fragment0192229 (fuel + 160) (chunk0051SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 421) (SourceJson.white tail) (chunk0051Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0051_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0052_before_reader"
  err.flush

noncomputable def chunk0052LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0052SuffixChars00 : List Char := [',']
noncomputable def chunk0052Chars00 : List Char := chunk0052LeadChars00 ++ fragment0193877Chars ++ chunk0052SuffixChars00
noncomputable def chunk0052Push00 (acc : List SourceJson) : List SourceJson := fragment0193877Value :: acc

noncomputable def chunk0052AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0052_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 421)
      (SourceJson.white (chunk0052LeadChars00 ++ (fragment0193877Chars ++ rest))) acc =
      (SourceJson.value (fuel + 420) (fragment0193877Chars ++ rest)).bind
        (chunk0052AfterValue00 (fuel + 420) acc) := by rfl

theorem array_chunk0052 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 421) (SourceJson.white (chunk0052Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 420) (SourceJson.white tail) (chunk0052Push00 acc) := by
  have hinput : chunk0052Chars00 ++ tail = chunk0052LeadChars00 ++ (fragment0193877Chars ++ (chunk0052SuffixChars00 ++ tail)) := by
    simp only [chunk0052Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 421) (SourceJson.white (chunk0052Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 421)
          (SourceJson.white (chunk0052LeadChars00 ++ (fragment0193877Chars ++ (chunk0052SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 421) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 420) (fragment0193877Chars ++ (chunk0052SuffixChars00 ++ tail))).bind
        (chunk0052AfterValue00 (fuel + 420) acc) := array_chunk0052_head fuel (chunk0052SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0193877Value, chunk0052SuffixChars00 ++ tail)).bind
        (chunk0052AfterValue00 (fuel + 420) acc) :=
      congrArg (fun result => result.bind (chunk0052AfterValue00 (fuel + 420) acc))
        (value_fragment0193877 (fuel + 163) (chunk0052SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 420) (SourceJson.white tail) (chunk0052Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0052_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0053_before_reader"
  err.flush

noncomputable def chunk0053LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0053SuffixChars00 : List Char := [',']
noncomputable def chunk0053Chars00 : List Char := chunk0053LeadChars00 ++ fragment0195514Chars ++ chunk0053SuffixChars00
noncomputable def chunk0053Push00 (acc : List SourceJson) : List SourceJson := fragment0195514Value :: acc

noncomputable def chunk0053AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0053_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 420)
      (SourceJson.white (chunk0053LeadChars00 ++ (fragment0195514Chars ++ rest))) acc =
      (SourceJson.value (fuel + 419) (fragment0195514Chars ++ rest)).bind
        (chunk0053AfterValue00 (fuel + 419) acc) := by rfl

theorem array_chunk0053 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 420) (SourceJson.white (chunk0053Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 419) (SourceJson.white tail) (chunk0053Push00 acc) := by
  have hinput : chunk0053Chars00 ++ tail = chunk0053LeadChars00 ++ (fragment0195514Chars ++ (chunk0053SuffixChars00 ++ tail)) := by
    simp only [chunk0053Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 420) (SourceJson.white (chunk0053Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 420)
          (SourceJson.white (chunk0053LeadChars00 ++ (fragment0195514Chars ++ (chunk0053SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 420) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 419) (fragment0195514Chars ++ (chunk0053SuffixChars00 ++ tail))).bind
        (chunk0053AfterValue00 (fuel + 419) acc) := array_chunk0053_head fuel (chunk0053SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0195514Value, chunk0053SuffixChars00 ++ tail)).bind
        (chunk0053AfterValue00 (fuel + 419) acc) :=
      congrArg (fun result => result.bind (chunk0053AfterValue00 (fuel + 419) acc))
        (value_fragment0195514 (fuel + 136) (chunk0053SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 419) (SourceJson.white tail) (chunk0053Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0053_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0054_before_reader"
  err.flush

noncomputable def chunk0054LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0054SuffixChars00 : List Char := [',']
noncomputable def chunk0054Chars00 : List Char := chunk0054LeadChars00 ++ fragment0197204Chars ++ chunk0054SuffixChars00
noncomputable def chunk0054Push00 (acc : List SourceJson) : List SourceJson := fragment0197204Value :: acc

noncomputable def chunk0054AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0054_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 419)
      (SourceJson.white (chunk0054LeadChars00 ++ (fragment0197204Chars ++ rest))) acc =
      (SourceJson.value (fuel + 418) (fragment0197204Chars ++ rest)).bind
        (chunk0054AfterValue00 (fuel + 418) acc) := by rfl

theorem array_chunk0054 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 419) (SourceJson.white (chunk0054Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 418) (SourceJson.white tail) (chunk0054Push00 acc) := by
  have hinput : chunk0054Chars00 ++ tail = chunk0054LeadChars00 ++ (fragment0197204Chars ++ (chunk0054SuffixChars00 ++ tail)) := by
    simp only [chunk0054Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 419) (SourceJson.white (chunk0054Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 419)
          (SourceJson.white (chunk0054LeadChars00 ++ (fragment0197204Chars ++ (chunk0054SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 419) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 418) (fragment0197204Chars ++ (chunk0054SuffixChars00 ++ tail))).bind
        (chunk0054AfterValue00 (fuel + 418) acc) := array_chunk0054_head fuel (chunk0054SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0197204Value, chunk0054SuffixChars00 ++ tail)).bind
        (chunk0054AfterValue00 (fuel + 418) acc) :=
      congrArg (fun result => result.bind (chunk0054AfterValue00 (fuel + 418) acc))
        (value_fragment0197204 (fuel + 167) (chunk0054SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 418) (SourceJson.white tail) (chunk0054Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0054_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0055_before_reader"
  err.flush

noncomputable def chunk0055LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0055SuffixChars00 : List Char := ['\r', '\n', ' ', ' ', ']']
noncomputable def chunk0055Chars00 : List Char := chunk0055LeadChars00 ++ fragment0198830Chars ++ chunk0055SuffixChars00
noncomputable def chunk0055Push00 (acc : List SourceJson) : List SourceJson := fragment0198830Value :: acc

noncomputable def chunk0055AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0055_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 418)
      (SourceJson.white (chunk0055LeadChars00 ++ (fragment0198830Chars ++ rest))) acc =
      (SourceJson.value (fuel + 417) (fragment0198830Chars ++ rest)).bind
        (chunk0055AfterValue00 (fuel + 417) acc) := by rfl

theorem array_chunk0055 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 418) (SourceJson.white (chunk0055Chars00 ++ tail)) acc =
      .ok (.arr ((chunk0055Push00 acc).reverse), tail) := by
  have hinput : chunk0055Chars00 ++ tail = chunk0055LeadChars00 ++ (fragment0198830Chars ++ (chunk0055SuffixChars00 ++ tail)) := by
    simp only [chunk0055Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 418) (SourceJson.white (chunk0055Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 418)
          (SourceJson.white (chunk0055LeadChars00 ++ (fragment0198830Chars ++ (chunk0055SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 418) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 417) (fragment0198830Chars ++ (chunk0055SuffixChars00 ++ tail))).bind
        (chunk0055AfterValue00 (fuel + 417) acc) := array_chunk0055_head fuel (chunk0055SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0198830Value, chunk0055SuffixChars00 ++ tail)).bind
        (chunk0055AfterValue00 (fuel + 417) acc) :=
      congrArg (fun result => result.bind (chunk0055AfterValue00 (fuel + 417) acc))
        (value_fragment0198830 (fuel + 52) (chunk0055SuffixChars00 ++ tail))
    _ = .ok (.arr ((chunk0055Push00 acc).reverse), tail) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0055_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0048Chars00 ++ chunk0049Chars00 ++ chunk0050Chars00 ++ chunk0051Chars00 ++ chunk0052Chars00 ++ chunk0053Chars00 ++ chunk0054Chars00 ++ chunk0055Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0055Push00 (chunk0054Push00 (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 425) (SourceJson.white (blockChars ++ tail)) acc =
      .ok (.arr ((blockPush acc).reverse), tail) := by
  have hinput : blockChars ++ tail = chunk0048Chars00 ++ (chunk0049Chars00 ++ (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 425) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 425) (SourceJson.white (chunk0048Chars00 ++ (chunk0049Chars00 ++ (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 425) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 424) (SourceJson.white (chunk0049Chars00 ++ (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))))))))) (chunk0048Push00 (acc)) := array_chunk0048 fuel (chunk0049Chars00 ++ (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 423) (SourceJson.white (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))))) (chunk0049Push00 (chunk0048Push00 (acc))) := array_chunk0049 fuel (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))))))) (chunk0048Push00 (acc))
    _ = SourceJson.array (fuel + 422) (SourceJson.white (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))))))) (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc)))) := array_chunk0050 fuel (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))) (chunk0049Push00 (chunk0048Push00 (acc)))
    _ = SourceJson.array (fuel + 421) (SourceJson.white (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))) (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc))))) := array_chunk0051 fuel (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))))) (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc))))
    _ = SourceJson.array (fuel + 420) (SourceJson.white (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))))) (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc)))))) := array_chunk0052 fuel (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))) (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc)))))
    _ = SourceJson.array (fuel + 419) (SourceJson.white (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))) (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc))))))) := array_chunk0053 fuel (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))) (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc))))))
    _ = SourceJson.array (fuel + 418) (SourceJson.white (chunk0055Chars00 ++ (tail))) (chunk0054Push00 (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc)))))))) := array_chunk0054 fuel (chunk0055Chars00 ++ (tail)) (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc)))))))
    _ = .ok (.arr ((blockPush acc).reverse), tail) := array_chunk0055 fuel (tail) (chunk0054Push00 (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 187116).take 13583 = blockChars := by rfl

theorem block_original_split : sourceRest 187116 = blockChars ++ sourceRest 200699 := by
  calc
    sourceRest 187116 = (sourceRest 187116).take 13583 ++ (sourceRest 187116).drop 13583 :=
      (List.take_append_drop 13583 (sourceRest 187116)).symm
    _ = blockChars ++ (sourceRest 187116).drop 13583 :=
      congrArg (fun part => part ++ (sourceRest 187116).drop 13583) block_original_prefix
    _ = blockChars ++ sourceRest 200699 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 187116 13583)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 425) (SourceJson.white (sourceRest 187116)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 200699) :=
  (congrArg (fun chars => SourceJson.array (fuel + 425) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 200699) acc)

#print axioms object_fragment0187122_field_000
#print axioms object_fragment0187122_field_001
#print axioms object_fragment0187122_field_002
#print axioms object_fragment0187122_field_003
#print axioms object_fragment0187122_field_004
#print axioms object_fragment0187122_field_005
#print axioms object_fragment0187122_field_006
#print axioms object_fragment0187122_field_007
#print axioms object_fragment0187122_field_008
#print axioms object_fragment0187122_field_009
#print axioms value_fragment0187122
#print axioms object_fragment0188995_field_000
#print axioms object_fragment0188995_field_001
#print axioms object_fragment0188995_field_002
#print axioms object_fragment0188995_field_003
#print axioms object_fragment0188995_field_004
#print axioms object_fragment0188995_field_005
#print axioms object_fragment0188995_field_006
#print axioms object_fragment0188995_field_007
#print axioms object_fragment0188995_field_008
#print axioms object_fragment0188995_field_009
#print axioms value_fragment0188995
#print axioms object_fragment0190642_field_000
#print axioms object_fragment0190642_field_001
#print axioms object_fragment0190642_field_002
#print axioms object_fragment0190642_field_003
#print axioms object_fragment0190642_field_004
#print axioms object_fragment0190642_field_005
#print axioms object_fragment0190642_field_006
#print axioms object_fragment0190642_field_007
#print axioms object_fragment0190642_field_008
#print axioms object_fragment0190642_field_009
#print axioms value_fragment0190642
#print axioms object_fragment0192229_field_000
#print axioms object_fragment0192229_field_001
#print axioms object_fragment0192229_field_002
#print axioms object_fragment0192229_field_003
#print axioms object_fragment0192229_field_004
#print axioms object_fragment0192229_field_005
#print axioms object_fragment0192229_field_006
#print axioms object_fragment0192229_field_007
#print axioms object_fragment0192229_field_008
#print axioms object_fragment0192229_field_009
#print axioms value_fragment0192229
#print axioms object_fragment0193877_field_000
#print axioms object_fragment0193877_field_001
#print axioms object_fragment0193877_field_002
#print axioms object_fragment0193877_field_003
#print axioms object_fragment0193877_field_004
#print axioms object_fragment0193877_field_005
#print axioms object_fragment0193877_field_006
#print axioms object_fragment0193877_field_007
#print axioms object_fragment0193877_field_008
#print axioms object_fragment0193877_field_009
#print axioms value_fragment0193877
#print axioms object_fragment0195514_field_000
#print axioms object_fragment0195514_field_001
#print axioms object_fragment0195514_field_002
#print axioms object_fragment0195514_field_003
#print axioms object_fragment0195514_field_004
#print axioms object_fragment0195514_field_005
#print axioms object_fragment0195514_field_006
#print axioms object_fragment0195514_field_007
#print axioms object_fragment0195514_field_008
#print axioms object_fragment0195514_field_009
#print axioms value_fragment0195514
#print axioms object_fragment0197204_field_000
#print axioms object_fragment0197204_field_001
#print axioms object_fragment0197204_field_002
#print axioms object_fragment0197204_field_003
#print axioms object_fragment0197204_field_004
#print axioms object_fragment0197204_field_005
#print axioms object_fragment0197204_field_006
#print axioms object_fragment0197204_field_007
#print axioms object_fragment0197204_field_008
#print axioms object_fragment0197204_field_009
#print axioms value_fragment0197204
#print axioms object_fragment0198830_field_000
#print axioms object_fragment0198830_field_001
#print axioms object_fragment0198830_field_002
#print axioms object_fragment0198830_field_003
#print axioms object_fragment0198830_field_004
#print axioms object_fragment0198830_field_005
#print axioms object_fragment0198830_field_006
#print axioms object_fragment0198830_field_007
#print axioms object_fragment0198830_field_008
#print axioms object_fragment0198830_field_009
#print axioms value_fragment0198830
#print axioms array_chunk0048_head
#print axioms array_chunk0048
#print axioms array_chunk0049_head
#print axioms array_chunk0049
#print axioms array_chunk0050_head
#print axioms array_chunk0050
#print axioms array_chunk0051_head
#print axioms array_chunk0051
#print axioms array_chunk0052_head
#print axioms array_chunk0052
#print axioms array_chunk0053_head
#print axioms array_chunk0053
#print axioms array_chunk0054_head
#print axioms array_chunk0054
#print axioms array_chunk0055_head
#print axioms array_chunk0055
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock006

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
