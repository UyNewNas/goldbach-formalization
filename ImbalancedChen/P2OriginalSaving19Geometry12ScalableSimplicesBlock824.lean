import ImbalancedChen.P2OriginalSaving19Geometry12ScalableInput

/-! Original simplices grouped chunk transitions, including exact compact-input binding.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry12ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesBlock824

noncomputable def fragment14446322Acc00000 : List (String × SourceJson) := []

noncomputable def fragment14446322Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment14446322Field000Value00 : SourceJson := .number (String.ofList ['6', '5', '9', '2'])
noncomputable def fragment14446322Acc00100 : List (String × SourceJson) := (fragment14446322Field000Key00, fragment14446322Field000Value00) :: fragment14446322Acc00000
noncomputable def fragment14446322Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '5', '9', '2', ',']

theorem object_fragment14446322_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 332) (SourceJson.white (fragment14446322Field000Chars00 ++ tail)) fragment14446322Acc00000 =
      SourceJson.object (fuel + 331) (SourceJson.white tail) fragment14446322Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14446322_object_field_000"
  err.flush

noncomputable def fragment14446322Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment14446322Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '7']), .number (String.ofList ['1', '3', '5']), .number (String.ofList ['1', '1', '7']), .number (String.ofList ['1', '1', '5']), .number (String.ofList ['8', '4']), .number (String.ofList ['6', '6']), .number (String.ofList ['5', '6']), .number (String.ofList ['2', '7'])]
noncomputable def fragment14446322Acc00200 : List (String × SourceJson) := (fragment14446322Field001Key00, fragment14446322Field001Value00) :: fragment14446322Acc00100
noncomputable def fragment14446322Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14446322_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 331) (SourceJson.white (fragment14446322Field001Chars00 ++ tail)) fragment14446322Acc00100 =
      SourceJson.object (fuel + 330) (SourceJson.white tail) fragment14446322Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14446322_object_field_001"
  err.flush

noncomputable def fragment14446322Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment14446322Field002Value00 : SourceJson := .str (String.ofList ['2', '1', '6', '7', '1', '3', '8', '4', '6', '2', '8', '1', '2', '4', '8', '3', '8', '9', '9', '2', '9', '8', '1', '4', '7', '9', '0', '1', '1', '0', '9', '6', '2', '9', '0', '2', '8', '8', '4', '5', '5', '4', '9', '2', '1', '/', '9', '2', '6', '0', '3', '5', '1', '1', '5', '3', '9', '9', '3', '3', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14446322Acc00300 : List (String × SourceJson) := (fragment14446322Field002Key00, fragment14446322Field002Value00) :: fragment14446322Acc00200
noncomputable def fragment14446322Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '1', '6', '7', '1', '3', '8', '4', '6', '2', '8', '1', '2', '4', '8', '3', '8', '9', '9', '2', '9', '8', '1', '4', '7', '9', '0', '1', '1', '0', '9', '6', '2', '9', '0', '2', '8', '8', '4', '5', '5', '4', '9', '2', '1', '/', '9', '2', '6', '0', '3', '5', '1', '1', '5', '3', '9', '9', '3', '3', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14446322_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 330) (SourceJson.white (fragment14446322Field002Chars00 ++ tail)) fragment14446322Acc00200 =
      SourceJson.object (fuel + 329) (SourceJson.white tail) fragment14446322Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14446322_object_field_002"
  err.flush

noncomputable def fragment14446322Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment14446322Field003Value00 : SourceJson := .str (String.ofList ['2', '0', '1', '5', '2', '6', '9', '/', '2', '9', '8', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14446322Acc00400 : List (String × SourceJson) := (fragment14446322Field003Key00, fragment14446322Field003Value00) :: fragment14446322Acc00300
noncomputable def fragment14446322Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '0', '1', '5', '2', '6', '9', '/', '2', '9', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14446322_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 329) (SourceJson.white (fragment14446322Field003Chars00 ++ tail)) fragment14446322Acc00300 =
      SourceJson.object (fuel + 328) (SourceJson.white tail) fragment14446322Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14446322_object_field_003"
  err.flush

noncomputable def fragment14446322Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment14446322Field004Value00 : SourceJson := .arr [.str (String.ofList ['4', '4', '9', '2', '0', '1', '/', '8', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '9', '2', '0', '1', '/', '8', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '3', '5', '8', '7', '7', '9', '/', '3', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '5', '6', '2', '4', '7', '/', '3', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '2', '1', '6', '9', '1', '/', '1', '8', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '6', '2', '4', '9', '/', '4', '3', '7', '5', '0', '0', '0']), .str (String.ofList ['1', '5', '6', '2', '4', '9', '/', '4', '3', '7', '5', '0', '0', '0'])]
noncomputable def fragment14446322Acc00500 : List (String × SourceJson) := (fragment14446322Field004Key00, fragment14446322Field004Value00) :: fragment14446322Acc00400
noncomputable def fragment14446322Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '9', '2', '0', '1', '/', '8', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '9', '2', '0', '1', '/', '8', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '3', '5', '8', '7', '7', '9', '/', '3', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '5', '6', '2', '4', '7', '/', '3', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '2', '1', '6', '9', '1', '/', '1', '8', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '2', '4', '9', '/', '4', '3', '7', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '2', '4', '9', '/', '4', '3', '7', '5', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14446322_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 328) (SourceJson.white (fragment14446322Field004Chars00 ++ tail)) fragment14446322Acc00400 =
      SourceJson.object (fuel + 327) (SourceJson.white tail) fragment14446322Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14446322_object_field_004"
  err.flush

noncomputable def fragment14446322Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment14446322Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '8', '3', '1', '8', '7', '4', '7', '0', '0', '7', '7', '2', '0', '6', '8', '7', '3', '/', '2', '3', '9', '2', '4', '1', '0', '4', '9', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '2', '2', '3', '1', '7', '5', '1', '4', '4', '6', '4', '7', '8', '8', '5', '3', '/', '2', '3', '9', '2', '4', '1', '0', '4', '9', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '3', '7', '8', '3', '6', '4', '0', '6', '2', '2', '5', '0', '2', '1', '3', '/', '6', '2', '9', '5', '8', '1', '7', '0', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '9', '5', '2', '9', '3', '0', '8', '4', '3', '7', '6', '2', '5', '4', '7', '9', '/', '4', '7', '8', '4', '8', '2', '0', '9', '9', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '6', '0', '1', '4', '3', '4', '5', '3', '3', '3', '6', '5', '7', '/', '1', '0', '4', '9', '3', '0', '2', '8', '4', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '2', '0', '4', '0', '7', '7', '8', '8', '8', '6', '5', '3', '0', '3', '/', '6', '2', '9', '5', '8', '1', '7', '0', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '6', '5', '1', '5', '3', '1', '4', '2', '4', '9', '2', '3', '6', '0', '3', '/', '6', '2', '9', '5', '8', '1', '7', '0', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '3', '0', '4', '3', '3', '6', '4', '1', '1', '9', '0', '6', '8', '7', '/', '1', '0', '4', '9', '3', '0', '2', '8', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '5', '3', '6', '4', '3', '2', '6', '3', '3', '8', '3', '2', '0', '3', '5', '9', '/', '2', '3', '9', '2', '4', '1', '0', '4', '9', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '4', '8', '6', '7', '7', '0', '3', '1', '2', '5', '8', '3', '9', '0', '5', '9', '/', '2', '3', '9', '2', '4', '1', '0', '4', '9', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment14446322Acc00600 : List (String × SourceJson) := (fragment14446322Field005Key00, fragment14446322Field005Value00) :: fragment14446322Acc00500
noncomputable def fragment14446322Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '3', '1', '8', '7', '4', '7', '0', '0', '7', '7', '2', '0', '6', '8', '7', '3', '/', '2', '3', '9', '2', '4', '1', '0', '4', '9', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '2', '2', '3', '1', '7', '5', '1', '4', '4', '6', '4', '7', '8', '8', '5', '3', '/', '2', '3', '9', '2', '4', '1', '0', '4', '9', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '3', '7', '8', '3', '6', '4', '0', '6', '2', '2', '5', '0', '2', '1', '3', '/', '6', '2', '9', '5', '8', '1', '7', '0', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '9', '5', '2', '9', '3', '0', '8', '4', '3', '7', '6', '2', '5', '4', '7', '9', '/', '4', '7', '8', '4', '8', '2', '0', '9', '9', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '6', '0', '1', '4', '3', '4', '5', '3', '3', '3', '6', '5', '7', '/', '1', '0', '4', '9', '3', '0', '2', '8', '4', '9', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '2', '0', '4', '0', '7', '7', '8', '8', '8', '6', '5', '3', '0', '3', '/', '6', '2', '9', '5', '8', '1', '7', '0', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '6', '5', '1', '5', '3', '1', '4', '2', '4', '9', '2', '3', '6', '0', '3', '/', '6', '2', '9', '5', '8', '1', '7', '0', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '3', '0', '4', '3', '3', '6', '4', '1', '1', '9', '0', '6', '8', '7', '/', '1', '0', '4', '9', '3', '0', '2', '8', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '5', '3', '6', '4', '3', '2', '6', '3', '3', '8', '3', '2', '0', '3', '5', '9', '/', '2', '3', '9', '2', '4', '1', '0', '4', '9', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '4', '8', '6', '7', '7', '0', '3', '1', '2', '5', '8', '3', '9', '0', '5', '9', '/', '2', '3', '9', '2', '4', '1', '0', '4', '9', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14446322_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 327) (SourceJson.white (fragment14446322Field005Chars00 ++ tail)) fragment14446322Acc00500 =
      SourceJson.object (fuel + 326) (SourceJson.white tail) fragment14446322Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14446322_object_field_005"
  err.flush

noncomputable def fragment14446322Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14446322Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '1', '3', '9', '9', '2', '6', '9', '2', '0', '1', '5', '5', '2', '9', '5', '9', '4', '7', '2', '6', '6', '7', '9', '8', '5', '0', '5', '1', '0', '5', '0', '7', '5', '5', '2', '9', '5', '9', '9', '5', '7', '4', '0', '7', '5', '0', '2', '6', '0', '4', '7', '3', '3', '2', '0', '3', '1', '2', '5', '/', '6', '1', '1', '6', '4', '6', '5', '0', '4', '8', '6', '2', '3', '0', '5', '5', '9', '2', '4', '0', '7', '5', '2', '4', '1', '4', '9', '4', '4', '7', '8', '8', '6', '5', '9', '0', '9', '0', '0', '3', '6', '0', '1', '7', '9', '5', '2', '7', '8', '5', '5', '8', '2', '4', '6', '3', '9', '9', '1', '9', '1', '3', '9', '9', '3', '7', '6', '1', '8', '9', '4', '4'])
noncomputable def fragment14446322Acc00700 : List (String × SourceJson) := (fragment14446322Field006Key00, fragment14446322Field006Value00) :: fragment14446322Acc00600
noncomputable def fragment14446322Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '1', '3', '9', '9', '2', '6', '9', '2', '0', '1', '5', '5', '2', '9', '5', '9', '4', '7', '2', '6', '6', '7', '9', '8', '5', '0', '5', '1', '0', '5', '0', '7', '5', '5', '2', '9', '5', '9', '9', '5', '7', '4', '0', '7', '5', '0', '2', '6', '0', '4', '7', '3', '3', '2', '0', '3', '1', '2', '5', '/', '6', '1', '1', '6', '4', '6', '5', '0', '4', '8', '6', '2', '3', '0', '5', '5', '9', '2', '4', '0', '7', '5', '2', '4', '1', '4', '9', '4', '4', '7', '8', '8', '6', '5', '9', '0', '9', '0', '0', '3', '6', '0', '1', '7', '9', '5', '2', '7', '8', '5', '5', '8', '2', '4', '6', '3', '9', '9', '1', '9', '1', '3', '9', '9', '3', '7', '6', '1', '8', '9', '4', '4', '"', ',']

theorem object_fragment14446322_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 326) (SourceJson.white (fragment14446322Field006Chars00 ++ tail)) fragment14446322Acc00600 =
      SourceJson.object (fuel + 325) (SourceJson.white tail) fragment14446322Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14446322_object_field_006"
  err.flush

noncomputable def fragment14446322Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14446322Field007Value00 : SourceJson := .str (String.ofList ['3', '1', '4', '3', '3', '0', '7', '5', '6', '7', '4', '1', '8', '8', '2', '7', '0', '3', '3', '2', '7', '1', '4', '9', '4', '4', '2', '0', '3', '2', '2', '1', '4', '3', '0', '3', '8', '6', '0', '7', '4', '3', '6', '4', '2', '6', '8', '8', '5', '4', '2', '2', '3', '7', '3', '3', '1', '7', '3', '5', '0', '1', '9', '7', '4', '2', '0', '2', '4', '4', '9', '7', '6', '1', '0', '8', '6', '1', '5', '1', '2', '5', '3', '9', '4', '5', '8', '6', '6', '7', '5', '7', '8', '1', '2', '3', '3', '7', '7', '1', '3', '0', '5', '1', '3', '6', '5', '5', '1', '4', '5', '9', '4', '7', '8', '4', '6', '9', '1', '0', '9', '4', '5', '5', '4', '8', '8', '4', '9', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '4', '3', '7', '6', '1', '6', '3', '1', '1', '4', '9', '9', '8', '3', '4', '5', '0', '0', '1', '4', '9', '6', '7', '9', '1', '0', '8', '7', '6', '2', '0', '7', '3', '1', '8', '4', '7', '6', '1', '5', '5', '2', '1', '9', '6', '4', '2', '7', '5', '1', '2', '6', '3', '9', '4', '0', '6', '1', '3', '9', '0', '5', '2', '8', '0', '8', '6', '7', '6', '4', '3', '5', '2', '0', '2', '5', '4', '9', '0', '8', '1', '7', '0', '3', '5', '4', '6', '7', '5', '3', '0', '6', '8', '2', '0', '4', '1', '8', '4', '4', '1', '0', '0', '5', '4', '4', '9', '0', '0', '5', '5', '2', '6', '9', '0', '6', '4', '4', '0', '0', '5', '6', '3', '4', '8', '8', '7', '2', '0', '3', '5', '8', '6', '3', '3', '9', '0', '5', '5', '3', '7', '2', '9', '6', '4', '8', '2', '3', '0', '8', '3', '4', '1', '9', '4', '6', '9', '7', '9', '2', '5', '4', '9', '9'])
noncomputable def fragment14446322Acc00800 : List (String × SourceJson) := (fragment14446322Field007Key00, fragment14446322Field007Value00) :: fragment14446322Acc00700
noncomputable def fragment14446322Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '1', '4', '3', '3', '0', '7', '5', '6', '7', '4', '1', '8', '8', '2', '7', '0', '3', '3', '2', '7', '1', '4', '9', '4', '4', '2', '0', '3', '2', '2', '1', '4', '3', '0', '3', '8', '6', '0', '7', '4', '3', '6', '4', '2', '6', '8', '8', '5', '4', '2', '2', '3', '7', '3', '3', '1', '7', '3', '5', '0', '1', '9', '7', '4', '2', '0', '2', '4', '4', '9', '7', '6', '1', '0', '8', '6', '1', '5', '1', '2', '5', '3', '9', '4', '5', '8', '6', '6', '7', '5', '7', '8', '1', '2', '3', '3', '7', '7', '1', '3', '0', '5', '1', '3', '6', '5', '5', '1', '4', '5', '9', '4', '7', '8', '4', '6', '9', '1', '0', '9', '4', '5', '5', '4', '8', '8', '4', '9', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '4', '3', '7', '6', '1', '6', '3', '1', '1', '4', '9', '9', '8', '3', '4', '5', '0', '0', '1', '4', '9', '6', '7', '9', '1', '0', '8', '7', '6', '2', '0', '7', '3', '1', '8', '4', '7', '6', '1', '5', '5', '2', '1', '9', '6', '4', '2', '7', '5', '1', '2', '6', '3', '9', '4', '0', '6', '1', '3', '9', '0', '5', '2', '8', '0', '8', '6', '7', '6', '4', '3', '5', '2', '0', '2', '5', '4', '9', '0', '8', '1', '7', '0', '3', '5', '4', '6', '7', '5', '3', '0', '6', '8', '2', '0', '4', '1', '8', '4', '4', '1', '0', '0', '5', '4', '4', '9', '0', '0', '5', '5', '2', '6', '9', '0', '6', '4', '4', '0', '0', '5', '6', '3', '4', '8', '8', '7', '2', '0', '3', '5', '8', '6', '3', '3', '9', '0', '5', '5', '3', '7', '2', '9', '6', '4', '8', '2', '3', '0', '8', '3', '4', '1', '9', '4', '6', '9', '7', '9', '2', '5', '4', '9', '9', '"', ',']

theorem object_fragment14446322_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 325) (SourceJson.white (fragment14446322Field007Chars00 ++ tail)) fragment14446322Acc00700 =
      SourceJson.object (fuel + 324) (SourceJson.white tail) fragment14446322Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14446322_object_field_007"
  err.flush

noncomputable def fragment14446322Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14446322Field008Value00 : SourceJson := .str (String.ofList ['2', '3', '4', '9', '7', '1', '1', '9', '1', '1', '3', '7', '6', '7', '9', '1', '9', '6'])
noncomputable def fragment14446322Acc00900 : List (String × SourceJson) := (fragment14446322Field008Key00, fragment14446322Field008Value00) :: fragment14446322Acc00800
noncomputable def fragment14446322Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '4', '9', '7', '1', '1', '9', '1', '1', '3', '7', '6', '7', '9', '1', '9', '6', '"', ',']

theorem object_fragment14446322_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 324) (SourceJson.white (fragment14446322Field008Chars00 ++ tail)) fragment14446322Acc00800 =
      SourceJson.object (fuel + 323) (SourceJson.white tail) fragment14446322Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14446322_object_field_008"
  err.flush

noncomputable def fragment14446322Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14446322Field009Value00 : SourceJson := .str (String.ofList ['1', '6', '1', '3', '1', '9', '2', '5', '9', '2', '4', '2', '2', '8', '4', '2', '2', '2', '1'])
noncomputable def fragment14446322Acc01000 : List (String × SourceJson) := (fragment14446322Field009Key00, fragment14446322Field009Value00) :: fragment14446322Acc00900
noncomputable def fragment14446322Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '1', '3', '1', '9', '2', '5', '9', '2', '4', '2', '2', '8', '4', '2', '2', '2', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment14446322_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 323) (SourceJson.white (fragment14446322Field009Chars00 ++ tail)) fragment14446322Acc00900 =
      .ok (.obj (fragment14446322Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14446322_object_field_009"
  err.flush

noncomputable def fragment14446322Chars : List Char := '{' :: (fragment14446322Field000Chars00 ++ fragment14446322Field001Chars00 ++ fragment14446322Field002Chars00 ++ fragment14446322Field003Chars00 ++ fragment14446322Field004Chars00 ++ fragment14446322Field005Chars00 ++ fragment14446322Field006Chars00 ++ fragment14446322Field007Chars00 ++ fragment14446322Field008Chars00 ++ fragment14446322Field009Chars00)
noncomputable def fragment14446322Value : SourceJson := .obj (fragment14446322Acc01000.reverse)

theorem value_fragment14446322 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 333) (fragment14446322Chars ++ tail) =
      .ok (fragment14446322Value, tail) := by
  have hinput : fragment14446322Chars ++ tail = '{' :: (fragment14446322Field000Chars00 ++ (fragment14446322Field001Chars00 ++ (fragment14446322Field002Chars00 ++ (fragment14446322Field003Chars00 ++ (fragment14446322Field004Chars00 ++ (fragment14446322Field005Chars00 ++ (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment14446322Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 333) (fragment14446322Chars ++ tail) =
        SourceJson.value (fuel + 333) ('{' :: (fragment14446322Field000Chars00 ++ (fragment14446322Field001Chars00 ++ (fragment14446322Field002Chars00 ++ (fragment14446322Field003Chars00 ++ (fragment14446322Field004Chars00 ++ (fragment14446322Field005Chars00 ++ (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 333)) hinput
    _ = SourceJson.object (fuel + 332) (SourceJson.white (fragment14446322Field000Chars00 ++ (fragment14446322Field001Chars00 ++ (fragment14446322Field002Chars00 ++ (fragment14446322Field003Chars00 ++ (fragment14446322Field004Chars00 ++ (fragment14446322Field005Chars00 ++ (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail)))))))))))) fragment14446322Acc00000 := by rfl
    _ = SourceJson.object (fuel + 331) (SourceJson.white (fragment14446322Field001Chars00 ++ (fragment14446322Field002Chars00 ++ (fragment14446322Field003Chars00 ++ (fragment14446322Field004Chars00 ++ (fragment14446322Field005Chars00 ++ (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail))))))))))) fragment14446322Acc00100 := object_fragment14446322_field_000 fuel (fragment14446322Field001Chars00 ++ (fragment14446322Field002Chars00 ++ (fragment14446322Field003Chars00 ++ (fragment14446322Field004Chars00 ++ (fragment14446322Field005Chars00 ++ (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 330) (SourceJson.white (fragment14446322Field002Chars00 ++ (fragment14446322Field003Chars00 ++ (fragment14446322Field004Chars00 ++ (fragment14446322Field005Chars00 ++ (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail)))))))))) fragment14446322Acc00200 := object_fragment14446322_field_001 fuel (fragment14446322Field002Chars00 ++ (fragment14446322Field003Chars00 ++ (fragment14446322Field004Chars00 ++ (fragment14446322Field005Chars00 ++ (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 329) (SourceJson.white (fragment14446322Field003Chars00 ++ (fragment14446322Field004Chars00 ++ (fragment14446322Field005Chars00 ++ (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail))))))))) fragment14446322Acc00300 := object_fragment14446322_field_002 fuel (fragment14446322Field003Chars00 ++ (fragment14446322Field004Chars00 ++ (fragment14446322Field005Chars00 ++ (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 328) (SourceJson.white (fragment14446322Field004Chars00 ++ (fragment14446322Field005Chars00 ++ (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail)))))))) fragment14446322Acc00400 := object_fragment14446322_field_003 fuel (fragment14446322Field004Chars00 ++ (fragment14446322Field005Chars00 ++ (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 327) (SourceJson.white (fragment14446322Field005Chars00 ++ (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail))))))) fragment14446322Acc00500 := object_fragment14446322_field_004 fuel (fragment14446322Field005Chars00 ++ (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 326) (SourceJson.white (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail)))))) fragment14446322Acc00600 := object_fragment14446322_field_005 fuel (fragment14446322Field006Chars00 ++ (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 325) (SourceJson.white (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail))))) fragment14446322Acc00700 := object_fragment14446322_field_006 fuel (fragment14446322Field007Chars00 ++ (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 324) (SourceJson.white (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail)))) fragment14446322Acc00800 := object_fragment14446322_field_007 fuel (fragment14446322Field008Chars00 ++ (fragment14446322Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 323) (SourceJson.white (fragment14446322Field009Chars00 ++ (tail))) fragment14446322Acc00900 := object_fragment14446322_field_008 fuel (fragment14446322Field009Chars00 ++ (tail))
    _ = .ok (fragment14446322Value, tail) := object_fragment14446322_field_009 fuel (tail)

noncomputable def fragment14448161Acc00000 : List (String × SourceJson) := []

noncomputable def fragment14448161Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment14448161Field000Value00 : SourceJson := .number (String.ofList ['6', '5', '9', '3'])
noncomputable def fragment14448161Acc00100 : List (String × SourceJson) := (fragment14448161Field000Key00, fragment14448161Field000Value00) :: fragment14448161Acc00000
noncomputable def fragment14448161Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '5', '9', '3', ',']

theorem object_fragment14448161_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 277) (SourceJson.white (fragment14448161Field000Chars00 ++ tail)) fragment14448161Acc00000 =
      SourceJson.object (fuel + 276) (SourceJson.white tail) fragment14448161Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14448161_object_field_000"
  err.flush

noncomputable def fragment14448161Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment14448161Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '7']), .number (String.ofList ['1', '3', '5']), .number (String.ofList ['1', '1', '7']), .number (String.ofList ['1', '1', '5']), .number (String.ofList ['1', '1', '1']), .number (String.ofList ['1', '0', '6']), .number (String.ofList ['9', '7']), .number (String.ofList ['5', '5'])]
noncomputable def fragment14448161Acc00200 : List (String × SourceJson) := (fragment14448161Field001Key00, fragment14448161Field001Value00) :: fragment14448161Acc00100
noncomputable def fragment14448161Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14448161_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 276) (SourceJson.white (fragment14448161Field001Chars00 ++ tail)) fragment14448161Acc00100 =
      SourceJson.object (fuel + 275) (SourceJson.white tail) fragment14448161Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14448161_object_field_001"
  err.flush

noncomputable def fragment14448161Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment14448161Field002Value00 : SourceJson := .str (String.ofList ['4', '7', '8', '1', '3', '0', '1', '9', '8', '8', '3', '3', '4', '5', '5', '0', '3', '7', '4', '1', '0', '9', '5', '3', '3', '4', '8', '1', '4', '1', '5', '0', '0', '5', '1', '/', '7', '2', '1', '8', '0', '7', '4', '0', '6', '5', '3', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14448161Acc00300 : List (String × SourceJson) := (fragment14448161Field002Key00, fragment14448161Field002Value00) :: fragment14448161Acc00200
noncomputable def fragment14448161Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '7', '8', '1', '3', '0', '1', '9', '8', '8', '3', '3', '4', '5', '5', '0', '3', '7', '4', '1', '0', '9', '5', '3', '3', '4', '8', '1', '4', '1', '5', '0', '0', '5', '1', '/', '7', '2', '1', '8', '0', '7', '4', '0', '6', '5', '3', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14448161_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 275) (SourceJson.white (fragment14448161Field002Chars00 ++ tail)) fragment14448161Acc00200 =
      SourceJson.object (fuel + 274) (SourceJson.white tail) fragment14448161Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14448161_object_field_002"
  err.flush

noncomputable def fragment14448161Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment14448161Field003Value00 : SourceJson := .str (String.ofList ['5', '2', '6', '5', '0', '7', '/', '6', '2', '1', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14448161Acc00400 : List (String × SourceJson) := (fragment14448161Field003Key00, fragment14448161Field003Value00) :: fragment14448161Acc00300
noncomputable def fragment14448161Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '2', '6', '5', '0', '7', '/', '6', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14448161_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 274) (SourceJson.white (fragment14448161Field003Chars00 ++ tail)) fragment14448161Acc00300 =
      SourceJson.object (fuel + 273) (SourceJson.white tail) fragment14448161Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14448161_object_field_003"
  err.flush

noncomputable def fragment14448161Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment14448161Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '8', '9', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '6', '8', '7', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '6', '8', '7', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '/', '3', '8', '4']), .str (String.ofList ['1', '1', '/', '3', '8', '4'])]
noncomputable def fragment14448161Acc00500 : List (String × SourceJson) := (fragment14448161Field004Key00, fragment14448161Field004Value00) :: fragment14448161Acc00400
noncomputable def fragment14448161Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '8', '9', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '6', '8', '7', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '6', '8', '7', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '3', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '3', '8', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14448161_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 273) (SourceJson.white (fragment14448161Field004Chars00 ++ tail)) fragment14448161Acc00400 =
      SourceJson.object (fuel + 272) (SourceJson.white tail) fragment14448161Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14448161_object_field_004"
  err.flush

noncomputable def fragment14448161Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment14448161Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '4', '9', '8', '3', '2', '9', '2', '2', '6', '1', '9', '8', '1', '/', '1', '0', '8', '2', '7', '4', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '4', '6', '7', '9', '9', '9', '9', '2', '6', '3', '7', '/', '2', '1', '6', '5', '4', '9', '2', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '8', '6', '0', '7', '3', '4', '6', '7', '8', '5', '7', '3', '/', '4', '8', '4', '3', '8', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '4', '8', '0', '1', '0', '4', '1', '5', '1', '4', '9', '7', '3', '7', '/', '5', '5', '2', '2', '0', '0', '5', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '5', '0', '9', '2', '1', '4', '3', '8', '6', '1', '7', '1', '/', '4', '8', '4', '3', '8', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '1', '7', '0', '6', '2', '7', '4', '5', '0', '0', '1', '/', '9', '6', '8', '7', '7', '2', '8', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '7', '3', '4', '8', '0', '9', '4', '3', '2', '1', '7', '3', '/', '2', '4', '2', '1', '9', '3', '2', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '6', '7', '8', '6', '1', '7', '8', '1', '9', '3', '8', '8', '9', '/', '1', '4', '5', '3', '1', '5', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '7', '4', '1', '8', '6', '2', '7', '4', '7', '1', '9', '8', '5', '3', '/', '5', '5', '2', '2', '0', '0', '5', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '3', '7', '9', '5', '9', '6', '3', '8', '3', '8', '7', '1', '3', '/', '5', '5', '2', '2', '0', '0', '5', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment14448161Acc00600 : List (String × SourceJson) := (fragment14448161Field005Key00, fragment14448161Field005Value00) :: fragment14448161Acc00500
noncomputable def fragment14448161Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '9', '8', '3', '2', '9', '2', '2', '6', '1', '9', '8', '1', '/', '1', '0', '8', '2', '7', '4', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '4', '6', '7', '9', '9', '9', '9', '2', '6', '3', '7', '/', '2', '1', '6', '5', '4', '9', '2', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '8', '6', '0', '7', '3', '4', '6', '7', '8', '5', '7', '3', '/', '4', '8', '4', '3', '8', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '4', '8', '0', '1', '0', '4', '1', '5', '1', '4', '9', '7', '3', '7', '/', '5', '5', '2', '2', '0', '0', '5', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '5', '0', '9', '2', '1', '4', '3', '8', '6', '1', '7', '1', '/', '4', '8', '4', '3', '8', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '1', '7', '0', '6', '2', '7', '4', '5', '0', '0', '1', '/', '9', '6', '8', '7', '7', '2', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '3', '4', '8', '0', '9', '4', '3', '2', '1', '7', '3', '/', '2', '4', '2', '1', '9', '3', '2', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '6', '7', '8', '6', '1', '7', '8', '1', '9', '3', '8', '8', '9', '/', '1', '4', '5', '3', '1', '5', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '7', '4', '1', '8', '6', '2', '7', '4', '7', '1', '9', '8', '5', '3', '/', '5', '5', '2', '2', '0', '0', '5', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '3', '7', '9', '5', '9', '6', '3', '8', '3', '8', '7', '1', '3', '/', '5', '5', '2', '2', '0', '0', '5', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14448161_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 272) (SourceJson.white (fragment14448161Field005Chars00 ++ tail)) fragment14448161Acc00500 =
      SourceJson.object (fuel + 271) (SourceJson.white tail) fragment14448161Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14448161_object_field_005"
  err.flush

noncomputable def fragment14448161Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14448161Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '1', '1', '8', '3', '8', '9', '7', '6', '8', '8', '4', '4', '7', '6', '3', '9', '8', '9', '8', '9', '1', '7', '4', '5', '4', '3', '3', '9', '0', '9', '6', '0', '9', '3', '1', '8', '4', '/', '8', '3', '9', '1', '4', '7', '4', '2', '2', '6', '3', '2', '2', '2', '1', '0', '8', '5', '5', '2', '8', '2', '5', '4', '0', '5', '8', '0', '0', '6', '5', '6', '4', '7', '0', '0', '7', '2', '5', '9', '1', '8', '1', '5', '0', '8', '0', '1', '0', '9', '3', '7', '5'])
noncomputable def fragment14448161Acc00700 : List (String × SourceJson) := (fragment14448161Field006Key00, fragment14448161Field006Value00) :: fragment14448161Acc00600
noncomputable def fragment14448161Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '1', '1', '8', '3', '8', '9', '7', '6', '8', '8', '4', '4', '7', '6', '3', '9', '8', '9', '8', '9', '1', '7', '4', '5', '4', '3', '3', '9', '0', '9', '6', '0', '9', '3', '1', '8', '4', '/', '8', '3', '9', '1', '4', '7', '4', '2', '2', '6', '3', '2', '2', '2', '1', '0', '8', '5', '5', '2', '8', '2', '5', '4', '0', '5', '8', '0', '0', '6', '5', '6', '4', '7', '0', '0', '7', '2', '5', '9', '1', '8', '1', '5', '0', '8', '0', '1', '0', '9', '3', '7', '5', '"', ',']

theorem object_fragment14448161_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 271) (SourceJson.white (fragment14448161Field006Chars00 ++ tail)) fragment14448161Acc00600 =
      SourceJson.object (fuel + 270) (SourceJson.white tail) fragment14448161Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14448161_object_field_006"
  err.flush

noncomputable def fragment14448161Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14448161Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '5', '1', '8', '3', '9', '6', '9', '5', '1', '4', '8', '1', '1', '8', '8', '8', '2', '0', '1', '9', '5', '3', '6', '6', '1', '4', '8', '5', '5', '6', '8', '1', '3', '4', '3', '6', '1', '5', '6', '3', '2', '8', '5', '5', '2', '5', '2', '2', '1', '2', '1', '2', '5', '3', '7', '3', '7', '0', '8', '7', '6', '6', '7', '4', '8', '2', '9', '3', '9', '6', '6', '7', '0', '6', '8', '5', '9', '6', '3', '6', '9', '5', '1', '0', '0', '9', '9', '0', '3', '9', '5', '3', '7', '9', '2', '5', '2', '0', '6', '2', '1', '5', '1', '7', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '0', '0', '6', '4', '4', '2', '1', '9', '3', '0', '9', '8', '3', '9', '8', '5', '1', '0', '5', '6', '0', '3', '7', '4', '3', '4', '3', '3', '9', '3', '5', '3', '3', '2', '6', '5', '2', '1', '5', '0', '3', '5', '1', '4', '2', '7', '7', '0', '0', '7', '2', '9', '7', '0', '1', '4', '6', '1', '7', '5', '2', '9', '5', '8', '3', '1', '2', '7', '2', '1', '5', '3', '3', '7', '5', '8', '8', '9', '4', '0', '5', '5', '0', '6', '1', '3', '3', '5', '1', '4', '2', '0', '6', '5', '5', '9', '6', '0', '2', '5', '3', '4', '5', '5', '7', '7', '0', '0', '6', '7', '5', '2', '7', '7', '0', '6', '3', '4', '7', '7', '8', '1', '2', '9', '1', '6', '2', '5', '8', '0', '7', '2', '1', '7', '4', '5', '6', '1'])
noncomputable def fragment14448161Acc00800 : List (String × SourceJson) := (fragment14448161Field007Key00, fragment14448161Field007Value00) :: fragment14448161Acc00700
noncomputable def fragment14448161Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '5', '1', '8', '3', '9', '6', '9', '5', '1', '4', '8', '1', '1', '8', '8', '8', '2', '0', '1', '9', '5', '3', '6', '6', '1', '4', '8', '5', '5', '6', '8', '1', '3', '4', '3', '6', '1', '5', '6', '3', '2', '8', '5', '5', '2', '5', '2', '2', '1', '2', '1', '2', '5', '3', '7', '3', '7', '0', '8', '7', '6', '6', '7', '4', '8', '2', '9', '3', '9', '6', '6', '7', '0', '6', '8', '5', '9', '6', '3', '6', '9', '5', '1', '0', '0', '9', '9', '0', '3', '9', '5', '3', '7', '9', '2', '5', '2', '0', '6', '2', '1', '5', '1', '7', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '0', '0', '6', '4', '4', '2', '1', '9', '3', '0', '9', '8', '3', '9', '8', '5', '1', '0', '5', '6', '0', '3', '7', '4', '3', '4', '3', '3', '9', '3', '5', '3', '3', '2', '6', '5', '2', '1', '5', '0', '3', '5', '1', '4', '2', '7', '7', '0', '0', '7', '2', '9', '7', '0', '1', '4', '6', '1', '7', '5', '2', '9', '5', '8', '3', '1', '2', '7', '2', '1', '5', '3', '3', '7', '5', '8', '8', '9', '4', '0', '5', '5', '0', '6', '1', '3', '3', '5', '1', '4', '2', '0', '6', '5', '5', '9', '6', '0', '2', '5', '3', '4', '5', '5', '7', '7', '0', '0', '6', '7', '5', '2', '7', '7', '0', '6', '3', '4', '7', '7', '8', '1', '2', '9', '1', '6', '2', '5', '8', '0', '7', '2', '1', '7', '4', '5', '6', '1', '"', ',']

theorem object_fragment14448161_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 270) (SourceJson.white (fragment14448161Field007Chars00 ++ tail)) fragment14448161Acc00700 =
      SourceJson.object (fuel + 269) (SourceJson.white tail) fragment14448161Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14448161_object_field_007"
  err.flush

noncomputable def fragment14448161Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14448161Field008Value00 : SourceJson := .str (String.ofList ['1', '7', '1', '0', '6', '4', '9', '0', '3', '5', '4', '2', '2', '1', '7'])
noncomputable def fragment14448161Acc00900 : List (String × SourceJson) := (fragment14448161Field008Key00, fragment14448161Field008Value00) :: fragment14448161Acc00800
noncomputable def fragment14448161Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '1', '0', '6', '4', '9', '0', '3', '5', '4', '2', '2', '1', '7', '"', ',']

theorem object_fragment14448161_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 269) (SourceJson.white (fragment14448161Field008Chars00 ++ tail)) fragment14448161Acc00800 =
      SourceJson.object (fuel + 268) (SourceJson.white tail) fragment14448161Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14448161_object_field_008"
  err.flush

noncomputable def fragment14448161Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14448161Field009Value00 : SourceJson := .str (String.ofList ['7', '6', '0', '0', '7', '6', '4', '7', '4', '6', '9', '4', '8', '3', '7'])
noncomputable def fragment14448161Acc01000 : List (String × SourceJson) := (fragment14448161Field009Key00, fragment14448161Field009Value00) :: fragment14448161Acc00900
noncomputable def fragment14448161Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '6', '0', '0', '7', '6', '4', '7', '4', '6', '9', '4', '8', '3', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment14448161_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 268) (SourceJson.white (fragment14448161Field009Chars00 ++ tail)) fragment14448161Acc00900 =
      .ok (.obj (fragment14448161Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14448161_object_field_009"
  err.flush

noncomputable def fragment14448161Chars : List Char := '{' :: (fragment14448161Field000Chars00 ++ fragment14448161Field001Chars00 ++ fragment14448161Field002Chars00 ++ fragment14448161Field003Chars00 ++ fragment14448161Field004Chars00 ++ fragment14448161Field005Chars00 ++ fragment14448161Field006Chars00 ++ fragment14448161Field007Chars00 ++ fragment14448161Field008Chars00 ++ fragment14448161Field009Chars00)
noncomputable def fragment14448161Value : SourceJson := .obj (fragment14448161Acc01000.reverse)

theorem value_fragment14448161 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 278) (fragment14448161Chars ++ tail) =
      .ok (fragment14448161Value, tail) := by
  have hinput : fragment14448161Chars ++ tail = '{' :: (fragment14448161Field000Chars00 ++ (fragment14448161Field001Chars00 ++ (fragment14448161Field002Chars00 ++ (fragment14448161Field003Chars00 ++ (fragment14448161Field004Chars00 ++ (fragment14448161Field005Chars00 ++ (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment14448161Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 278) (fragment14448161Chars ++ tail) =
        SourceJson.value (fuel + 278) ('{' :: (fragment14448161Field000Chars00 ++ (fragment14448161Field001Chars00 ++ (fragment14448161Field002Chars00 ++ (fragment14448161Field003Chars00 ++ (fragment14448161Field004Chars00 ++ (fragment14448161Field005Chars00 ++ (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 278)) hinput
    _ = SourceJson.object (fuel + 277) (SourceJson.white (fragment14448161Field000Chars00 ++ (fragment14448161Field001Chars00 ++ (fragment14448161Field002Chars00 ++ (fragment14448161Field003Chars00 ++ (fragment14448161Field004Chars00 ++ (fragment14448161Field005Chars00 ++ (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail)))))))))))) fragment14448161Acc00000 := by rfl
    _ = SourceJson.object (fuel + 276) (SourceJson.white (fragment14448161Field001Chars00 ++ (fragment14448161Field002Chars00 ++ (fragment14448161Field003Chars00 ++ (fragment14448161Field004Chars00 ++ (fragment14448161Field005Chars00 ++ (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail))))))))))) fragment14448161Acc00100 := object_fragment14448161_field_000 fuel (fragment14448161Field001Chars00 ++ (fragment14448161Field002Chars00 ++ (fragment14448161Field003Chars00 ++ (fragment14448161Field004Chars00 ++ (fragment14448161Field005Chars00 ++ (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 275) (SourceJson.white (fragment14448161Field002Chars00 ++ (fragment14448161Field003Chars00 ++ (fragment14448161Field004Chars00 ++ (fragment14448161Field005Chars00 ++ (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail)))))))))) fragment14448161Acc00200 := object_fragment14448161_field_001 fuel (fragment14448161Field002Chars00 ++ (fragment14448161Field003Chars00 ++ (fragment14448161Field004Chars00 ++ (fragment14448161Field005Chars00 ++ (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 274) (SourceJson.white (fragment14448161Field003Chars00 ++ (fragment14448161Field004Chars00 ++ (fragment14448161Field005Chars00 ++ (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail))))))))) fragment14448161Acc00300 := object_fragment14448161_field_002 fuel (fragment14448161Field003Chars00 ++ (fragment14448161Field004Chars00 ++ (fragment14448161Field005Chars00 ++ (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 273) (SourceJson.white (fragment14448161Field004Chars00 ++ (fragment14448161Field005Chars00 ++ (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail)))))))) fragment14448161Acc00400 := object_fragment14448161_field_003 fuel (fragment14448161Field004Chars00 ++ (fragment14448161Field005Chars00 ++ (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 272) (SourceJson.white (fragment14448161Field005Chars00 ++ (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail))))))) fragment14448161Acc00500 := object_fragment14448161_field_004 fuel (fragment14448161Field005Chars00 ++ (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 271) (SourceJson.white (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail)))))) fragment14448161Acc00600 := object_fragment14448161_field_005 fuel (fragment14448161Field006Chars00 ++ (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 270) (SourceJson.white (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail))))) fragment14448161Acc00700 := object_fragment14448161_field_006 fuel (fragment14448161Field007Chars00 ++ (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 269) (SourceJson.white (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail)))) fragment14448161Acc00800 := object_fragment14448161_field_007 fuel (fragment14448161Field008Chars00 ++ (fragment14448161Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 268) (SourceJson.white (fragment14448161Field009Chars00 ++ (tail))) fragment14448161Acc00900 := object_fragment14448161_field_008 fuel (fragment14448161Field009Chars00 ++ (tail))
    _ = .ok (fragment14448161Value, tail) := object_fragment14448161_field_009 fuel (tail)

noncomputable def fragment14449800Acc00000 : List (String × SourceJson) := []

noncomputable def fragment14449800Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment14449800Field000Value00 : SourceJson := .number (String.ofList ['6', '5', '9', '4'])
noncomputable def fragment14449800Acc00100 : List (String × SourceJson) := (fragment14449800Field000Key00, fragment14449800Field000Value00) :: fragment14449800Acc00000
noncomputable def fragment14449800Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '5', '9', '4', ',']

theorem object_fragment14449800_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 279) (SourceJson.white (fragment14449800Field000Chars00 ++ tail)) fragment14449800Acc00000 =
      SourceJson.object (fuel + 278) (SourceJson.white tail) fragment14449800Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14449800_object_field_000"
  err.flush

noncomputable def fragment14449800Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment14449800Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '7']), .number (String.ofList ['1', '3', '5']), .number (String.ofList ['1', '1', '7']), .number (String.ofList ['9', '8']), .number (String.ofList ['8', '4']), .number (String.ofList ['8', '3']), .number (String.ofList ['5', '6']), .number (String.ofList ['2', '7'])]
noncomputable def fragment14449800Acc00200 : List (String × SourceJson) := (fragment14449800Field001Key00, fragment14449800Field001Value00) :: fragment14449800Acc00100
noncomputable def fragment14449800Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14449800_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 278) (SourceJson.white (fragment14449800Field001Chars00 ++ tail)) fragment14449800Acc00100 =
      SourceJson.object (fuel + 277) (SourceJson.white tail) fragment14449800Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14449800_object_field_001"
  err.flush

noncomputable def fragment14449800Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment14449800Field002Value00 : SourceJson := .str (String.ofList ['6', '8', '5', '5', '8', '3', '5', '5', '6', '2', '3', '8', '3', '9', '9', '1', '9', '4', '3', '3', '2', '9', '6', '7', '5', '5', '2', '9', '9', '5', '6', '1', '4', '9', '9', '1', '2', '4', '1', '9', '9', '1', '9', '/', '1', '0', '0', '7', '3', '9', '8', '8', '1', '8', '3', '4', '9', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14449800Acc00300 : List (String × SourceJson) := (fragment14449800Field002Key00, fragment14449800Field002Value00) :: fragment14449800Acc00200
noncomputable def fragment14449800Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '8', '5', '5', '8', '3', '5', '5', '6', '2', '3', '8', '3', '9', '9', '1', '9', '4', '3', '3', '2', '9', '6', '7', '5', '5', '2', '9', '9', '5', '6', '1', '4', '9', '9', '1', '2', '4', '1', '9', '9', '1', '9', '/', '1', '0', '0', '7', '3', '9', '8', '8', '1', '8', '3', '4', '9', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14449800_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 277) (SourceJson.white (fragment14449800Field002Chars00 ++ tail)) fragment14449800Acc00200 =
      SourceJson.object (fuel + 276) (SourceJson.white tail) fragment14449800Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14449800_object_field_002"
  err.flush

noncomputable def fragment14449800Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment14449800Field003Value00 : SourceJson := .str (String.ofList ['2', '0', '1', '5', '2', '6', '9', '/', '2', '9', '8', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14449800Acc00400 : List (String × SourceJson) := (fragment14449800Field003Key00, fragment14449800Field003Value00) :: fragment14449800Acc00300
noncomputable def fragment14449800Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '0', '1', '5', '2', '6', '9', '/', '2', '9', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14449800_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 276) (SourceJson.white (fragment14449800Field003Chars00 ++ tail)) fragment14449800Acc00300 =
      SourceJson.object (fuel + 275) (SourceJson.white tail) fragment14449800Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14449800_object_field_003"
  err.flush

noncomputable def fragment14449800Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment14449800Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '9', '3', '6', '9', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '3', '6', '9', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '8', '1', '2', '9', '/', '2', '2', '0', '8', '0', '0', '0']), .str (String.ofList ['3', '1', '3', '5', '8', '7', '7', '9', '/', '3', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '5', '6', '2', '4', '7', '/', '3', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '2', '1', '6', '9', '1', '/', '1', '8', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '1', '2', '1', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '1', '2', '1', '/', '9', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment14449800Acc00500 : List (String × SourceJson) := (fragment14449800Field004Key00, fragment14449800Field004Value00) :: fragment14449800Acc00400
noncomputable def fragment14449800Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '3', '6', '9', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '3', '6', '9', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '1', '2', '9', '/', '2', '2', '0', '8', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '3', '5', '8', '7', '7', '9', '/', '3', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '5', '6', '2', '4', '7', '/', '3', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '2', '1', '6', '9', '1', '/', '1', '8', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '2', '1', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '2', '1', '/', '9', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14449800_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 275) (SourceJson.white (fragment14449800Field004Chars00 ++ tail)) fragment14449800Acc00400 =
      SourceJson.object (fuel + 274) (SourceJson.white tail) fragment14449800Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14449800_object_field_004"
  err.flush

noncomputable def fragment14449800Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment14449800Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '5', '2', '7', '8', '9', '0', '6', '6', '3', '1', '9', '8', '7', '/', '3', '1', '4', '8', '3', '2', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '1', '0', '1', '0', '2', '5', '5', '1', '2', '0', '0', '7', '/', '3', '1', '4', '8', '3', '2', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '3', '1', '9', '3', '4', '4', '8', '9', '9', '7', '6', '7', '/', '1', '8', '6', '4', '1', '3', '8', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '0', '1', '3', '6', '6', '7', '9', '2', '9', '7', '9', '5', '9', '/', '5', '6', '6', '6', '9', '8', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '0', '6', '1', '5', '4', '9', '5', '1', '0', '9', '/', '2', '9', '8', '2', '6', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '1', '4', '8', '4', '4', '1', '5', '3', '3', '6', '2', '9', '/', '3', '7', '2', '8', '2', '7', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '7', '4', '8', '1', '6', '0', '9', '2', '8', '4', '1', '7', '/', '1', '1', '1', '8', '4', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '4', '7', '2', '3', '7', '6', '4', '2', '1', '4', '9', '9', '/', '5', '5', '9', '2', '4', '1', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '6', '8', '3', '1', '0', '1', '2', '6', '7', '3', '8', '4', '9', '/', '2', '8', '3', '3', '4', '9', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '0', '7', '1', '1', '8', '3', '7', '9', '2', '5', '5', '4', '9', '/', '2', '8', '3', '3', '4', '9', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment14449800Acc00600 : List (String × SourceJson) := (fragment14449800Field005Key00, fragment14449800Field005Value00) :: fragment14449800Acc00500
noncomputable def fragment14449800Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '2', '7', '8', '9', '0', '6', '6', '3', '1', '9', '8', '7', '/', '3', '1', '4', '8', '3', '2', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '1', '0', '1', '0', '2', '5', '5', '1', '2', '0', '0', '7', '/', '3', '1', '4', '8', '3', '2', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '3', '1', '9', '3', '4', '4', '8', '9', '9', '7', '6', '7', '/', '1', '8', '6', '4', '1', '3', '8', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '0', '1', '3', '6', '6', '7', '9', '2', '9', '7', '9', '5', '9', '/', '5', '6', '6', '6', '9', '8', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '0', '6', '1', '5', '4', '9', '5', '1', '0', '9', '/', '2', '9', '8', '2', '6', '2', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '1', '4', '8', '4', '4', '1', '5', '3', '3', '6', '2', '9', '/', '3', '7', '2', '8', '2', '7', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '7', '4', '8', '1', '6', '0', '9', '2', '8', '4', '1', '7', '/', '1', '1', '1', '8', '4', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '4', '7', '2', '3', '7', '6', '4', '2', '1', '4', '9', '9', '/', '5', '5', '9', '2', '4', '1', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '6', '8', '3', '1', '0', '1', '2', '6', '7', '3', '8', '4', '9', '/', '2', '8', '3', '3', '4', '9', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '0', '7', '1', '1', '8', '3', '7', '9', '2', '5', '5', '4', '9', '/', '2', '8', '3', '3', '4', '9', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14449800_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 274) (SourceJson.white (fragment14449800Field005Chars00 ++ tail)) fragment14449800Acc00500 =
      SourceJson.object (fuel + 273) (SourceJson.white tail) fragment14449800Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14449800_object_field_005"
  err.flush

noncomputable def fragment14449800Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14449800Field006Value00 : SourceJson := .str (String.ofList ['1', '5', '1', '0', '8', '1', '8', '1', '8', '7', '2', '0', '6', '0', '2', '2', '2', '4', '0', '2', '7', '1', '8', '5', '8', '3', '7', '2', '5', '9', '4', '5', '8', '5', '5', '5', '0', '3', '8', '3', '1', '7', '9', '3', '7', '6', '2', '2', '0', '1', '2', '2', '8', '5', '/', '2', '0', '0', '8', '7', '6', '1', '3', '4', '2', '4', '8', '7', '4', '2', '0', '3', '9', '7', '9', '7', '5', '1', '7', '9', '1', '3', '8', '9', '5', '9', '9', '3', '4', '9', '1', '6', '9', '9', '1', '2', '4', '7', '7', '4', '2', '0', '7', '9', '6', '7', '0', '4', '0', '4', '9', '6', '4', '3', '5', '1', '8', '0', '0', '2'])
noncomputable def fragment14449800Acc00700 : List (String × SourceJson) := (fragment14449800Field006Key00, fragment14449800Field006Value00) :: fragment14449800Acc00600
noncomputable def fragment14449800Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '1', '0', '8', '1', '8', '1', '8', '7', '2', '0', '6', '0', '2', '2', '2', '4', '0', '2', '7', '1', '8', '5', '8', '3', '7', '2', '5', '9', '4', '5', '8', '5', '5', '5', '0', '3', '8', '3', '1', '7', '9', '3', '7', '6', '2', '2', '0', '1', '2', '2', '8', '5', '/', '2', '0', '0', '8', '7', '6', '1', '3', '4', '2', '4', '8', '7', '4', '2', '0', '3', '9', '7', '9', '7', '5', '1', '7', '9', '1', '3', '8', '9', '5', '9', '9', '3', '4', '9', '1', '6', '9', '9', '1', '2', '4', '7', '7', '4', '2', '0', '7', '9', '6', '7', '0', '4', '0', '4', '9', '6', '4', '3', '5', '1', '8', '0', '0', '2', '"', ',']

theorem object_fragment14449800_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 273) (SourceJson.white (fragment14449800Field006Chars00 ++ tail)) fragment14449800Acc00600 =
      SourceJson.object (fuel + 272) (SourceJson.white tail) fragment14449800Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14449800_object_field_006"
  err.flush

noncomputable def fragment14449800Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14449800Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '9', '2', '8', '7', '7', '9', '9', '8', '7', '2', '3', '0', '4', '8', '1', '3', '6', '6', '2', '2', '9', '8', '1', '0', '6', '7', '4', '6', '6', '9', '2', '8', '8', '0', '9', '3', '7', '6', '1', '8', '5', '0', '3', '1', '6', '4', '9', '8', '6', '3', '5', '3', '9', '2', '4', '7', '2', '8', '4', '3', '1', '2', '7', '4', '3', '9', '8', '8', '6', '7', '6', '7', '1', '8', '8', '9', '4', '0', '2', '0', '7', '1', '5', '2', '1', '5', '9', '7', '8', '6', '4', '2', '0', '1', '2', '3', '7', '8', '1', '2', '9', '8', '7', '5', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '4', '1', '7', '0', '6', '8', '9', '9', '2', '1', '6', '6', '7', '4', '2', '5', '8', '0', '2', '5', '9', '7', '5', '5', '6', '5', '9', '5', '9', '2', '1', '1', '5', '0', '6', '7', '5', '4', '3', '0', '6', '1', '8', '9', '4', '7', '4', '4', '1', '4', '8', '5', '4', '0', '2', '9', '3', '5', '2', '3', '3', '4', '9', '8', '2', '2', '3', '4', '4', '5', '2', '0', '7', '4', '8', '1', '6', '3', '5', '2', '0', '6', '0', '6', '9', '9', '5', '7', '4', '8', '5', '5', '1', '6', '9', '8', '2', '6', '3', '7', '8', '2', '0', '4', '9', '3', '9', '7', '7', '2', '5', '3', '9', '4', '9', '5', '0', '8', '0', '6', '6', '5', '9', '3', '7', '8', '5', '2', '5', '0', '9', '0', '4', '2', '1', '3', '9'])
noncomputable def fragment14449800Acc00800 : List (String × SourceJson) := (fragment14449800Field007Key00, fragment14449800Field007Value00) :: fragment14449800Acc00700
noncomputable def fragment14449800Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '9', '2', '8', '7', '7', '9', '9', '8', '7', '2', '3', '0', '4', '8', '1', '3', '6', '6', '2', '2', '9', '8', '1', '0', '6', '7', '4', '6', '6', '9', '2', '8', '8', '0', '9', '3', '7', '6', '1', '8', '5', '0', '3', '1', '6', '4', '9', '8', '6', '3', '5', '3', '9', '2', '4', '7', '2', '8', '4', '3', '1', '2', '7', '4', '3', '9', '8', '8', '6', '7', '6', '7', '1', '8', '8', '9', '4', '0', '2', '0', '7', '1', '5', '2', '1', '5', '9', '7', '8', '6', '4', '2', '0', '1', '2', '3', '7', '8', '1', '2', '9', '8', '7', '5', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '4', '1', '7', '0', '6', '8', '9', '9', '2', '1', '6', '6', '7', '4', '2', '5', '8', '0', '2', '5', '9', '7', '5', '5', '6', '5', '9', '5', '9', '2', '1', '1', '5', '0', '6', '7', '5', '4', '3', '0', '6', '1', '8', '9', '4', '7', '4', '4', '1', '4', '8', '5', '4', '0', '2', '9', '3', '5', '2', '3', '3', '4', '9', '8', '2', '2', '3', '4', '4', '5', '2', '0', '7', '4', '8', '1', '6', '3', '5', '2', '0', '6', '0', '6', '9', '9', '5', '7', '4', '8', '5', '5', '1', '6', '9', '8', '2', '6', '3', '7', '8', '2', '0', '4', '9', '3', '9', '7', '7', '2', '5', '3', '9', '4', '9', '5', '0', '8', '0', '6', '6', '5', '9', '3', '7', '8', '5', '2', '5', '0', '9', '0', '4', '2', '1', '3', '9', '"', ',']

theorem object_fragment14449800_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 272) (SourceJson.white (fragment14449800Field007Chars00 ++ tail)) fragment14449800Acc00700 =
      SourceJson.object (fuel + 271) (SourceJson.white tail) fragment14449800Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14449800_object_field_007"
  err.flush

noncomputable def fragment14449800Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14449800Field008Value00 : SourceJson := .str (String.ofList ['5', '9', '5', '8', '8', '6', '3', '6', '2', '0', '7', '6', '4', '5', '7', '4', '3', '7'])
noncomputable def fragment14449800Acc00900 : List (String × SourceJson) := (fragment14449800Field008Key00, fragment14449800Field008Value00) :: fragment14449800Acc00800
noncomputable def fragment14449800Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '5', '8', '8', '6', '3', '6', '2', '0', '7', '6', '4', '5', '7', '4', '3', '7', '"', ',']

theorem object_fragment14449800_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 271) (SourceJson.white (fragment14449800Field008Chars00 ++ tail)) fragment14449800Acc00800 =
      SourceJson.object (fuel + 270) (SourceJson.white tail) fragment14449800Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14449800_object_field_008"
  err.flush

noncomputable def fragment14449800Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14449800Field009Value00 : SourceJson := .str (String.ofList ['4', '0', '3', '5', '9', '2', '4', '9', '0', '4', '7', '8', '3', '5', '3', '6', '4', '6', '4'])
noncomputable def fragment14449800Acc01000 : List (String × SourceJson) := (fragment14449800Field009Key00, fragment14449800Field009Value00) :: fragment14449800Acc00900
noncomputable def fragment14449800Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '3', '5', '9', '2', '4', '9', '0', '4', '7', '8', '3', '5', '3', '6', '4', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment14449800_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 270) (SourceJson.white (fragment14449800Field009Chars00 ++ tail)) fragment14449800Acc00900 =
      .ok (.obj (fragment14449800Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14449800_object_field_009"
  err.flush

noncomputable def fragment14449800Chars : List Char := '{' :: (fragment14449800Field000Chars00 ++ fragment14449800Field001Chars00 ++ fragment14449800Field002Chars00 ++ fragment14449800Field003Chars00 ++ fragment14449800Field004Chars00 ++ fragment14449800Field005Chars00 ++ fragment14449800Field006Chars00 ++ fragment14449800Field007Chars00 ++ fragment14449800Field008Chars00 ++ fragment14449800Field009Chars00)
noncomputable def fragment14449800Value : SourceJson := .obj (fragment14449800Acc01000.reverse)

theorem value_fragment14449800 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 280) (fragment14449800Chars ++ tail) =
      .ok (fragment14449800Value, tail) := by
  have hinput : fragment14449800Chars ++ tail = '{' :: (fragment14449800Field000Chars00 ++ (fragment14449800Field001Chars00 ++ (fragment14449800Field002Chars00 ++ (fragment14449800Field003Chars00 ++ (fragment14449800Field004Chars00 ++ (fragment14449800Field005Chars00 ++ (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment14449800Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 280) (fragment14449800Chars ++ tail) =
        SourceJson.value (fuel + 280) ('{' :: (fragment14449800Field000Chars00 ++ (fragment14449800Field001Chars00 ++ (fragment14449800Field002Chars00 ++ (fragment14449800Field003Chars00 ++ (fragment14449800Field004Chars00 ++ (fragment14449800Field005Chars00 ++ (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 280)) hinput
    _ = SourceJson.object (fuel + 279) (SourceJson.white (fragment14449800Field000Chars00 ++ (fragment14449800Field001Chars00 ++ (fragment14449800Field002Chars00 ++ (fragment14449800Field003Chars00 ++ (fragment14449800Field004Chars00 ++ (fragment14449800Field005Chars00 ++ (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail)))))))))))) fragment14449800Acc00000 := by rfl
    _ = SourceJson.object (fuel + 278) (SourceJson.white (fragment14449800Field001Chars00 ++ (fragment14449800Field002Chars00 ++ (fragment14449800Field003Chars00 ++ (fragment14449800Field004Chars00 ++ (fragment14449800Field005Chars00 ++ (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail))))))))))) fragment14449800Acc00100 := object_fragment14449800_field_000 fuel (fragment14449800Field001Chars00 ++ (fragment14449800Field002Chars00 ++ (fragment14449800Field003Chars00 ++ (fragment14449800Field004Chars00 ++ (fragment14449800Field005Chars00 ++ (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 277) (SourceJson.white (fragment14449800Field002Chars00 ++ (fragment14449800Field003Chars00 ++ (fragment14449800Field004Chars00 ++ (fragment14449800Field005Chars00 ++ (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail)))))))))) fragment14449800Acc00200 := object_fragment14449800_field_001 fuel (fragment14449800Field002Chars00 ++ (fragment14449800Field003Chars00 ++ (fragment14449800Field004Chars00 ++ (fragment14449800Field005Chars00 ++ (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 276) (SourceJson.white (fragment14449800Field003Chars00 ++ (fragment14449800Field004Chars00 ++ (fragment14449800Field005Chars00 ++ (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail))))))))) fragment14449800Acc00300 := object_fragment14449800_field_002 fuel (fragment14449800Field003Chars00 ++ (fragment14449800Field004Chars00 ++ (fragment14449800Field005Chars00 ++ (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 275) (SourceJson.white (fragment14449800Field004Chars00 ++ (fragment14449800Field005Chars00 ++ (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail)))))))) fragment14449800Acc00400 := object_fragment14449800_field_003 fuel (fragment14449800Field004Chars00 ++ (fragment14449800Field005Chars00 ++ (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 274) (SourceJson.white (fragment14449800Field005Chars00 ++ (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail))))))) fragment14449800Acc00500 := object_fragment14449800_field_004 fuel (fragment14449800Field005Chars00 ++ (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 273) (SourceJson.white (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail)))))) fragment14449800Acc00600 := object_fragment14449800_field_005 fuel (fragment14449800Field006Chars00 ++ (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 272) (SourceJson.white (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail))))) fragment14449800Acc00700 := object_fragment14449800_field_006 fuel (fragment14449800Field007Chars00 ++ (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 271) (SourceJson.white (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail)))) fragment14449800Acc00800 := object_fragment14449800_field_007 fuel (fragment14449800Field008Chars00 ++ (fragment14449800Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 270) (SourceJson.white (fragment14449800Field009Chars00 ++ (tail))) fragment14449800Acc00900 := object_fragment14449800_field_008 fuel (fragment14449800Field009Chars00 ++ (tail))
    _ = .ok (fragment14449800Value, tail) := object_fragment14449800_field_009 fuel (tail)

noncomputable def fragment14451507Acc00000 : List (String × SourceJson) := []

noncomputable def fragment14451507Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment14451507Field000Value00 : SourceJson := .number (String.ofList ['6', '5', '9', '5'])
noncomputable def fragment14451507Acc00100 : List (String × SourceJson) := (fragment14451507Field000Key00, fragment14451507Field000Value00) :: fragment14451507Acc00000
noncomputable def fragment14451507Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '5', '9', '5', ',']

theorem object_fragment14451507_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 456) (SourceJson.white (fragment14451507Field000Chars00 ++ tail)) fragment14451507Acc00000 =
      SourceJson.object (fuel + 455) (SourceJson.white tail) fragment14451507Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14451507_object_field_000"
  err.flush

noncomputable def fragment14451507Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment14451507Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '7']), .number (String.ofList ['1', '3', '5']), .number (String.ofList ['1', '1', '7']), .number (String.ofList ['9', '8']), .number (String.ofList ['8', '4']), .number (String.ofList ['8', '3']), .number (String.ofList ['6', '5']), .number (String.ofList ['2', '7'])]
noncomputable def fragment14451507Acc00200 : List (String × SourceJson) := (fragment14451507Field001Key00, fragment14451507Field001Value00) :: fragment14451507Acc00100
noncomputable def fragment14451507Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14451507_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 455) (SourceJson.white (fragment14451507Field001Chars00 ++ tail)) fragment14451507Acc00100 =
      SourceJson.object (fuel + 454) (SourceJson.white tail) fragment14451507Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14451507_object_field_001"
  err.flush

noncomputable def fragment14451507Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment14451507Field002Value00 : SourceJson := .str (String.ofList ['2', '0', '9', '8', '1', '3', '3', '8', '1', '7', '6', '0', '9', '7', '1', '7', '2', '6', '1', '3', '3', '6', '7', '0', '2', '1', '7', '6', '3', '5', '7', '5', '1', '3', '4', '4', '4', '0', '0', '6', '7', '/', '1', '0', '6', '7', '5', '2', '5', '6', '2', '9', '5', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14451507Acc00300 : List (String × SourceJson) := (fragment14451507Field002Key00, fragment14451507Field002Value00) :: fragment14451507Acc00200
noncomputable def fragment14451507Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '0', '9', '8', '1', '3', '3', '8', '1', '7', '6', '0', '9', '7', '1', '7', '2', '6', '1', '3', '3', '6', '7', '0', '2', '1', '7', '6', '3', '5', '7', '5', '1', '3', '4', '4', '4', '0', '0', '6', '7', '/', '1', '0', '6', '7', '5', '2', '5', '6', '2', '9', '5', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14451507_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 454) (SourceJson.white (fragment14451507Field002Chars00 ++ tail)) fragment14451507Acc00200 =
      SourceJson.object (fuel + 453) (SourceJson.white tail) fragment14451507Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14451507_object_field_002"
  err.flush

noncomputable def fragment14451507Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment14451507Field003Value00 : SourceJson := .str (String.ofList ['2', '6', '8', '5', '3', '5', '2', '7', '/', '2', '5', '3', '9', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14451507Acc00400 : List (String × SourceJson) := (fragment14451507Field003Key00, fragment14451507Field003Value00) :: fragment14451507Acc00300
noncomputable def fragment14451507Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '6', '8', '5', '3', '5', '2', '7', '/', '2', '5', '3', '9', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14451507_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 453) (SourceJson.white (fragment14451507Field003Chars00 ++ tail)) fragment14451507Acc00300 =
      SourceJson.object (fuel + 452) (SourceJson.white tail) fragment14451507Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14451507_object_field_003"
  err.flush

noncomputable def fragment14451507Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment14451507Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '9', '3', '6', '9', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '3', '6', '9', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '8', '1', '2', '9', '/', '2', '2', '0', '8', '0', '0', '0']), .str (String.ofList ['5', '7', '1', '8', '6', '7', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '5', '6', '2', '4', '7', '/', '3', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '2', '1', '6', '9', '1', '/', '1', '8', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '1', '2', '1', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '1', '2', '1', '/', '9', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment14451507Acc00500 : List (String × SourceJson) := (fragment14451507Field004Key00, fragment14451507Field004Value00) :: fragment14451507Acc00400
noncomputable def fragment14451507Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '3', '6', '9', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '3', '6', '9', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '1', '2', '9', '/', '2', '2', '0', '8', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '1', '8', '6', '7', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '5', '6', '2', '4', '7', '/', '3', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '2', '1', '6', '9', '1', '/', '1', '8', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '2', '1', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '2', '1', '/', '9', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14451507_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 452) (SourceJson.white (fragment14451507Field004Chars00 ++ tail)) fragment14451507Acc00400 =
      SourceJson.object (fuel + 451) (SourceJson.white tail) fragment14451507Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14451507_object_field_004"
  err.flush

noncomputable def fragment14451507Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment14451507Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '7', '5', '8', '0', '8', '0', '9', '9', '0', '1', '8', '7', '0', '1', '9', '7', '5', '7', '0', '2', '9', '3', '9', '/', '4', '3', '1', '1', '7', '2', '2', '1', '3', '7', '0', '4', '0', '2', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '2', '1', '1', '8', '5', '4', '7', '7', '0', '3', '3', '1', '0', '9', '5', '4', '2', '0', '8', '5', '4', '9', '/', '4', '3', '1', '1', '7', '2', '2', '1', '3', '7', '0', '4', '0', '2', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '8', '7', '6', '8', '9', '5', '5', '5', '8', '0', '2', '8', '5', '2', '0', '1', '3', '6', '8', '9', '7', '/', '3', '4', '0', '3', '9', '9', '1', '1', '6', '0', '8', '2', '1', '2', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '0', '8', '9', '4', '4', '2', '1', '9', '6', '7', '0', '5', '5', '4', '8', '1', '9', '0', '9', '0', '3', '/', '2', '5', '8', '7', '0', '3', '3', '2', '8', '2', '2', '2', '4', '1', '7', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '0', '2', '2', '6', '6', '6', '0', '9', '3', '0', '1', '3', '6', '9', '2', '6', '8', '3', '9', '/', '4', '2', '5', '4', '9', '8', '8', '9', '5', '1', '0', '2', '6', '6', '0', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '4', '9', '6', '2', '9', '9', '5', '1', '8', '1', '2', '9', '7', '4', '9', '0', '9', '6', '1', '4', '7', '/', '3', '4', '0', '3', '9', '9', '1', '1', '6', '0', '8', '2', '1', '2', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '0', '4', '5', '7', '9', '9', '1', '3', '3', '8', '7', '8', '9', '4', '0', '0', '3', '3', '5', '5', '1', '/', '1', '0', '2', '1', '1', '9', '7', '3', '4', '8', '2', '4', '6', '3', '8', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '9', '9', '3', '7', '1', '2', '9', '4', '5', '0', '1', '9', '2', '6', '7', '3', '7', '4', '7', '3', '/', '1', '2', '7', '6', '4', '9', '6', '6', '8', '5', '3', '0', '7', '9', '8', '2', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '7', '2', '5', '2', '1', '4', '5', '6', '4', '5', '4', '9', '2', '4', '0', '5', '3', '7', '4', '5', '3', '1', '/', '1', '2', '9', '3', '5', '1', '6', '6', '4', '1', '1', '1', '2', '0', '8', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '0', '7', '6', '3', '3', '8', '2', '6', '6', '2', '0', '3', '2', '1', '3', '7', '0', '5', '4', '8', '3', '1', '/', '1', '2', '9', '3', '5', '1', '6', '6', '4', '1', '1', '1', '2', '0', '8', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment14451507Acc00600 : List (String × SourceJson) := (fragment14451507Field005Key00, fragment14451507Field005Value00) :: fragment14451507Acc00500
noncomputable def fragment14451507Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '8', '0', '8', '0', '9', '9', '0', '1', '8', '7', '0', '1', '9', '7', '5', '7', '0', '2', '9', '3', '9', '/', '4', '3', '1', '1', '7', '2', '2', '1', '3', '7', '0', '4', '0', '2', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '2', '1', '1', '8', '5', '4', '7', '7', '0', '3', '3', '1', '0', '9', '5', '4', '2', '0', '8', '5', '4', '9', '/', '4', '3', '1', '1', '7', '2', '2', '1', '3', '7', '0', '4', '0', '2', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '8', '7', '6', '8', '9', '5', '5', '5', '8', '0', '2', '8', '5', '2', '0', '1', '3', '6', '8', '9', '7', '/', '3', '4', '0', '3', '9', '9', '1', '1', '6', '0', '8', '2', '1', '2', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '0', '8', '9', '4', '4', '2', '1', '9', '6', '7', '0', '5', '5', '4', '8', '1', '9', '0', '9', '0', '3', '/', '2', '5', '8', '7', '0', '3', '3', '2', '8', '2', '2', '2', '4', '1', '7', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '0', '2', '2', '6', '6', '6', '0', '9', '3', '0', '1', '3', '6', '9', '2', '6', '8', '3', '9', '/', '4', '2', '5', '4', '9', '8', '8', '9', '5', '1', '0', '2', '6', '6', '0', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '4', '9', '6', '2', '9', '9', '5', '1', '8', '1', '2', '9', '7', '4', '9', '0', '9', '6', '1', '4', '7', '/', '3', '4', '0', '3', '9', '9', '1', '1', '6', '0', '8', '2', '1', '2', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '0', '4', '5', '7', '9', '9', '1', '3', '3', '8', '7', '8', '9', '4', '0', '0', '3', '3', '5', '5', '1', '/', '1', '0', '2', '1', '1', '9', '7', '3', '4', '8', '2', '4', '6', '3', '8', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '9', '9', '3', '7', '1', '2', '9', '4', '5', '0', '1', '9', '2', '6', '7', '3', '7', '4', '7', '3', '/', '1', '2', '7', '6', '4', '9', '6', '6', '8', '5', '3', '0', '7', '9', '8', '2', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '7', '2', '5', '2', '1', '4', '5', '6', '4', '5', '4', '9', '2', '4', '0', '5', '3', '7', '4', '5', '3', '1', '/', '1', '2', '9', '3', '5', '1', '6', '6', '4', '1', '1', '1', '2', '0', '8', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '0', '7', '6', '3', '3', '8', '2', '6', '6', '2', '0', '3', '2', '1', '3', '7', '0', '5', '4', '8', '3', '1', '/', '1', '2', '9', '3', '5', '1', '6', '6', '4', '1', '1', '1', '2', '0', '8', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14451507_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 451) (SourceJson.white (fragment14451507Field005Chars00 ++ tail)) fragment14451507Acc00500 =
      SourceJson.object (fuel + 450) (SourceJson.white tail) fragment14451507Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14451507_object_field_005"
  err.flush

noncomputable def fragment14451507Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14451507Field006Value00 : SourceJson := .str (String.ofList ['3', '3', '2', '6', '9', '5', '6', '0', '6', '6', '4', '8', '9', '8', '6', '0', '4', '4', '3', '7', '1', '9', '6', '4', '3', '9', '7', '9', '2', '5', '3', '9', '4', '4', '6', '7', '3', '5', '6', '5', '4', '7', '0', '8', '3', '9', '6', '4', '8', '0', '1', '4', '1', '/', '9', '2', '0', '5', '8', '5', '7', '2', '4', '4', '0', '2', '8', '3', '5', '2', '5', '0', '0', '6', '0', '4', '6', '9', '3', '4', '6', '7', '8', '0', '6', '0', '5', '4', '1', '8', '4', '5', '2', '1', '0', '7', '3', '2', '1', '4', '9', '2', '8', '9', '7', '5', '7', '5', '2', '3', '7', '8', '9', '4', '1', '7', '5', '6'])
noncomputable def fragment14451507Acc00700 : List (String × SourceJson) := (fragment14451507Field006Key00, fragment14451507Field006Value00) :: fragment14451507Acc00600
noncomputable def fragment14451507Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '3', '2', '6', '9', '5', '6', '0', '6', '6', '4', '8', '9', '8', '6', '0', '4', '4', '3', '7', '1', '9', '6', '4', '3', '9', '7', '9', '2', '5', '3', '9', '4', '4', '6', '7', '3', '5', '6', '5', '4', '7', '0', '8', '3', '9', '6', '4', '8', '0', '1', '4', '1', '/', '9', '2', '0', '5', '8', '5', '7', '2', '4', '4', '0', '2', '8', '3', '5', '2', '5', '0', '0', '6', '0', '4', '6', '9', '3', '4', '6', '7', '8', '0', '6', '0', '5', '4', '1', '8', '4', '5', '2', '1', '0', '7', '3', '2', '1', '4', '9', '2', '8', '9', '7', '5', '7', '5', '2', '3', '7', '8', '9', '4', '1', '7', '5', '6', '"', ',']

theorem object_fragment14451507_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 450) (SourceJson.white (fragment14451507Field006Chars00 ++ tail)) fragment14451507Acc00600 =
      SourceJson.object (fuel + 449) (SourceJson.white tail) fragment14451507Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14451507_object_field_006"
  err.flush

noncomputable def fragment14451507Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14451507Field007Value00 : SourceJson := .str (String.ofList ['4', '2', '9', '9', '0', '1', '4', '6', '2', '1', '3', '6', '7', '4', '6', '6', '0', '7', '3', '4', '7', '1', '6', '9', '3', '2', '4', '2', '7', '9', '6', '3', '8', '7', '8', '4', '4', '9', '6', '7', '5', '1', '4', '5', '1', '7', '4', '4', '7', '0', '5', '5', '9', '0', '9', '0', '8', '8', '6', '3', '1', '5', '9', '1', '9', '5', '7', '8', '1', '8', '4', '2', '1', '3', '5', '8', '5', '0', '1', '3', '5', '3', '9', '3', '5', '1', '2', '1', '8', '5', '9', '8', '5', '2', '5', '8', '0', '4', '4', '0', '6', '2', '0', '3', '2', '7', '4', '8', '1', '8', '0', '3', '2', '2', '0', '9', '9', '9', '9', '1', '8', '9', '1', '1', '9', '6', '6', '1', '0', '8', '0', '1', '6', '8', '6', '1', '8', '2', '9', '7', '6', '8', '8', '5', '9', '6', '8', '5', '8', '5', '9', '5', '4', '8', '1', '9', '1', '7', '7', '4', '4', '0', '8', '2', '2', '9', '0', '6', '5', '5', '5', '6', '5', '7', '2', '8', '5', '3', '4', '7', '3', '4', '9', '1', '2', '7', '5', '9', '8', '5', '9', '1', '2', '2', '7', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '0', '5', '1', '5', '7', '5', '4', '0', '1', '6', '0', '0', '4', '5', '5', '4', '6', '4', '4', '5', '6', '6', '6', '0', '2', '3', '8', '6', '0', '0', '2', '2', '3', '5', '9', '1', '4', '3', '0', '0', '3', '4', '0', '6', '4', '7', '0', '6', '5', '8', '4', '2', '1', '3', '6', '9', '7', '8', '3', '8', '8', '4', '5', '9', '8', '9', '0', '0', '7', '9', '7', '9', '2', '3', '8', '5', '6', '4', '8', '2', '8', '4', '6', '5', '0', '4', '4', '6', '5', '1', '4', '3', '3', '1', '1', '5', '7', '6', '4', '6', '5', '3', '7', '3', '0', '0', '8', '3', '0', '9', '3', '4', '4', '6', '7', '3', '2', '0', '5', '7', '9', '4', '6', '9', '6', '4', '3', '7', '3', '3', '7', '9', '9', '1', '3', '0', '4', '8', '3', '0', '8', '8', '9', '6', '9', '6', '8', '4', '7', '0', '9', '1', '1', '7', '5', '6', '0', '0', '3', '1', '8', '8', '4', '0', '8', '7', '4', '6', '1', '8', '0', '2', '9', '1', '8', '7', '9', '7', '7', '8', '2', '8', '4', '4', '6', '3', '9', '2', '2', '5', '2', '1', '6', '6', '2', '7', '9', '3', '5', '4', '0', '0', '2', '4', '9', '1', '9', '0', '0', '5', '2', '6', '7', '5', '2', '0', '3', '4', '4', '0', '9', '9', '4', '3', '9', '9'])
noncomputable def fragment14451507Acc00800 : List (String × SourceJson) := (fragment14451507Field007Key00, fragment14451507Field007Value00) :: fragment14451507Acc00700
noncomputable def fragment14451507Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '2', '9', '9', '0', '1', '4', '6', '2', '1', '3', '6', '7', '4', '6', '6', '0', '7', '3', '4', '7', '1', '6', '9', '3', '2', '4', '2', '7', '9', '6', '3', '8', '7', '8', '4', '4', '9', '6', '7', '5', '1', '4', '5', '1', '7', '4', '4', '7', '0', '5', '5', '9', '0', '9', '0', '8', '8', '6', '3', '1', '5', '9', '1', '9', '5', '7', '8', '1', '8', '4', '2', '1', '3', '5', '8', '5', '0', '1', '3', '5', '3', '9', '3', '5', '1', '2', '1', '8', '5', '9', '8', '5', '2', '5', '8', '0', '4', '4', '0', '6', '2', '0', '3', '2', '7', '4', '8', '1', '8', '0', '3', '2', '2', '0', '9', '9', '9', '9', '1', '8', '9', '1', '1', '9', '6', '6', '1', '0', '8', '0', '1', '6', '8', '6', '1', '8', '2', '9', '7', '6', '8', '8', '5', '9', '6', '8', '5', '8', '5', '9', '5', '4', '8', '1', '9', '1', '7', '7', '4', '4', '0', '8', '2', '2', '9', '0', '6', '5', '5', '5', '6', '5', '7', '2', '8', '5', '3', '4', '7', '3', '4', '9', '1', '2', '7', '5', '9', '8', '5', '9', '1', '2', '2', '7', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '0', '5', '1', '5', '7', '5', '4', '0', '1', '6', '0', '0', '4', '5', '5', '4', '6', '4', '4', '5', '6', '6', '6', '0', '2', '3', '8', '6', '0', '0', '2', '2', '3', '5', '9', '1', '4', '3', '0', '0', '3', '4', '0', '6', '4', '7', '0', '6', '5', '8', '4', '2', '1', '3', '6', '9', '7', '8', '3', '8', '8', '4', '5', '9', '8', '9', '0', '0', '7', '9', '7', '9', '2', '3', '8', '5', '6', '4', '8', '2', '8', '4', '6', '5', '0', '4', '4', '6', '5', '1', '4', '3', '3', '1', '1', '5', '7', '6', '4', '6', '5', '3', '7', '3', '0', '0', '8', '3', '0', '9', '3', '4', '4', '6', '7', '3', '2', '0', '5', '7', '9', '4', '6', '9', '6', '4', '3', '7', '3', '3', '7', '9', '9', '1', '3', '0', '4', '8', '3', '0', '8', '8', '9', '6', '9', '6', '8', '4', '7', '0', '9', '1', '1', '7', '5', '6', '0', '0', '3', '1', '8', '8', '4', '0', '8', '7', '4', '6', '1', '8', '0', '2', '9', '1', '8', '7', '9', '7', '7', '8', '2', '8', '4', '4', '6', '3', '9', '2', '2', '5', '2', '1', '6', '6', '2', '7', '9', '3', '5', '4', '0', '0', '2', '4', '9', '1', '9', '0', '0', '5', '2', '6', '7', '5', '2', '0', '3', '4', '4', '0', '9', '9', '4', '3', '9', '9', '"', ',']

theorem object_fragment14451507_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 449) (SourceJson.white (fragment14451507Field007Chars00 ++ tail)) fragment14451507Acc00700 =
      SourceJson.object (fuel + 448) (SourceJson.white tail) fragment14451507Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14451507_object_field_007"
  err.flush

noncomputable def fragment14451507Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14451507Field008Value00 : SourceJson := .str (String.ofList ['2', '8', '6', '3', '2', '7', '0', '7', '2', '9', '9', '9', '8', '1', '2', '9', '4', '7'])
noncomputable def fragment14451507Acc00900 : List (String × SourceJson) := (fragment14451507Field008Key00, fragment14451507Field008Value00) :: fragment14451507Acc00800
noncomputable def fragment14451507Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '8', '6', '3', '2', '7', '0', '7', '2', '9', '9', '9', '8', '1', '2', '9', '4', '7', '"', ',']

theorem object_fragment14451507_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 448) (SourceJson.white (fragment14451507Field008Chars00 ++ tail)) fragment14451507Acc00800 =
      SourceJson.object (fuel + 447) (SourceJson.white tail) fragment14451507Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14451507_object_field_008"
  err.flush

noncomputable def fragment14451507Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14451507Field009Value00 : SourceJson := .str (String.ofList ['1', '6', '9', '8', '6', '3', '4', '7', '5', '6', '8', '7', '6', '5', '8', '0', '7', '6', '6'])
noncomputable def fragment14451507Acc01000 : List (String × SourceJson) := (fragment14451507Field009Key00, fragment14451507Field009Value00) :: fragment14451507Acc00900
noncomputable def fragment14451507Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '9', '8', '6', '3', '4', '7', '5', '6', '8', '7', '6', '5', '8', '0', '7', '6', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment14451507_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 447) (SourceJson.white (fragment14451507Field009Chars00 ++ tail)) fragment14451507Acc00900 =
      .ok (.obj (fragment14451507Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14451507_object_field_009"
  err.flush

noncomputable def fragment14451507Chars : List Char := '{' :: (fragment14451507Field000Chars00 ++ fragment14451507Field001Chars00 ++ fragment14451507Field002Chars00 ++ fragment14451507Field003Chars00 ++ fragment14451507Field004Chars00 ++ fragment14451507Field005Chars00 ++ fragment14451507Field006Chars00 ++ fragment14451507Field007Chars00 ++ fragment14451507Field008Chars00 ++ fragment14451507Field009Chars00)
noncomputable def fragment14451507Value : SourceJson := .obj (fragment14451507Acc01000.reverse)

theorem value_fragment14451507 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 457) (fragment14451507Chars ++ tail) =
      .ok (fragment14451507Value, tail) := by
  have hinput : fragment14451507Chars ++ tail = '{' :: (fragment14451507Field000Chars00 ++ (fragment14451507Field001Chars00 ++ (fragment14451507Field002Chars00 ++ (fragment14451507Field003Chars00 ++ (fragment14451507Field004Chars00 ++ (fragment14451507Field005Chars00 ++ (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment14451507Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 457) (fragment14451507Chars ++ tail) =
        SourceJson.value (fuel + 457) ('{' :: (fragment14451507Field000Chars00 ++ (fragment14451507Field001Chars00 ++ (fragment14451507Field002Chars00 ++ (fragment14451507Field003Chars00 ++ (fragment14451507Field004Chars00 ++ (fragment14451507Field005Chars00 ++ (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 457)) hinput
    _ = SourceJson.object (fuel + 456) (SourceJson.white (fragment14451507Field000Chars00 ++ (fragment14451507Field001Chars00 ++ (fragment14451507Field002Chars00 ++ (fragment14451507Field003Chars00 ++ (fragment14451507Field004Chars00 ++ (fragment14451507Field005Chars00 ++ (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail)))))))))))) fragment14451507Acc00000 := by rfl
    _ = SourceJson.object (fuel + 455) (SourceJson.white (fragment14451507Field001Chars00 ++ (fragment14451507Field002Chars00 ++ (fragment14451507Field003Chars00 ++ (fragment14451507Field004Chars00 ++ (fragment14451507Field005Chars00 ++ (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail))))))))))) fragment14451507Acc00100 := object_fragment14451507_field_000 fuel (fragment14451507Field001Chars00 ++ (fragment14451507Field002Chars00 ++ (fragment14451507Field003Chars00 ++ (fragment14451507Field004Chars00 ++ (fragment14451507Field005Chars00 ++ (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 454) (SourceJson.white (fragment14451507Field002Chars00 ++ (fragment14451507Field003Chars00 ++ (fragment14451507Field004Chars00 ++ (fragment14451507Field005Chars00 ++ (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail)))))))))) fragment14451507Acc00200 := object_fragment14451507_field_001 fuel (fragment14451507Field002Chars00 ++ (fragment14451507Field003Chars00 ++ (fragment14451507Field004Chars00 ++ (fragment14451507Field005Chars00 ++ (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 453) (SourceJson.white (fragment14451507Field003Chars00 ++ (fragment14451507Field004Chars00 ++ (fragment14451507Field005Chars00 ++ (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail))))))))) fragment14451507Acc00300 := object_fragment14451507_field_002 fuel (fragment14451507Field003Chars00 ++ (fragment14451507Field004Chars00 ++ (fragment14451507Field005Chars00 ++ (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 452) (SourceJson.white (fragment14451507Field004Chars00 ++ (fragment14451507Field005Chars00 ++ (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail)))))))) fragment14451507Acc00400 := object_fragment14451507_field_003 fuel (fragment14451507Field004Chars00 ++ (fragment14451507Field005Chars00 ++ (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 451) (SourceJson.white (fragment14451507Field005Chars00 ++ (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail))))))) fragment14451507Acc00500 := object_fragment14451507_field_004 fuel (fragment14451507Field005Chars00 ++ (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 450) (SourceJson.white (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail)))))) fragment14451507Acc00600 := object_fragment14451507_field_005 fuel (fragment14451507Field006Chars00 ++ (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 449) (SourceJson.white (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail))))) fragment14451507Acc00700 := object_fragment14451507_field_006 fuel (fragment14451507Field007Chars00 ++ (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 448) (SourceJson.white (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail)))) fragment14451507Acc00800 := object_fragment14451507_field_007 fuel (fragment14451507Field008Chars00 ++ (fragment14451507Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 447) (SourceJson.white (fragment14451507Field009Chars00 ++ (tail))) fragment14451507Acc00900 := object_fragment14451507_field_008 fuel (fragment14451507Field009Chars00 ++ (tail))
    _ = .ok (fragment14451507Value, tail) := object_fragment14451507_field_009 fuel (tail)

noncomputable def fragment14453560Acc00000 : List (String × SourceJson) := []

noncomputable def fragment14453560Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment14453560Field000Value00 : SourceJson := .number (String.ofList ['6', '5', '9', '6'])
noncomputable def fragment14453560Acc00100 : List (String × SourceJson) := (fragment14453560Field000Key00, fragment14453560Field000Value00) :: fragment14453560Acc00000
noncomputable def fragment14453560Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '5', '9', '6', ',']

theorem object_fragment14453560_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 311) (SourceJson.white (fragment14453560Field000Chars00 ++ tail)) fragment14453560Acc00000 =
      SourceJson.object (fuel + 310) (SourceJson.white tail) fragment14453560Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14453560_object_field_000"
  err.flush

noncomputable def fragment14453560Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment14453560Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '7']), .number (String.ofList ['1', '3', '5']), .number (String.ofList ['1', '1', '7']), .number (String.ofList ['9', '8']), .number (String.ofList ['8', '4']), .number (String.ofList ['6', '6']), .number (String.ofList ['5', '6']), .number (String.ofList ['2', '7'])]
noncomputable def fragment14453560Acc00200 : List (String × SourceJson) := (fragment14453560Field001Key00, fragment14453560Field001Value00) :: fragment14453560Acc00100
noncomputable def fragment14453560Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14453560_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 310) (SourceJson.white (fragment14453560Field001Chars00 ++ tail)) fragment14453560Acc00100 =
      SourceJson.object (fuel + 309) (SourceJson.white tail) fragment14453560Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14453560_object_field_001"
  err.flush

noncomputable def fragment14453560Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment14453560Field002Value00 : SourceJson := .str (String.ofList ['1', '9', '3', '1', '7', '4', '2', '1', '2', '7', '0', '5', '0', '9', '5', '0', '2', '9', '9', '3', '9', '1', '1', '8', '5', '7', '0', '1', '5', '9', '9', '4', '6', '3', '4', '0', '5', '0', '6', '8', '9', '1', '9', '3', '9', '/', '1', '6', '6', '7', '8', '0', '4', '7', '1', '0', '3', '7', '7', '8', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14453560Acc00300 : List (String × SourceJson) := (fragment14453560Field002Key00, fragment14453560Field002Value00) :: fragment14453560Acc00200
noncomputable def fragment14453560Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '9', '3', '1', '7', '4', '2', '1', '2', '7', '0', '5', '0', '9', '5', '0', '2', '9', '9', '3', '9', '1', '1', '8', '5', '7', '0', '1', '5', '9', '9', '4', '6', '3', '4', '0', '5', '0', '6', '8', '9', '1', '9', '3', '9', '/', '1', '6', '6', '7', '8', '0', '4', '7', '1', '0', '3', '7', '7', '8', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14453560_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 309) (SourceJson.white (fragment14453560Field002Chars00 ++ tail)) fragment14453560Acc00200 =
      SourceJson.object (fuel + 308) (SourceJson.white tail) fragment14453560Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14453560_object_field_002"
  err.flush

noncomputable def fragment14453560Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment14453560Field003Value00 : SourceJson := .str (String.ofList ['2', '0', '1', '5', '2', '6', '9', '/', '2', '9', '8', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14453560Acc00400 : List (String × SourceJson) := (fragment14453560Field003Key00, fragment14453560Field003Value00) :: fragment14453560Acc00300
noncomputable def fragment14453560Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '0', '1', '5', '2', '6', '9', '/', '2', '9', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14453560_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 308) (SourceJson.white (fragment14453560Field003Chars00 ++ tail)) fragment14453560Acc00300 =
      SourceJson.object (fuel + 307) (SourceJson.white tail) fragment14453560Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14453560_object_field_003"
  err.flush

noncomputable def fragment14453560Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment14453560Field004Value00 : SourceJson := .arr [.str (String.ofList ['4', '4', '9', '2', '0', '1', '/', '8', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '9', '2', '0', '1', '/', '8', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '8', '1', '2', '9', '/', '2', '2', '0', '8', '0', '0', '0']), .str (String.ofList ['3', '1', '3', '5', '8', '7', '7', '9', '/', '3', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '5', '6', '2', '4', '7', '/', '3', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '2', '1', '6', '9', '1', '/', '1', '8', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '6', '2', '4', '9', '/', '4', '3', '7', '5', '0', '0', '0']), .str (String.ofList ['1', '5', '6', '2', '4', '9', '/', '4', '3', '7', '5', '0', '0', '0'])]
noncomputable def fragment14453560Acc00500 : List (String × SourceJson) := (fragment14453560Field004Key00, fragment14453560Field004Value00) :: fragment14453560Acc00400
noncomputable def fragment14453560Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '9', '2', '0', '1', '/', '8', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '9', '2', '0', '1', '/', '8', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '1', '2', '9', '/', '2', '2', '0', '8', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '3', '5', '8', '7', '7', '9', '/', '3', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '5', '6', '2', '4', '7', '/', '3', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '2', '1', '6', '9', '1', '/', '1', '8', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '2', '4', '9', '/', '4', '3', '7', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '2', '4', '9', '/', '4', '3', '7', '5', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14453560_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 307) (SourceJson.white (fragment14453560Field004Chars00 ++ tail)) fragment14453560Acc00400 =
      SourceJson.object (fuel + 306) (SourceJson.white tail) fragment14453560Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14453560_object_field_004"
  err.flush

noncomputable def fragment14453560Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment14453560Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '7', '8', '8', '2', '0', '2', '2', '5', '9', '4', '2', '3', '0', '5', '6', '3', '/', '4', '6', '9', '1', '0', '0', '0', '9', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '4', '5', '1', '5', '1', '8', '3', '0', '7', '3', '5', '3', '5', '4', '3', '/', '4', '6', '9', '1', '0', '0', '0', '9', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '2', '3', '2', '0', '3', '9', '0', '6', '5', '1', '5', '4', '5', '9', '/', '3', '7', '0', '3', '4', '2', '1', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '9', '6', '4', '1', '6', '1', '0', '3', '3', '3', '5', '6', '9', '/', '3', '7', '5', '2', '8', '0', '0', '7', '7', '7', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '7', '4', '5', '1', '8', '4', '9', '8', '9', '5', '5', '8', '3', '/', '3', '7', '0', '3', '4', '2', '1', '8', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '8', '2', '6', '0', '6', '2', '0', '2', '3', '7', '3', '6', '8', '9', '/', '3', '7', '0', '3', '4', '2', '1', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '2', '4', '8', '0', '4', '4', '3', '2', '9', '9', '6', '5', '9', '/', '3', '7', '0', '3', '4', '2', '1', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '5', '4', '7', '8', '1', '0', '9', '8', '8', '7', '8', '7', '3', '/', '1', '8', '5', '1', '7', '1', '0', '9', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '4', '2', '9', '8', '5', '2', '4', '6', '4', '3', '1', '9', '0', '4', '7', '/', '1', '4', '0', '7', '3', '0', '0', '2', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '6', '3', '5', '9', '3', '3', '4', '5', '1', '8', '2', '0', '1', '4', '7', '/', '1', '4', '0', '7', '3', '0', '0', '2', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment14453560Acc00600 : List (String × SourceJson) := (fragment14453560Field005Key00, fragment14453560Field005Value00) :: fragment14453560Acc00500
noncomputable def fragment14453560Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '8', '2', '0', '2', '2', '5', '9', '4', '2', '3', '0', '5', '6', '3', '/', '4', '6', '9', '1', '0', '0', '0', '9', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '4', '5', '1', '5', '1', '8', '3', '0', '7', '3', '5', '3', '5', '4', '3', '/', '4', '6', '9', '1', '0', '0', '0', '9', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '2', '3', '2', '0', '3', '9', '0', '6', '5', '1', '5', '4', '5', '9', '/', '3', '7', '0', '3', '4', '2', '1', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '9', '6', '4', '1', '6', '1', '0', '3', '3', '3', '5', '6', '9', '/', '3', '7', '5', '2', '8', '0', '0', '7', '7', '7', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '7', '4', '5', '1', '8', '4', '9', '8', '9', '5', '5', '8', '3', '/', '3', '7', '0', '3', '4', '2', '1', '8', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '8', '2', '6', '0', '6', '2', '0', '2', '3', '7', '3', '6', '8', '9', '/', '3', '7', '0', '3', '4', '2', '1', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '2', '4', '8', '0', '4', '4', '3', '2', '9', '9', '6', '5', '9', '/', '3', '7', '0', '3', '4', '2', '1', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '5', '4', '7', '8', '1', '0', '9', '8', '8', '7', '8', '7', '3', '/', '1', '8', '5', '1', '7', '1', '0', '9', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '4', '2', '9', '8', '5', '2', '4', '6', '4', '3', '1', '9', '0', '4', '7', '/', '1', '4', '0', '7', '3', '0', '0', '2', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '6', '3', '5', '9', '3', '3', '4', '5', '1', '8', '2', '0', '1', '4', '7', '/', '1', '4', '0', '7', '3', '0', '0', '2', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14453560_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 306) (SourceJson.white (fragment14453560Field005Chars00 ++ tail)) fragment14453560Acc00500 =
      SourceJson.object (fuel + 305) (SourceJson.white tail) fragment14453560Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14453560_object_field_005"
  err.flush

noncomputable def fragment14453560Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14453560Field006Value00 : SourceJson := .str (String.ofList ['1', '3', '9', '0', '9', '2', '9', '3', '2', '1', '3', '0', '3', '6', '1', '0', '0', '5', '6', '9', '8', '3', '3', '2', '8', '0', '9', '1', '9', '4', '0', '7', '1', '9', '3', '8', '8', '3', '1', '9', '1', '1', '8', '5', '2', '6', '8', '6', '1', '3', '6', '1', '5', '9', '3', '7', '5', '/', '9', '1', '8', '9', '8', '4', '9', '0', '2', '2', '9', '8', '6', '1', '0', '2', '5', '2', '5', '0', '0', '8', '1', '8', '9', '0', '9', '4', '6', '1', '8', '7', '3', '1', '5', '5', '6', '2', '7', '0', '5', '5', '2', '9', '3', '8', '2', '9', '2', '7', '2', '2', '1', '9', '0', '9', '8', '1', '8', '3', '1', '7', '4', '5', '5', '3', '6'])
noncomputable def fragment14453560Acc00700 : List (String × SourceJson) := (fragment14453560Field006Key00, fragment14453560Field006Value00) :: fragment14453560Acc00600
noncomputable def fragment14453560Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '9', '0', '9', '2', '9', '3', '2', '1', '3', '0', '3', '6', '1', '0', '0', '5', '6', '9', '8', '3', '3', '2', '8', '0', '9', '1', '9', '4', '0', '7', '1', '9', '3', '8', '8', '3', '1', '9', '1', '1', '8', '5', '2', '6', '8', '6', '1', '3', '6', '1', '5', '9', '3', '7', '5', '/', '9', '1', '8', '9', '8', '4', '9', '0', '2', '2', '9', '8', '6', '1', '0', '2', '5', '2', '5', '0', '0', '8', '1', '8', '9', '0', '9', '4', '6', '1', '8', '7', '3', '1', '5', '5', '6', '2', '7', '0', '5', '5', '2', '9', '3', '8', '2', '9', '2', '7', '2', '2', '1', '9', '0', '9', '8', '1', '8', '3', '1', '7', '4', '5', '5', '3', '6', '"', ',']

theorem object_fragment14453560_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 305) (SourceJson.white (fragment14453560Field006Chars00 ++ tail)) fragment14453560Acc00600 =
      SourceJson.object (fuel + 304) (SourceJson.white tail) fragment14453560Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14453560_object_field_006"
  err.flush

noncomputable def fragment14453560Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14453560Field007Value00 : SourceJson := .str (String.ofList ['3', '1', '2', '3', '1', '1', '1', '8', '8', '0', '1', '8', '6', '3', '6', '4', '4', '4', '8', '2', '7', '1', '0', '7', '3', '9', '5', '5', '1', '0', '1', '6', '7', '9', '1', '7', '6', '3', '5', '3', '8', '6', '4', '4', '0', '0', '6', '8', '6', '1', '0', '9', '7', '8', '0', '7', '2', '8', '5', '1', '2', '1', '5', '2', '1', '9', '1', '4', '4', '9', '3', '8', '3', '1', '1', '0', '9', '9', '2', '8', '8', '5', '4', '0', '8', '0', '8', '1', '6', '5', '1', '6', '2', '3', '2', '5', '1', '0', '7', '9', '0', '3', '1', '9', '1', '4', '2', '3', '7', '2', '2', '9', '4', '3', '4', '8', '3', '2', '6', '1', '5', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '2', '6', '4', '8', '5', '8', '0', '5', '0', '8', '4', '7', '5', '6', '2', '9', '4', '0', '5', '2', '7', '7', '9', '2', '8', '6', '4', '7', '6', '7', '5', '2', '5', '7', '3', '3', '0', '6', '7', '3', '9', '4', '7', '5', '2', '3', '7', '6', '6', '5', '2', '1', '9', '8', '6', '9', '6', '9', '7', '0', '4', '8', '9', '4', '8', '4', '8', '8', '5', '7', '7', '3', '2', '1', '8', '8', '3', '2', '5', '3', '0', '1', '8', '4', '0', '6', '8', '9', '4', '9', '4', '9', '2', '9', '4', '6', '7', '4', '3', '6', '7', '0', '4', '3', '8', '8', '7', '8', '1', '5', '6', '1', '0', '8', '3', '0', '5', '7', '6', '5', '4', '4', '8', '9', '6', '4', '8', '0', '2', '6', '5', '5', '9', '4', '6', '7', '9', '6', '3', '6', '0', '2', '9', '2', '3', '3', '3', '6', '0', '8', '9', '6', '8', '7'])
noncomputable def fragment14453560Acc00800 : List (String × SourceJson) := (fragment14453560Field007Key00, fragment14453560Field007Value00) :: fragment14453560Acc00700
noncomputable def fragment14453560Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '1', '2', '3', '1', '1', '1', '8', '8', '0', '1', '8', '6', '3', '6', '4', '4', '4', '8', '2', '7', '1', '0', '7', '3', '9', '5', '5', '1', '0', '1', '6', '7', '9', '1', '7', '6', '3', '5', '3', '8', '6', '4', '4', '0', '0', '6', '8', '6', '1', '0', '9', '7', '8', '0', '7', '2', '8', '5', '1', '2', '1', '5', '2', '1', '9', '1', '4', '4', '9', '3', '8', '3', '1', '1', '0', '9', '9', '2', '8', '8', '5', '4', '0', '8', '0', '8', '1', '6', '5', '1', '6', '2', '3', '2', '5', '1', '0', '7', '9', '0', '3', '1', '9', '1', '4', '2', '3', '7', '2', '2', '9', '4', '3', '4', '8', '3', '2', '6', '1', '5', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '2', '6', '4', '8', '5', '8', '0', '5', '0', '8', '4', '7', '5', '6', '2', '9', '4', '0', '5', '2', '7', '7', '9', '2', '8', '6', '4', '7', '6', '7', '5', '2', '5', '7', '3', '3', '0', '6', '7', '3', '9', '4', '7', '5', '2', '3', '7', '6', '6', '5', '2', '1', '9', '8', '6', '9', '6', '9', '7', '0', '4', '8', '9', '4', '8', '4', '8', '8', '5', '7', '7', '3', '2', '1', '8', '8', '3', '2', '5', '3', '0', '1', '8', '4', '0', '6', '8', '9', '4', '9', '4', '9', '2', '9', '4', '6', '7', '4', '3', '6', '7', '0', '4', '3', '8', '8', '7', '8', '1', '5', '6', '1', '0', '8', '3', '0', '5', '7', '6', '5', '4', '4', '8', '9', '6', '4', '8', '0', '2', '6', '5', '5', '9', '4', '6', '7', '9', '6', '3', '6', '0', '2', '9', '2', '3', '3', '3', '6', '0', '8', '9', '6', '8', '7', '"', ',']

theorem object_fragment14453560_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 304) (SourceJson.white (fragment14453560Field007Chars00 ++ tail)) fragment14453560Acc00700 =
      SourceJson.object (fuel + 303) (SourceJson.white tail) fragment14453560Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14453560_object_field_007"
  err.flush

noncomputable def fragment14453560Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14453560Field008Value00 : SourceJson := .str (String.ofList ['1', '1', '9', '9', '1', '5', '7', '6', '1', '4', '4', '3', '3', '6', '8', '8', '9', '1', '2'])
noncomputable def fragment14453560Acc00900 : List (String × SourceJson) := (fragment14453560Field008Key00, fragment14453560Field008Value00) :: fragment14453560Acc00800
noncomputable def fragment14453560Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '9', '9', '1', '5', '7', '6', '1', '4', '4', '3', '3', '6', '8', '8', '9', '1', '2', '"', ',']

theorem object_fragment14453560_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 303) (SourceJson.white (fragment14453560Field008Chars00 ++ tail)) fragment14453560Acc00800 =
      SourceJson.object (fuel + 302) (SourceJson.white tail) fragment14453560Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14453560_object_field_008"
  err.flush

noncomputable def fragment14453560Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14453560Field009Value00 : SourceJson := .str (String.ofList ['7', '5', '7', '8', '8', '4', '1', '4', '6', '0', '7', '9', '1', '8', '2', '4', '7', '3', '0'])
noncomputable def fragment14453560Acc01000 : List (String × SourceJson) := (fragment14453560Field009Key00, fragment14453560Field009Value00) :: fragment14453560Acc00900
noncomputable def fragment14453560Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '5', '7', '8', '8', '4', '1', '4', '6', '0', '7', '9', '1', '8', '2', '4', '7', '3', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment14453560_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 302) (SourceJson.white (fragment14453560Field009Chars00 ++ tail)) fragment14453560Acc00900 =
      .ok (.obj (fragment14453560Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14453560_object_field_009"
  err.flush

noncomputable def fragment14453560Chars : List Char := '{' :: (fragment14453560Field000Chars00 ++ fragment14453560Field001Chars00 ++ fragment14453560Field002Chars00 ++ fragment14453560Field003Chars00 ++ fragment14453560Field004Chars00 ++ fragment14453560Field005Chars00 ++ fragment14453560Field006Chars00 ++ fragment14453560Field007Chars00 ++ fragment14453560Field008Chars00 ++ fragment14453560Field009Chars00)
noncomputable def fragment14453560Value : SourceJson := .obj (fragment14453560Acc01000.reverse)

theorem value_fragment14453560 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 312) (fragment14453560Chars ++ tail) =
      .ok (fragment14453560Value, tail) := by
  have hinput : fragment14453560Chars ++ tail = '{' :: (fragment14453560Field000Chars00 ++ (fragment14453560Field001Chars00 ++ (fragment14453560Field002Chars00 ++ (fragment14453560Field003Chars00 ++ (fragment14453560Field004Chars00 ++ (fragment14453560Field005Chars00 ++ (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment14453560Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 312) (fragment14453560Chars ++ tail) =
        SourceJson.value (fuel + 312) ('{' :: (fragment14453560Field000Chars00 ++ (fragment14453560Field001Chars00 ++ (fragment14453560Field002Chars00 ++ (fragment14453560Field003Chars00 ++ (fragment14453560Field004Chars00 ++ (fragment14453560Field005Chars00 ++ (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 312)) hinput
    _ = SourceJson.object (fuel + 311) (SourceJson.white (fragment14453560Field000Chars00 ++ (fragment14453560Field001Chars00 ++ (fragment14453560Field002Chars00 ++ (fragment14453560Field003Chars00 ++ (fragment14453560Field004Chars00 ++ (fragment14453560Field005Chars00 ++ (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail)))))))))))) fragment14453560Acc00000 := by rfl
    _ = SourceJson.object (fuel + 310) (SourceJson.white (fragment14453560Field001Chars00 ++ (fragment14453560Field002Chars00 ++ (fragment14453560Field003Chars00 ++ (fragment14453560Field004Chars00 ++ (fragment14453560Field005Chars00 ++ (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail))))))))))) fragment14453560Acc00100 := object_fragment14453560_field_000 fuel (fragment14453560Field001Chars00 ++ (fragment14453560Field002Chars00 ++ (fragment14453560Field003Chars00 ++ (fragment14453560Field004Chars00 ++ (fragment14453560Field005Chars00 ++ (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 309) (SourceJson.white (fragment14453560Field002Chars00 ++ (fragment14453560Field003Chars00 ++ (fragment14453560Field004Chars00 ++ (fragment14453560Field005Chars00 ++ (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail)))))))))) fragment14453560Acc00200 := object_fragment14453560_field_001 fuel (fragment14453560Field002Chars00 ++ (fragment14453560Field003Chars00 ++ (fragment14453560Field004Chars00 ++ (fragment14453560Field005Chars00 ++ (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 308) (SourceJson.white (fragment14453560Field003Chars00 ++ (fragment14453560Field004Chars00 ++ (fragment14453560Field005Chars00 ++ (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail))))))))) fragment14453560Acc00300 := object_fragment14453560_field_002 fuel (fragment14453560Field003Chars00 ++ (fragment14453560Field004Chars00 ++ (fragment14453560Field005Chars00 ++ (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 307) (SourceJson.white (fragment14453560Field004Chars00 ++ (fragment14453560Field005Chars00 ++ (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail)))))))) fragment14453560Acc00400 := object_fragment14453560_field_003 fuel (fragment14453560Field004Chars00 ++ (fragment14453560Field005Chars00 ++ (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 306) (SourceJson.white (fragment14453560Field005Chars00 ++ (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail))))))) fragment14453560Acc00500 := object_fragment14453560_field_004 fuel (fragment14453560Field005Chars00 ++ (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 305) (SourceJson.white (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail)))))) fragment14453560Acc00600 := object_fragment14453560_field_005 fuel (fragment14453560Field006Chars00 ++ (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 304) (SourceJson.white (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail))))) fragment14453560Acc00700 := object_fragment14453560_field_006 fuel (fragment14453560Field007Chars00 ++ (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 303) (SourceJson.white (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail)))) fragment14453560Acc00800 := object_fragment14453560_field_007 fuel (fragment14453560Field008Chars00 ++ (fragment14453560Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 302) (SourceJson.white (fragment14453560Field009Chars00 ++ (tail))) fragment14453560Acc00900 := object_fragment14453560_field_008 fuel (fragment14453560Field009Chars00 ++ (tail))
    _ = .ok (fragment14453560Value, tail) := object_fragment14453560_field_009 fuel (tail)

noncomputable def fragment14455343Acc00000 : List (String × SourceJson) := []

noncomputable def fragment14455343Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment14455343Field000Value00 : SourceJson := .number (String.ofList ['6', '5', '9', '7'])
noncomputable def fragment14455343Acc00100 : List (String × SourceJson) := (fragment14455343Field000Key00, fragment14455343Field000Value00) :: fragment14455343Acc00000
noncomputable def fragment14455343Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '5', '9', '7', ',']

theorem object_fragment14455343_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment14455343Field000Chars00 ++ tail)) fragment14455343Acc00000 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment14455343Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14455343_object_field_000"
  err.flush

noncomputable def fragment14455343Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment14455343Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '7']), .number (String.ofList ['1', '3', '5']), .number (String.ofList ['1', '1', '7']), .number (String.ofList ['9', '8']), .number (String.ofList ['9', '4']), .number (String.ofList ['8', '4']), .number (String.ofList ['8', '3']), .number (String.ofList ['6', '5'])]
noncomputable def fragment14455343Acc00200 : List (String × SourceJson) := (fragment14455343Field001Key00, fragment14455343Field001Value00) :: fragment14455343Acc00100
noncomputable def fragment14455343Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14455343_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment14455343Field001Chars00 ++ tail)) fragment14455343Acc00100 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment14455343Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14455343_object_field_001"
  err.flush

noncomputable def fragment14455343Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment14455343Field002Value00 : SourceJson := .str (String.ofList ['5', '1', '8', '4', '3', '7', '7', '5', '5', '1', '5', '2', '0', '8', '0', '1', '1', '2', '4', '4', '0', '0', '1', '1', '8', '7', '0', '2', '1', '8', '0', '4', '1', '9', '4', '0', '6', '1', '7', '8', '3', '/', '4', '1', '4', '1', '4', '8', '4', '9', '7', '2', '4', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14455343Acc00300 : List (String × SourceJson) := (fragment14455343Field002Key00, fragment14455343Field002Value00) :: fragment14455343Acc00200
noncomputable def fragment14455343Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '1', '8', '4', '3', '7', '7', '5', '5', '1', '5', '2', '0', '8', '0', '1', '1', '2', '4', '4', '0', '0', '1', '1', '8', '7', '0', '2', '1', '8', '0', '4', '1', '9', '4', '0', '6', '1', '7', '8', '3', '/', '4', '1', '4', '1', '4', '8', '4', '9', '7', '2', '4', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14455343_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment14455343Field002Chars00 ++ tail)) fragment14455343Acc00200 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment14455343Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14455343_object_field_002"
  err.flush

noncomputable def fragment14455343Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment14455343Field003Value00 : SourceJson := .str (String.ofList ['2', '3', '4', '3', '0', '7', '/', '6', '1', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14455343Acc00400 : List (String × SourceJson) := (fragment14455343Field003Key00, fragment14455343Field003Value00) :: fragment14455343Acc00300
noncomputable def fragment14455343Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '3', '4', '3', '0', '7', '/', '6', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14455343_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment14455343Field003Chars00 ++ tail)) fragment14455343Acc00300 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment14455343Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14455343_object_field_003"
  err.flush

noncomputable def fragment14455343Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment14455343Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '9', '3', '6', '9', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '3', '6', '9', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '8', '1', '2', '9', '/', '2', '2', '0', '8', '0', '0', '0']), .str (String.ofList ['5', '7', '1', '8', '6', '7', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '5', '6', '2', '4', '7', '/', '3', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '2', '1', '6', '9', '1', '/', '1', '8', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '1', '2', '1', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '1', '2', '1', '/', '9', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment14455343Acc00500 : List (String × SourceJson) := (fragment14455343Field004Key00, fragment14455343Field004Value00) :: fragment14455343Acc00400
noncomputable def fragment14455343Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '3', '6', '9', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '3', '6', '9', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '1', '2', '9', '/', '2', '2', '0', '8', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '1', '8', '6', '7', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '5', '6', '2', '4', '7', '/', '3', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '2', '1', '6', '9', '1', '/', '1', '8', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '2', '1', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '2', '1', '/', '9', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14455343_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment14455343Field004Chars00 ++ tail)) fragment14455343Acc00400 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment14455343Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14455343_object_field_004"
  err.flush

noncomputable def fragment14455343Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment14455343Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '8', '3', '9', '6', '4', '8', '5', '2', '4', '3', '3', '2', '3', '/', '6', '4', '4', '8', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '8', '4', '0', '8', '6', '7', '2', '1', '3', '3', '8', '3', '/', '6', '4', '4', '8', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '5', '7', '8', '0', '9', '7', '5', '3', '2', '1', '8', '7', '/', '1', '5', '2', '7', '2', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '2', '9', '7', '3', '0', '0', '4', '6', '1', '0', '9', '1', '/', '1', '1', '6', '0', '7', '0', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '6', '3', '4', '3', '1', '6', '6', '9', '7', '7', '/', '3', '8', '1', '8', '1', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '8', '9', '0', '0', '3', '1', '0', '0', '8', '0', '7', '/', '1', '5', '2', '7', '2', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '7', '6', '8', '2', '0', '6', '8', '4', '2', '1', '3', '1', '/', '4', '5', '8', '1', '7', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '1', '4', '1', '6', '0', '0', '3', '6', '4', '6', '1', '/', '1', '1', '4', '5', '4', '3', '4', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '8', '4', '2', '2', '7', '1', '0', '1', '4', '3', '3', '/', '8', '2', '9', '0', '7', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '2', '7', '3', '8', '3', '7', '7', '8', '3', '3', '3', '/', '8', '2', '9', '0', '7', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment14455343Acc00600 : List (String × SourceJson) := (fragment14455343Field005Key00, fragment14455343Field005Value00) :: fragment14455343Acc00500
noncomputable def fragment14455343Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '3', '9', '6', '4', '8', '5', '2', '4', '3', '3', '2', '3', '/', '6', '4', '4', '8', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '8', '4', '0', '8', '6', '7', '2', '1', '3', '3', '8', '3', '/', '6', '4', '4', '8', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '5', '7', '8', '0', '9', '7', '5', '3', '2', '1', '8', '7', '/', '1', '5', '2', '7', '2', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '2', '9', '7', '3', '0', '0', '4', '6', '1', '0', '9', '1', '/', '1', '1', '6', '0', '7', '0', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '6', '3', '4', '3', '1', '6', '6', '9', '7', '7', '/', '3', '8', '1', '8', '1', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '8', '9', '0', '0', '3', '1', '0', '0', '8', '0', '7', '/', '1', '5', '2', '7', '2', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '7', '6', '8', '2', '0', '6', '8', '4', '2', '1', '3', '1', '/', '4', '5', '8', '1', '7', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '1', '4', '1', '6', '0', '0', '3', '6', '4', '6', '1', '/', '1', '1', '4', '5', '4', '3', '4', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '8', '4', '2', '2', '7', '1', '0', '1', '4', '3', '3', '/', '8', '2', '9', '0', '7', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '2', '7', '3', '8', '3', '7', '7', '8', '3', '3', '3', '/', '8', '2', '9', '0', '7', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14455343_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment14455343Field005Chars00 ++ tail)) fragment14455343Acc00500 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment14455343Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14455343_object_field_005"
  err.flush

noncomputable def fragment14455343Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14455343Field006Value00 : SourceJson := .str (String.ofList ['7', '1', '7', '2', '8', '9', '4', '3', '1', '6', '8', '4', '8', '4', '1', '2', '1', '6', '2', '7', '3', '3', '7', '9', '8', '4', '2', '6', '4', '3', '8', '0', '3', '0', '1', '8', '4', '7', '3', '6', '2', '0', '8', '4', '8', '7', '5', '8', '6', '6', '9', '/', '8', '6', '0', '5', '8', '5', '2', '9', '0', '3', '4', '0', '2', '9', '0', '1', '7', '4', '2', '4', '7', '2', '6', '7', '0', '3', '3', '4', '2', '5', '3', '3', '0', '0', '7', '6', '1', '8', '3', '9', '9', '9', '2', '9', '6', '0', '3', '9', '2', '3', '0', '7', '1', '3', '3', '8', '8', '3', '0', '5', '7', '7', '6'])
noncomputable def fragment14455343Acc00700 : List (String × SourceJson) := (fragment14455343Field006Key00, fragment14455343Field006Value00) :: fragment14455343Acc00600
noncomputable def fragment14455343Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '1', '7', '2', '8', '9', '4', '3', '1', '6', '8', '4', '8', '4', '1', '2', '1', '6', '2', '7', '3', '3', '7', '9', '8', '4', '2', '6', '4', '3', '8', '0', '3', '0', '1', '8', '4', '7', '3', '6', '2', '0', '8', '4', '8', '7', '5', '8', '6', '6', '9', '/', '8', '6', '0', '5', '8', '5', '2', '9', '0', '3', '4', '0', '2', '9', '0', '1', '7', '4', '2', '4', '7', '2', '6', '7', '0', '3', '3', '4', '2', '5', '3', '3', '0', '0', '7', '6', '1', '8', '3', '9', '9', '9', '2', '9', '6', '0', '3', '9', '2', '3', '0', '7', '1', '3', '3', '8', '8', '3', '0', '5', '7', '7', '6', '"', ',']

theorem object_fragment14455343_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment14455343Field006Chars00 ++ tail)) fragment14455343Acc00600 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment14455343Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14455343_object_field_006"
  err.flush

noncomputable def fragment14455343Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14455343Field007Value00 : SourceJson := .str (String.ofList ['2', '4', '8', '3', '2', '4', '5', '0', '8', '1', '5', '9', '1', '1', '6', '5', '8', '7', '2', '9', '7', '5', '1', '5', '8', '8', '5', '7', '7', '5', '6', '4', '5', '0', '4', '4', '3', '1', '6', '8', '7', '7', '1', '5', '6', '1', '6', '7', '3', '6', '9', '4', '8', '2', '7', '5', '7', '1', '2', '3', '6', '0', '0', '3', '9', '6', '5', '1', '7', '3', '8', '8', '1', '5', '2', '0', '8', '3', '0', '8', '4', '8', '5', '7', '9', '0', '3', '5', '2', '7', '9', '4', '6', '5', '1', '7', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '6', '9', '3', '1', '4', '3', '9', '5', '5', '9', '9', '4', '5', '4', '8', '6', '2', '3', '1', '4', '7', '1', '6', '5', '4', '4', '4', '8', '6', '4', '0', '5', '7', '3', '7', '5', '3', '0', '0', '7', '4', '3', '6', '7', '3', '0', '2', '0', '2', '9', '7', '7', '6', '5', '5', '6', '4', '8', '3', '5', '1', '9', '9', '0', '0', '3', '2', '7', '8', '3', '1', '6', '7', '8', '0', '0', '8', '4', '8', '3', '1', '4', '9', '8', '2', '7', '5', '4', '6', '1', '2', '1', '2', '1', '0', '5', '9', '8', '1', '0', '1', '2', '2', '3', '8', '8', '0', '2', '3', '4', '2', '4', '5', '6', '7', '0', '8', '6', '2', '0', '8', '2', '6', '8', '1', '5', '8', '9'])
noncomputable def fragment14455343Acc00800 : List (String × SourceJson) := (fragment14455343Field007Key00, fragment14455343Field007Value00) :: fragment14455343Acc00700
noncomputable def fragment14455343Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '4', '8', '3', '2', '4', '5', '0', '8', '1', '5', '9', '1', '1', '6', '5', '8', '7', '2', '9', '7', '5', '1', '5', '8', '8', '5', '7', '7', '5', '6', '4', '5', '0', '4', '4', '3', '1', '6', '8', '7', '7', '1', '5', '6', '1', '6', '7', '3', '6', '9', '4', '8', '2', '7', '5', '7', '1', '2', '3', '6', '0', '0', '3', '9', '6', '5', '1', '7', '3', '8', '8', '1', '5', '2', '0', '8', '3', '0', '8', '4', '8', '5', '7', '9', '0', '3', '5', '2', '7', '9', '4', '6', '5', '1', '7', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '6', '9', '3', '1', '4', '3', '9', '5', '5', '9', '9', '4', '5', '4', '8', '6', '2', '3', '1', '4', '7', '1', '6', '5', '4', '4', '4', '8', '6', '4', '0', '5', '7', '3', '7', '5', '3', '0', '0', '7', '4', '3', '6', '7', '3', '0', '2', '0', '2', '9', '7', '7', '6', '5', '5', '6', '4', '8', '3', '5', '1', '9', '9', '0', '0', '3', '2', '7', '8', '3', '1', '6', '7', '8', '0', '0', '8', '4', '8', '3', '1', '4', '9', '8', '2', '7', '5', '4', '6', '1', '2', '1', '2', '1', '0', '5', '9', '8', '1', '0', '1', '2', '2', '3', '8', '8', '0', '2', '3', '4', '2', '4', '5', '6', '7', '0', '8', '6', '2', '0', '8', '2', '6', '8', '1', '5', '8', '9', '"', ',']

theorem object_fragment14455343_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment14455343Field007Chars00 ++ tail)) fragment14455343Acc00700 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment14455343Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14455343_object_field_007"
  err.flush

noncomputable def fragment14455343Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14455343Field008Value00 : SourceJson := .str (String.ofList ['6', '6', '0', '3', '5', '8', '9', '9', '4', '0', '6', '1', '1', '1', '7', '8', '6'])
noncomputable def fragment14455343Acc00900 : List (String × SourceJson) := (fragment14455343Field008Key00, fragment14455343Field008Value00) :: fragment14455343Acc00800
noncomputable def fragment14455343Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '0', '3', '5', '8', '9', '9', '4', '0', '6', '1', '1', '1', '7', '8', '6', '"', ',']

theorem object_fragment14455343_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment14455343Field008Chars00 ++ tail)) fragment14455343Acc00800 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment14455343Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14455343_object_field_008"
  err.flush

noncomputable def fragment14455343Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14455343Field009Value00 : SourceJson := .str (String.ofList ['3', '4', '5', '5', '7', '8', '7', '2', '8', '3', '9', '2', '9', '3', '5', '9', '3', '7'])
noncomputable def fragment14455343Acc01000 : List (String × SourceJson) := (fragment14455343Field009Key00, fragment14455343Field009Value00) :: fragment14455343Acc00900
noncomputable def fragment14455343Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '4', '5', '5', '7', '8', '7', '2', '8', '3', '9', '2', '9', '3', '5', '9', '3', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment14455343_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment14455343Field009Chars00 ++ tail)) fragment14455343Acc00900 =
      .ok (.obj (fragment14455343Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14455343_object_field_009"
  err.flush

noncomputable def fragment14455343Chars : List Char := '{' :: (fragment14455343Field000Chars00 ++ fragment14455343Field001Chars00 ++ fragment14455343Field002Chars00 ++ fragment14455343Field003Chars00 ++ fragment14455343Field004Chars00 ++ fragment14455343Field005Chars00 ++ fragment14455343Field006Chars00 ++ fragment14455343Field007Chars00 ++ fragment14455343Field008Chars00 ++ fragment14455343Field009Chars00)
noncomputable def fragment14455343Value : SourceJson := .obj (fragment14455343Acc01000.reverse)

theorem value_fragment14455343 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 259) (fragment14455343Chars ++ tail) =
      .ok (fragment14455343Value, tail) := by
  have hinput : fragment14455343Chars ++ tail = '{' :: (fragment14455343Field000Chars00 ++ (fragment14455343Field001Chars00 ++ (fragment14455343Field002Chars00 ++ (fragment14455343Field003Chars00 ++ (fragment14455343Field004Chars00 ++ (fragment14455343Field005Chars00 ++ (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment14455343Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 259) (fragment14455343Chars ++ tail) =
        SourceJson.value (fuel + 259) ('{' :: (fragment14455343Field000Chars00 ++ (fragment14455343Field001Chars00 ++ (fragment14455343Field002Chars00 ++ (fragment14455343Field003Chars00 ++ (fragment14455343Field004Chars00 ++ (fragment14455343Field005Chars00 ++ (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 259)) hinput
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment14455343Field000Chars00 ++ (fragment14455343Field001Chars00 ++ (fragment14455343Field002Chars00 ++ (fragment14455343Field003Chars00 ++ (fragment14455343Field004Chars00 ++ (fragment14455343Field005Chars00 ++ (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail)))))))))))) fragment14455343Acc00000 := by rfl
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment14455343Field001Chars00 ++ (fragment14455343Field002Chars00 ++ (fragment14455343Field003Chars00 ++ (fragment14455343Field004Chars00 ++ (fragment14455343Field005Chars00 ++ (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail))))))))))) fragment14455343Acc00100 := object_fragment14455343_field_000 fuel (fragment14455343Field001Chars00 ++ (fragment14455343Field002Chars00 ++ (fragment14455343Field003Chars00 ++ (fragment14455343Field004Chars00 ++ (fragment14455343Field005Chars00 ++ (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment14455343Field002Chars00 ++ (fragment14455343Field003Chars00 ++ (fragment14455343Field004Chars00 ++ (fragment14455343Field005Chars00 ++ (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail)))))))))) fragment14455343Acc00200 := object_fragment14455343_field_001 fuel (fragment14455343Field002Chars00 ++ (fragment14455343Field003Chars00 ++ (fragment14455343Field004Chars00 ++ (fragment14455343Field005Chars00 ++ (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment14455343Field003Chars00 ++ (fragment14455343Field004Chars00 ++ (fragment14455343Field005Chars00 ++ (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail))))))))) fragment14455343Acc00300 := object_fragment14455343_field_002 fuel (fragment14455343Field003Chars00 ++ (fragment14455343Field004Chars00 ++ (fragment14455343Field005Chars00 ++ (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment14455343Field004Chars00 ++ (fragment14455343Field005Chars00 ++ (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail)))))))) fragment14455343Acc00400 := object_fragment14455343_field_003 fuel (fragment14455343Field004Chars00 ++ (fragment14455343Field005Chars00 ++ (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment14455343Field005Chars00 ++ (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail))))))) fragment14455343Acc00500 := object_fragment14455343_field_004 fuel (fragment14455343Field005Chars00 ++ (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail)))))) fragment14455343Acc00600 := object_fragment14455343_field_005 fuel (fragment14455343Field006Chars00 ++ (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail))))) fragment14455343Acc00700 := object_fragment14455343_field_006 fuel (fragment14455343Field007Chars00 ++ (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail)))) fragment14455343Acc00800 := object_fragment14455343_field_007 fuel (fragment14455343Field008Chars00 ++ (fragment14455343Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment14455343Field009Chars00 ++ (tail))) fragment14455343Acc00900 := object_fragment14455343_field_008 fuel (fragment14455343Field009Chars00 ++ (tail))
    _ = .ok (fragment14455343Value, tail) := object_fragment14455343_field_009 fuel (tail)

noncomputable def fragment14456998Acc00000 : List (String × SourceJson) := []

noncomputable def fragment14456998Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment14456998Field000Value00 : SourceJson := .number (String.ofList ['6', '5', '9', '8'])
noncomputable def fragment14456998Acc00100 : List (String × SourceJson) := (fragment14456998Field000Key00, fragment14456998Field000Value00) :: fragment14456998Acc00000
noncomputable def fragment14456998Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '5', '9', '8', ',']

theorem object_fragment14456998_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 339) (SourceJson.white (fragment14456998Field000Chars00 ++ tail)) fragment14456998Acc00000 =
      SourceJson.object (fuel + 338) (SourceJson.white tail) fragment14456998Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14456998_object_field_000"
  err.flush

noncomputable def fragment14456998Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment14456998Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '7']), .number (String.ofList ['1', '3', '5']), .number (String.ofList ['1', '1', '7']), .number (String.ofList ['1', '1', '1']), .number (String.ofList ['1', '1', '0']), .number (String.ofList ['1', '0', '6']), .number (String.ofList ['9', '7']), .number (String.ofList ['5', '5'])]
noncomputable def fragment14456998Acc00200 : List (String × SourceJson) := (fragment14456998Field001Key00, fragment14456998Field001Value00) :: fragment14456998Acc00100
noncomputable def fragment14456998Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14456998_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 338) (SourceJson.white (fragment14456998Field001Chars00 ++ tail)) fragment14456998Acc00100 =
      SourceJson.object (fuel + 337) (SourceJson.white tail) fragment14456998Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14456998_object_field_001"
  err.flush

noncomputable def fragment14456998Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment14456998Field002Value00 : SourceJson := .str (String.ofList ['2', '4', '8', '1', '8', '3', '2', '0', '7', '0', '0', '1', '2', '3', '6', '0', '0', '4', '2', '0', '5', '0', '7', '0', '3', '3', '9', '6', '8', '5', '1', '9', '0', '9', '/', '2', '9', '0', '1', '3', '8', '2', '7', '1', '2', '5', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14456998Acc00300 : List (String × SourceJson) := (fragment14456998Field002Key00, fragment14456998Field002Value00) :: fragment14456998Acc00200
noncomputable def fragment14456998Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '4', '8', '1', '8', '3', '2', '0', '7', '0', '0', '1', '2', '3', '6', '0', '0', '4', '2', '0', '5', '0', '7', '0', '3', '3', '9', '6', '8', '5', '1', '9', '0', '9', '/', '2', '9', '0', '1', '3', '8', '2', '7', '1', '2', '5', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14456998_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 337) (SourceJson.white (fragment14456998Field002Chars00 ++ tail)) fragment14456998Acc00200 =
      SourceJson.object (fuel + 336) (SourceJson.white tail) fragment14456998Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14456998_object_field_002"
  err.flush

noncomputable def fragment14456998Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment14456998Field003Value00 : SourceJson := .str (String.ofList ['2', '3', '7', '4', '0', '8', '2', '9', '/', '2', '5', '4', '6', '1', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14456998Acc00400 : List (String × SourceJson) := (fragment14456998Field003Key00, fragment14456998Field003Value00) :: fragment14456998Acc00300
noncomputable def fragment14456998Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '3', '7', '4', '0', '8', '2', '9', '/', '2', '5', '4', '6', '1', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14456998_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 336) (SourceJson.white (fragment14456998Field003Chars00 ++ tail)) fragment14456998Acc00300 =
      SourceJson.object (fuel + 335) (SourceJson.white tail) fragment14456998Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14456998_object_field_003"
  err.flush

noncomputable def fragment14456998Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment14456998Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '8', '9', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '6', '8', '7', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '6', '8', '7', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '/', '3', '8', '4']), .str (String.ofList ['1', '1', '/', '3', '8', '4'])]
noncomputable def fragment14456998Acc00500 : List (String × SourceJson) := (fragment14456998Field004Key00, fragment14456998Field004Value00) :: fragment14456998Acc00400
noncomputable def fragment14456998Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '8', '9', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '6', '8', '7', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '6', '8', '7', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '3', '8', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '3', '8', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14456998_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 335) (SourceJson.white (fragment14456998Field004Chars00 ++ tail)) fragment14456998Acc00400 =
      SourceJson.object (fuel + 334) (SourceJson.white tail) fragment14456998Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14456998_object_field_004"
  err.flush

noncomputable def fragment14456998Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment14456998Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '2', '9', '4', '8', '7', '4', '7', '0', '9', '1', '3', '0', '5', '6', '4', '9', '4', '9', '/', '1', '0', '2', '0', '8', '7', '4', '6', '3', '9', '6', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '3', '5', '2', '9', '0', '6', '1', '7', '7', '3', '5', '7', '0', '7', '4', '9', '/', '2', '0', '4', '1', '7', '4', '9', '2', '7', '9', '3', '2', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '6', '7', '7', '3', '8', '5', '8', '3', '1', '3', '0', '8', '6', '4', '9', '/', '8', '9', '5', '5', '0', '4', '0', '6', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '8', '8', '8', '4', '7', '7', '9', '9', '7', '5', '8', '7', '7', '9', '4', '3', '/', '4', '8', '6', '1', '3', '0', '7', '8', '0', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '1', '0', '4', '7', '3', '2', '1', '3', '6', '8', '0', '5', '5', '3', '2', '9', '/', '2', '6', '8', '6', '5', '1', '2', '2', '0', '9', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '9', '9', '5', '3', '1', '2', '4', '4', '7', '8', '0', '6', '7', '3', '3', '/', '8', '9', '5', '5', '0', '4', '0', '6', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '0', '3', '6', '1', '4', '1', '0', '4', '0', '4', '8', '7', '6', '7', '/', '8', '3', '9', '5', '3', '5', '0', '6', '5', '5', '1', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '0', '1', '8', '1', '2', '0', '3', '9', '6', '1', '6', '9', '1', '7', '/', '1', '7', '9', '1', '0', '0', '8', '1', '3', '9', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '1', '7', '6', '8', '0', '1', '9', '1', '9', '0', '4', '7', '4', '4', '1', '3', '/', '6', '8', '0', '5', '8', '3', '0', '9', '3', '1', '0', '8', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '3', '0', '9', '2', '4', '6', '5', '3', '1', '1', '8', '8', '3', '9', '6', '1', '/', '6', '8', '0', '5', '8', '3', '0', '9', '3', '1', '0', '8', '8', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment14456998Acc00600 : List (String × SourceJson) := (fragment14456998Field005Key00, fragment14456998Field005Value00) :: fragment14456998Acc00500
noncomputable def fragment14456998Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '9', '4', '8', '7', '4', '7', '0', '9', '1', '3', '0', '5', '6', '4', '9', '4', '9', '/', '1', '0', '2', '0', '8', '7', '4', '6', '3', '9', '6', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '3', '5', '2', '9', '0', '6', '1', '7', '7', '3', '5', '7', '0', '7', '4', '9', '/', '2', '0', '4', '1', '7', '4', '9', '2', '7', '9', '3', '2', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '6', '7', '7', '3', '8', '5', '8', '3', '1', '3', '0', '8', '6', '4', '9', '/', '8', '9', '5', '5', '0', '4', '0', '6', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '8', '8', '8', '4', '7', '7', '9', '9', '7', '5', '8', '7', '7', '9', '4', '3', '/', '4', '8', '6', '1', '3', '0', '7', '8', '0', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '1', '0', '4', '7', '3', '2', '1', '3', '6', '8', '0', '5', '5', '3', '2', '9', '/', '2', '6', '8', '6', '5', '1', '2', '2', '0', '9', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '9', '9', '5', '3', '1', '2', '4', '4', '7', '8', '0', '6', '7', '3', '3', '/', '8', '9', '5', '5', '0', '4', '0', '6', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '0', '3', '6', '1', '4', '1', '0', '4', '0', '4', '8', '7', '6', '7', '/', '8', '3', '9', '5', '3', '5', '0', '6', '5', '5', '1', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '0', '1', '8', '1', '2', '0', '3', '9', '6', '1', '6', '9', '1', '7', '/', '1', '7', '9', '1', '0', '0', '8', '1', '3', '9', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '7', '6', '8', '0', '1', '9', '1', '9', '0', '4', '7', '4', '4', '1', '3', '/', '6', '8', '0', '5', '8', '3', '0', '9', '3', '1', '0', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '3', '0', '9', '2', '4', '6', '5', '3', '1', '1', '8', '8', '3', '9', '6', '1', '/', '6', '8', '0', '5', '8', '3', '0', '9', '3', '1', '0', '8', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14456998_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 334) (SourceJson.white (fragment14456998Field005Chars00 ++ tail)) fragment14456998Acc00500 =
      SourceJson.object (fuel + 333) (SourceJson.white tail) fragment14456998Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14456998_object_field_005"
  err.flush

noncomputable def fragment14456998Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14456998Field006Value00 : SourceJson := .str (String.ofList ['3', '4', '0', '4', '5', '7', '6', '1', '1', '7', '0', '6', '5', '1', '8', '9', '0', '8', '7', '5', '4', '0', '7', '0', '1', '9', '1', '7', '8', '6', '1', '4', '5', '1', '9', '8', '0', '8', '/', '1', '1', '1', '0', '2', '7', '6', '9', '1', '2', '5', '8', '9', '3', '4', '5', '6', '4', '7', '2', '0', '4', '2', '4', '6', '4', '1', '5', '9', '8', '5', '0', '7', '3', '0', '1', '2', '1', '3', '7', '1', '6', '5', '2', '1', '9', '5', '9', '5', '9', '3', '7', '5'])
noncomputable def fragment14456998Acc00700 : List (String × SourceJson) := (fragment14456998Field006Key00, fragment14456998Field006Value00) :: fragment14456998Acc00600
noncomputable def fragment14456998Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '4', '0', '4', '5', '7', '6', '1', '1', '7', '0', '6', '5', '1', '8', '9', '0', '8', '7', '5', '4', '0', '7', '0', '1', '9', '1', '7', '8', '6', '1', '4', '5', '1', '9', '8', '0', '8', '/', '1', '1', '1', '0', '2', '7', '6', '9', '1', '2', '5', '8', '9', '3', '4', '5', '6', '4', '7', '2', '0', '4', '2', '4', '6', '4', '1', '5', '9', '8', '5', '0', '7', '3', '0', '1', '2', '1', '3', '7', '1', '6', '5', '2', '1', '9', '5', '9', '5', '9', '3', '7', '5', '"', ',']

theorem object_fragment14456998_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 333) (SourceJson.white (fragment14456998Field006Chars00 ++ tail)) fragment14456998Acc00600 =
      SourceJson.object (fuel + 332) (SourceJson.white tail) fragment14456998Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14456998_object_field_006"
  err.flush

noncomputable def fragment14456998Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14456998Field007Value00 : SourceJson := .str (String.ofList ['8', '0', '5', '6', '7', '5', '8', '4', '0', '6', '7', '4', '7', '7', '1', '9', '5', '2', '4', '4', '0', '3', '1', '1', '7', '1', '0', '1', '0', '3', '3', '1', '0', '7', '7', '8', '1', '5', '0', '6', '5', '2', '7', '6', '6', '9', '4', '8', '8', '5', '8', '0', '9', '3', '5', '7', '8', '7', '2', '6', '0', '5', '4', '6', '3', '1', '3', '1', '2', '0', '2', '6', '9', '2', '3', '3', '3', '9', '6', '4', '2', '2', '4', '5', '2', '5', '5', '0', '8', '5', '1', '9', '8', '8', '9', '2', '1', '4', '4', '8', '1', '8', '7', '9', '5', '7', '5', '3', '2', '0', '8', '3', '3', '4', '2', '2', '0', '8', '1', '1', '7', '9', '4', '6', '6', '7', '3', '9', '7', '8', '1', '8', '3', '4', '3', '4', '5', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '9', '1', '0', '6', '5', '8', '8', '5', '0', '3', '6', '4', '8', '1', '2', '6', '8', '4', '5', '4', '1', '0', '8', '4', '3', '0', '9', '9', '4', '0', '5', '8', '2', '6', '5', '3', '3', '8', '2', '9', '2', '3', '5', '8', '0', '8', '8', '9', '2', '2', '2', '0', '6', '8', '5', '7', '3', '2', '7', '4', '5', '1', '4', '7', '7', '4', '4', '5', '8', '6', '3', '2', '3', '3', '8', '6', '0', '9', '9', '2', '9', '6', '7', '9', '2', '2', '6', '2', '8', '3', '4', '0', '7', '9', '3', '7', '4', '0', '0', '7', '4', '8', '6', '6', '1', '0', '5', '8', '6', '1', '8', '7', '3', '7', '4', '9', '2', '9', '1', '9', '1', '4', '7', '5', '4', '7', '6', '9', '3', '2', '1', '6', '4', '1', '6', '0', '7', '9', '1', '1', '6', '0', '1', '7', '5', '3', '0', '1', '0', '8', '5', '7', '1', '2', '0', '6', '8', '0', '2', '8', '3', '0', '5', '0', '3', '9', '3', '7', '5', '3'])
noncomputable def fragment14456998Acc00800 : List (String × SourceJson) := (fragment14456998Field007Key00, fragment14456998Field007Value00) :: fragment14456998Acc00700
noncomputable def fragment14456998Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '0', '5', '6', '7', '5', '8', '4', '0', '6', '7', '4', '7', '7', '1', '9', '5', '2', '4', '4', '0', '3', '1', '1', '7', '1', '0', '1', '0', '3', '3', '1', '0', '7', '7', '8', '1', '5', '0', '6', '5', '2', '7', '6', '6', '9', '4', '8', '8', '5', '8', '0', '9', '3', '5', '7', '8', '7', '2', '6', '0', '5', '4', '6', '3', '1', '3', '1', '2', '0', '2', '6', '9', '2', '3', '3', '3', '9', '6', '4', '2', '2', '4', '5', '2', '5', '5', '0', '8', '5', '1', '9', '8', '8', '9', '2', '1', '4', '4', '8', '1', '8', '7', '9', '5', '7', '5', '3', '2', '0', '8', '3', '3', '4', '2', '2', '0', '8', '1', '1', '7', '9', '4', '6', '6', '7', '3', '9', '7', '8', '1', '8', '3', '4', '3', '4', '5', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '9', '1', '0', '6', '5', '8', '8', '5', '0', '3', '6', '4', '8', '1', '2', '6', '8', '4', '5', '4', '1', '0', '8', '4', '3', '0', '9', '9', '4', '0', '5', '8', '2', '6', '5', '3', '3', '8', '2', '9', '2', '3', '5', '8', '0', '8', '8', '9', '2', '2', '2', '0', '6', '8', '5', '7', '3', '2', '7', '4', '5', '1', '4', '7', '7', '4', '4', '5', '8', '6', '3', '2', '3', '3', '8', '6', '0', '9', '9', '2', '9', '6', '7', '9', '2', '2', '6', '2', '8', '3', '4', '0', '7', '9', '3', '7', '4', '0', '0', '7', '4', '8', '6', '6', '1', '0', '5', '8', '6', '1', '8', '7', '3', '7', '4', '9', '2', '9', '1', '9', '1', '4', '7', '5', '4', '7', '6', '9', '3', '2', '1', '6', '4', '1', '6', '0', '7', '9', '1', '1', '6', '0', '1', '7', '5', '3', '0', '1', '0', '8', '5', '7', '1', '2', '0', '6', '8', '0', '2', '8', '3', '0', '5', '0', '3', '9', '3', '7', '5', '3', '"', ',']

theorem object_fragment14456998_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 332) (SourceJson.white (fragment14456998Field007Chars00 ++ tail)) fragment14456998Acc00700 =
      SourceJson.object (fuel + 331) (SourceJson.white tail) fragment14456998Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14456998_object_field_007"
  err.flush

noncomputable def fragment14456998Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14456998Field008Value00 : SourceJson := .str (String.ofList ['2', '4', '2', '9', '4', '6', '8', '7', '8', '2', '3', '9', '5', '4', '6'])
noncomputable def fragment14456998Acc00900 : List (String × SourceJson) := (fragment14456998Field008Key00, fragment14456998Field008Value00) :: fragment14456998Acc00800
noncomputable def fragment14456998Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '2', '9', '4', '6', '8', '7', '8', '2', '3', '9', '5', '4', '6', '"', ',']

theorem object_fragment14456998_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 331) (SourceJson.white (fragment14456998Field008Chars00 ++ tail)) fragment14456998Acc00800 =
      SourceJson.object (fuel + 330) (SourceJson.white tail) fragment14456998Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14456998_object_field_008"
  err.flush

noncomputable def fragment14456998Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14456998Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '9', '9', '5', '0', '9', '5', '0', '5', '5', '8', '7', '1', '0'])
noncomputable def fragment14456998Acc01000 : List (String × SourceJson) := (fragment14456998Field009Key00, fragment14456998Field009Value00) :: fragment14456998Acc00900
noncomputable def fragment14456998Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '7', '9', '9', '5', '0', '9', '5', '0', '5', '5', '8', '7', '1', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment14456998_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 330) (SourceJson.white (fragment14456998Field009Chars00 ++ tail)) fragment14456998Acc00900 =
      .ok (.obj (fragment14456998Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14456998_object_field_009"
  err.flush

noncomputable def fragment14456998Chars : List Char := '{' :: (fragment14456998Field000Chars00 ++ fragment14456998Field001Chars00 ++ fragment14456998Field002Chars00 ++ fragment14456998Field003Chars00 ++ fragment14456998Field004Chars00 ++ fragment14456998Field005Chars00 ++ fragment14456998Field006Chars00 ++ fragment14456998Field007Chars00 ++ fragment14456998Field008Chars00 ++ fragment14456998Field009Chars00)
noncomputable def fragment14456998Value : SourceJson := .obj (fragment14456998Acc01000.reverse)

theorem value_fragment14456998 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 340) (fragment14456998Chars ++ tail) =
      .ok (fragment14456998Value, tail) := by
  have hinput : fragment14456998Chars ++ tail = '{' :: (fragment14456998Field000Chars00 ++ (fragment14456998Field001Chars00 ++ (fragment14456998Field002Chars00 ++ (fragment14456998Field003Chars00 ++ (fragment14456998Field004Chars00 ++ (fragment14456998Field005Chars00 ++ (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment14456998Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 340) (fragment14456998Chars ++ tail) =
        SourceJson.value (fuel + 340) ('{' :: (fragment14456998Field000Chars00 ++ (fragment14456998Field001Chars00 ++ (fragment14456998Field002Chars00 ++ (fragment14456998Field003Chars00 ++ (fragment14456998Field004Chars00 ++ (fragment14456998Field005Chars00 ++ (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 340)) hinput
    _ = SourceJson.object (fuel + 339) (SourceJson.white (fragment14456998Field000Chars00 ++ (fragment14456998Field001Chars00 ++ (fragment14456998Field002Chars00 ++ (fragment14456998Field003Chars00 ++ (fragment14456998Field004Chars00 ++ (fragment14456998Field005Chars00 ++ (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail)))))))))))) fragment14456998Acc00000 := by rfl
    _ = SourceJson.object (fuel + 338) (SourceJson.white (fragment14456998Field001Chars00 ++ (fragment14456998Field002Chars00 ++ (fragment14456998Field003Chars00 ++ (fragment14456998Field004Chars00 ++ (fragment14456998Field005Chars00 ++ (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail))))))))))) fragment14456998Acc00100 := object_fragment14456998_field_000 fuel (fragment14456998Field001Chars00 ++ (fragment14456998Field002Chars00 ++ (fragment14456998Field003Chars00 ++ (fragment14456998Field004Chars00 ++ (fragment14456998Field005Chars00 ++ (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 337) (SourceJson.white (fragment14456998Field002Chars00 ++ (fragment14456998Field003Chars00 ++ (fragment14456998Field004Chars00 ++ (fragment14456998Field005Chars00 ++ (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail)))))))))) fragment14456998Acc00200 := object_fragment14456998_field_001 fuel (fragment14456998Field002Chars00 ++ (fragment14456998Field003Chars00 ++ (fragment14456998Field004Chars00 ++ (fragment14456998Field005Chars00 ++ (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 336) (SourceJson.white (fragment14456998Field003Chars00 ++ (fragment14456998Field004Chars00 ++ (fragment14456998Field005Chars00 ++ (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail))))))))) fragment14456998Acc00300 := object_fragment14456998_field_002 fuel (fragment14456998Field003Chars00 ++ (fragment14456998Field004Chars00 ++ (fragment14456998Field005Chars00 ++ (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 335) (SourceJson.white (fragment14456998Field004Chars00 ++ (fragment14456998Field005Chars00 ++ (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail)))))))) fragment14456998Acc00400 := object_fragment14456998_field_003 fuel (fragment14456998Field004Chars00 ++ (fragment14456998Field005Chars00 ++ (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 334) (SourceJson.white (fragment14456998Field005Chars00 ++ (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail))))))) fragment14456998Acc00500 := object_fragment14456998_field_004 fuel (fragment14456998Field005Chars00 ++ (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 333) (SourceJson.white (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail)))))) fragment14456998Acc00600 := object_fragment14456998_field_005 fuel (fragment14456998Field006Chars00 ++ (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 332) (SourceJson.white (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail))))) fragment14456998Acc00700 := object_fragment14456998_field_006 fuel (fragment14456998Field007Chars00 ++ (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 331) (SourceJson.white (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail)))) fragment14456998Acc00800 := object_fragment14456998_field_007 fuel (fragment14456998Field008Chars00 ++ (fragment14456998Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 330) (SourceJson.white (fragment14456998Field009Chars00 ++ (tail))) fragment14456998Acc00900 := object_fragment14456998_field_008 fuel (fragment14456998Field009Chars00 ++ (tail))
    _ = .ok (fragment14456998Value, tail) := object_fragment14456998_field_009 fuel (tail)

noncomputable def fragment14458765Acc00000 : List (String × SourceJson) := []

noncomputable def fragment14458765Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment14458765Field000Value00 : SourceJson := .number (String.ofList ['6', '5', '9', '9'])
noncomputable def fragment14458765Acc00100 : List (String × SourceJson) := (fragment14458765Field000Key00, fragment14458765Field000Value00) :: fragment14458765Acc00000
noncomputable def fragment14458765Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '5', '9', '9', ',']

theorem object_fragment14458765_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment14458765Field000Chars00 ++ tail)) fragment14458765Acc00000 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment14458765Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14458765_object_field_000"
  err.flush

noncomputable def fragment14458765Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment14458765Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['4', '3']), .number (String.ofList ['4', '2']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '4'])]
noncomputable def fragment14458765Acc00200 : List (String × SourceJson) := (fragment14458765Field001Key00, fragment14458765Field001Value00) :: fragment14458765Acc00100
noncomputable def fragment14458765Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14458765_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment14458765Field001Chars00 ++ tail)) fragment14458765Acc00100 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment14458765Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14458765_object_field_001"
  err.flush

noncomputable def fragment14458765Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment14458765Field002Value00 : SourceJson := .str (String.ofList ['3', '6', '1', '0', '2', '0', '7', '2', '7', '1', '1', '1', '6', '3', '4', '4', '2', '5', '5', '8', '6', '6', '7', '7', '7', '6', '1', '3', '2', '3', '9', '4', '2', '6', '4', '8', '5', '2', '9', '6', '7', '3', '4', '4', '7', '3', '/', '7', '1', '3', '8', '0', '9', '1', '6', '9', '0', '5', '2', '8', '6', '8', '8', '0', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14458765Acc00300 : List (String × SourceJson) := (fragment14458765Field002Key00, fragment14458765Field002Value00) :: fragment14458765Acc00200
noncomputable def fragment14458765Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '6', '1', '0', '2', '0', '7', '2', '7', '1', '1', '1', '6', '3', '4', '4', '2', '5', '5', '8', '6', '6', '7', '7', '7', '6', '1', '3', '2', '3', '9', '4', '2', '6', '4', '8', '5', '2', '9', '6', '7', '3', '4', '4', '7', '3', '/', '7', '1', '3', '8', '0', '9', '1', '6', '9', '0', '5', '2', '8', '6', '8', '8', '0', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14458765_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment14458765Field002Chars00 ++ tail)) fragment14458765Acc00200 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment14458765Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14458765_object_field_002"
  err.flush

noncomputable def fragment14458765Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment14458765Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '7', '4', '0', '1', '/', '6', '8', '4', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment14458765Acc00400 : List (String × SourceJson) := (fragment14458765Field003Key00, fragment14458765Field003Value00) :: fragment14458765Acc00300
noncomputable def fragment14458765Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '7', '4', '0', '1', '/', '6', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment14458765_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment14458765Field003Chars00 ++ tail)) fragment14458765Acc00300 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment14458765Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14458765_object_field_003"
  err.flush

noncomputable def fragment14458765Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment14458765Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '4', '5', '3', '0', '2', '7', '/', '2', '3', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '5', '3', '0', '2', '7', '/', '2', '3', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '4', '2', '1', '9', '5', '9', '/', '3', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '9', '5', '2', '8', '8', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '1', '2', '1', '/', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '1', '2', '1', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '1', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0'])]
noncomputable def fragment14458765Acc00500 : List (String × SourceJson) := (fragment14458765Field004Key00, fragment14458765Field004Value00) :: fragment14458765Acc00400
noncomputable def fragment14458765Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '3', '0', '2', '7', '/', '2', '3', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '3', '0', '2', '7', '/', '2', '3', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '4', '2', '1', '9', '5', '9', '/', '3', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '9', '5', '2', '8', '8', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '2', '1', '/', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '2', '1', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '1', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14458765_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment14458765Field004Chars00 ++ tail)) fragment14458765Acc00400 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment14458765Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14458765_object_field_004"
  err.flush

noncomputable def fragment14458765Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment14458765Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '8', '8', '9', '0', '9', '7', '3', '0', '5', '6', '9', '1', '/', '4', '8', '4', '5', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '4', '6', '6', '3', '6', '0', '3', '0', '6', '6', '1', '1', '/', '2', '4', '2', '2', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '2', '3', '4', '9', '7', '0', '6', '6', '2', '1', '/', '3', '0', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '8', '0', '1', '6', '3', '7', '2', '1', '5', '4', '1', '1', '/', '4', '8', '4', '5', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '7', '8', '3', '0', '4', '3', '4', '2', '1', '1', '1', '7', '/', '4', '8', '4', '5', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '1', '9', '8', '1', '7', '4', '4', '1', '/', '1', '3', '8', '4', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '4', '2', '9', '7', '7', '9', '2', '3', '4', '7', '/', '6', '0', '5', '6', '8', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '6', '4', '4', '3', '0', '8', '4', '0', '3', '/', '1', '3', '4', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '0', '3', '8', '5', '1', '6', '4', '6', '3', '/', '2', '0', '1', '8', '9', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '9', '5', '5', '6', '4', '8', '7', '7', '1', '9', '7', '/', '2', '4', '2', '2', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment14458765Acc00600 : List (String × SourceJson) := (fragment14458765Field005Key00, fragment14458765Field005Value00) :: fragment14458765Acc00500
noncomputable def fragment14458765Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '8', '9', '0', '9', '7', '3', '0', '5', '6', '9', '1', '/', '4', '8', '4', '5', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '6', '6', '3', '6', '0', '3', '0', '6', '6', '1', '1', '/', '2', '4', '2', '2', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '3', '4', '9', '7', '0', '6', '6', '2', '1', '/', '3', '0', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '8', '0', '1', '6', '3', '7', '2', '1', '5', '4', '1', '1', '/', '4', '8', '4', '5', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '7', '8', '3', '0', '4', '3', '4', '2', '1', '1', '1', '7', '/', '4', '8', '4', '5', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '1', '9', '8', '1', '7', '4', '4', '1', '/', '1', '3', '8', '4', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '4', '2', '9', '7', '7', '9', '2', '3', '4', '7', '/', '6', '0', '5', '6', '8', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '6', '4', '4', '3', '0', '8', '4', '0', '3', '/', '1', '3', '4', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '0', '3', '8', '5', '1', '6', '4', '6', '3', '/', '2', '0', '1', '8', '9', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '9', '5', '5', '6', '4', '8', '7', '7', '1', '9', '7', '/', '2', '4', '2', '2', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment14458765_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment14458765Field005Chars00 ++ tail)) fragment14458765Acc00500 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment14458765Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14458765_object_field_005"
  err.flush

noncomputable def fragment14458765Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14458765Field006Value00 : SourceJson := .str (String.ofList ['2', '7', '4', '8', '8', '0', '3', '4', '2', '0', '3', '9', '7', '1', '2', '1', '4', '5', '5', '1', '5', '1', '2', '5', '3', '1', '5', '6', '6', '3', '3', '0', '2', '6', '6', '7', '6', '0', '7', '5', '8', '9', '8', '0', '5', '3', '9', '4', '1', '1', '/', '5', '3', '7', '9', '6', '1', '7', '3', '1', '6', '5', '5', '4', '1', '8', '3', '3', '0', '3', '3', '3', '2', '4', '7', '0', '2', '9', '4', '9', '9', '4', '3', '9', '0', '1', '9', '7', '5', '7', '8', '0', '5', '0', '3', '0', '0', '4', '2', '9', '0', '4', '0', '2', '8', '0', '1', '5', '0', '4', '7', '6', '0', '4', '3', '8', '7', '8', '4', '0'])
noncomputable def fragment14458765Acc00700 : List (String × SourceJson) := (fragment14458765Field006Key00, fragment14458765Field006Value00) :: fragment14458765Acc00600
noncomputable def fragment14458765Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '7', '4', '8', '8', '0', '3', '4', '2', '0', '3', '9', '7', '1', '2', '1', '4', '5', '5', '1', '5', '1', '2', '5', '3', '1', '5', '6', '6', '3', '3', '0', '2', '6', '6', '7', '6', '0', '7', '5', '8', '9', '8', '0', '5', '3', '9', '4', '1', '1', '/', '5', '3', '7', '9', '6', '1', '7', '3', '1', '6', '5', '5', '4', '1', '8', '3', '3', '0', '3', '3', '3', '2', '4', '7', '0', '2', '9', '4', '9', '9', '4', '3', '9', '0', '1', '9', '7', '5', '7', '8', '0', '5', '0', '3', '0', '0', '4', '2', '9', '0', '4', '0', '2', '8', '0', '1', '5', '0', '4', '7', '6', '0', '4', '3', '8', '7', '8', '4', '0', '"', ',']

theorem object_fragment14458765_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment14458765Field006Chars00 ++ tail)) fragment14458765Acc00600 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment14458765Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14458765_object_field_006"
  err.flush

noncomputable def fragment14458765Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment14458765Field007Value00 : SourceJson := .str (String.ofList ['2', '1', '1', '1', '5', '6', '0', '4', '1', '5', '7', '7', '9', '1', '7', '6', '3', '3', '3', '3', '4', '7', '0', '1', '8', '2', '3', '3', '2', '4', '6', '1', '4', '2', '2', '3', '6', '2', '3', '7', '2', '4', '3', '9', '4', '1', '8', '4', '1', '8', '3', '2', '0', '0', '7', '6', '6', '1', '4', '1', '1', '0', '8', '2', '5', '5', '3', '7', '3', '6', '0', '5', '7', '4', '6', '7', '1', '5', '0', '6', '0', '4', '0', '8', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '2', '7', '9', '3', '5', '9', '6', '4', '1', '9', '8', '2', '6', '4', '8', '4', '9', '6', '8', '2', '9', '6', '1', '0', '3', '4', '1', '5', '3', '8', '5', '9', '1', '5', '7', '7', '9', '8', '5', '5', '7', '9', '8', '5', '1', '7', '1', '6', '2', '2', '3', '3', '1', '6', '3', '6', '7', '5', '0', '4', '3', '7', '0', '8', '9', '9', '8', '2', '6', '1', '6', '7', '0', '3', '7', '1', '4', '4', '9', '6', '1', '2', '6', '0', '5', '5', '2', '8', '8', '6', '0', '2', '4', '8', '8', '9', '7', '0', '5', '4', '0', '8', '4', '6', '4', '1', '6', '1', '5', '3', '2', '3', '9', '3', '5', '5', '3', '1', '1', '7'])
noncomputable def fragment14458765Acc00800 : List (String × SourceJson) := (fragment14458765Field007Key00, fragment14458765Field007Value00) :: fragment14458765Acc00700
noncomputable def fragment14458765Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '1', '1', '5', '6', '0', '4', '1', '5', '7', '7', '9', '1', '7', '6', '3', '3', '3', '3', '4', '7', '0', '1', '8', '2', '3', '3', '2', '4', '6', '1', '4', '2', '2', '3', '6', '2', '3', '7', '2', '4', '3', '9', '4', '1', '8', '4', '1', '8', '3', '2', '0', '0', '7', '6', '6', '1', '4', '1', '1', '0', '8', '2', '5', '5', '3', '7', '3', '6', '0', '5', '7', '4', '6', '7', '1', '5', '0', '6', '0', '4', '0', '8', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '2', '7', '9', '3', '5', '9', '6', '4', '1', '9', '8', '2', '6', '4', '8', '4', '9', '6', '8', '2', '9', '6', '1', '0', '3', '4', '1', '5', '3', '8', '5', '9', '1', '5', '7', '7', '9', '8', '5', '5', '7', '9', '8', '5', '1', '7', '1', '6', '2', '2', '3', '3', '1', '6', '3', '6', '7', '5', '0', '4', '3', '7', '0', '8', '9', '9', '8', '2', '6', '1', '6', '7', '0', '3', '7', '1', '4', '4', '9', '6', '1', '2', '6', '0', '5', '5', '2', '8', '8', '6', '0', '2', '4', '8', '8', '9', '7', '0', '5', '4', '0', '8', '4', '6', '4', '1', '6', '1', '5', '3', '2', '3', '9', '3', '5', '5', '3', '1', '1', '7', '"', ',']

theorem object_fragment14458765_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment14458765Field007Chars00 ++ tail)) fragment14458765Acc00700 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment14458765Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14458765_object_field_007"
  err.flush

noncomputable def fragment14458765Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14458765Field008Value00 : SourceJson := .str (String.ofList ['4', '0', '4', '8', '2', '9', '2', '4', '9', '5'])
noncomputable def fragment14458765Acc00900 : List (String × SourceJson) := (fragment14458765Field008Key00, fragment14458765Field008Value00) :: fragment14458765Acc00800
noncomputable def fragment14458765Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '4', '8', '2', '9', '2', '4', '9', '5', '"', ',']

theorem object_fragment14458765_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment14458765Field008Chars00 ++ tail)) fragment14458765Acc00800 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment14458765Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14458765_object_field_008"
  err.flush

noncomputable def fragment14458765Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment14458765Field009Value00 : SourceJson := .str (String.ofList ['1', '4', '8', '3', '1', '9', '6', '3', '6', '1', '2'])
noncomputable def fragment14458765Acc01000 : List (String × SourceJson) := (fragment14458765Field009Key00, fragment14458765Field009Value00) :: fragment14458765Acc00900
noncomputable def fragment14458765Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '8', '3', '1', '9', '6', '3', '6', '1', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment14458765_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment14458765Field009Chars00 ++ tail)) fragment14458765Acc00900 =
      .ok (.obj (fragment14458765Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment14458765_object_field_009"
  err.flush

noncomputable def fragment14458765Chars : List Char := '{' :: (fragment14458765Field000Chars00 ++ fragment14458765Field001Chars00 ++ fragment14458765Field002Chars00 ++ fragment14458765Field003Chars00 ++ fragment14458765Field004Chars00 ++ fragment14458765Field005Chars00 ++ fragment14458765Field006Chars00 ++ fragment14458765Field007Chars00 ++ fragment14458765Field008Chars00 ++ fragment14458765Field009Chars00)
noncomputable def fragment14458765Value : SourceJson := .obj (fragment14458765Acc01000.reverse)

theorem value_fragment14458765 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 237) (fragment14458765Chars ++ tail) =
      .ok (fragment14458765Value, tail) := by
  have hinput : fragment14458765Chars ++ tail = '{' :: (fragment14458765Field000Chars00 ++ (fragment14458765Field001Chars00 ++ (fragment14458765Field002Chars00 ++ (fragment14458765Field003Chars00 ++ (fragment14458765Field004Chars00 ++ (fragment14458765Field005Chars00 ++ (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment14458765Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 237) (fragment14458765Chars ++ tail) =
        SourceJson.value (fuel + 237) ('{' :: (fragment14458765Field000Chars00 ++ (fragment14458765Field001Chars00 ++ (fragment14458765Field002Chars00 ++ (fragment14458765Field003Chars00 ++ (fragment14458765Field004Chars00 ++ (fragment14458765Field005Chars00 ++ (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 237)) hinput
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment14458765Field000Chars00 ++ (fragment14458765Field001Chars00 ++ (fragment14458765Field002Chars00 ++ (fragment14458765Field003Chars00 ++ (fragment14458765Field004Chars00 ++ (fragment14458765Field005Chars00 ++ (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail)))))))))))) fragment14458765Acc00000 := by rfl
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment14458765Field001Chars00 ++ (fragment14458765Field002Chars00 ++ (fragment14458765Field003Chars00 ++ (fragment14458765Field004Chars00 ++ (fragment14458765Field005Chars00 ++ (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail))))))))))) fragment14458765Acc00100 := object_fragment14458765_field_000 fuel (fragment14458765Field001Chars00 ++ (fragment14458765Field002Chars00 ++ (fragment14458765Field003Chars00 ++ (fragment14458765Field004Chars00 ++ (fragment14458765Field005Chars00 ++ (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment14458765Field002Chars00 ++ (fragment14458765Field003Chars00 ++ (fragment14458765Field004Chars00 ++ (fragment14458765Field005Chars00 ++ (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail)))))))))) fragment14458765Acc00200 := object_fragment14458765_field_001 fuel (fragment14458765Field002Chars00 ++ (fragment14458765Field003Chars00 ++ (fragment14458765Field004Chars00 ++ (fragment14458765Field005Chars00 ++ (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment14458765Field003Chars00 ++ (fragment14458765Field004Chars00 ++ (fragment14458765Field005Chars00 ++ (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail))))))))) fragment14458765Acc00300 := object_fragment14458765_field_002 fuel (fragment14458765Field003Chars00 ++ (fragment14458765Field004Chars00 ++ (fragment14458765Field005Chars00 ++ (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment14458765Field004Chars00 ++ (fragment14458765Field005Chars00 ++ (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail)))))))) fragment14458765Acc00400 := object_fragment14458765_field_003 fuel (fragment14458765Field004Chars00 ++ (fragment14458765Field005Chars00 ++ (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment14458765Field005Chars00 ++ (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail))))))) fragment14458765Acc00500 := object_fragment14458765_field_004 fuel (fragment14458765Field005Chars00 ++ (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail)))))) fragment14458765Acc00600 := object_fragment14458765_field_005 fuel (fragment14458765Field006Chars00 ++ (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail))))) fragment14458765Acc00700 := object_fragment14458765_field_006 fuel (fragment14458765Field007Chars00 ++ (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail)))) fragment14458765Acc00800 := object_fragment14458765_field_007 fuel (fragment14458765Field008Chars00 ++ (fragment14458765Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment14458765Field009Chars00 ++ (tail))) fragment14458765Acc00900 := object_fragment14458765_field_008 fuel (fragment14458765Field009Chars00 ++ (tail))
    _ = .ok (fragment14458765Value, tail) := object_fragment14458765_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6592_before_reader"
  err.flush

noncomputable def chunk6592LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk6592SuffixChars00 : List Char := [',']
noncomputable def chunk6592Chars00 : List Char := chunk6592LeadChars00 ++ fragment14446322Chars ++ chunk6592SuffixChars00
noncomputable def chunk6592Push00 (acc : List SourceJson) : List SourceJson := fragment14446322Value :: acc

noncomputable def chunk6592AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk6592_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 600)
      (SourceJson.white (chunk6592LeadChars00 ++ (fragment14446322Chars ++ rest))) acc =
      (SourceJson.value (fuel + 599) (fragment14446322Chars ++ rest)).bind
        (chunk6592AfterValue00 (fuel + 599) acc) := by rfl

theorem array_chunk6592 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 600) (SourceJson.white (chunk6592Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 599) (SourceJson.white tail) (chunk6592Push00 acc) := by
  have hinput : chunk6592Chars00 ++ tail = chunk6592LeadChars00 ++ (fragment14446322Chars ++ (chunk6592SuffixChars00 ++ tail)) := by
    simp only [chunk6592Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 600) (SourceJson.white (chunk6592Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 600)
          (SourceJson.white (chunk6592LeadChars00 ++ (fragment14446322Chars ++ (chunk6592SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 600) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 599) (fragment14446322Chars ++ (chunk6592SuffixChars00 ++ tail))).bind
        (chunk6592AfterValue00 (fuel + 599) acc) := array_chunk6592_head fuel (chunk6592SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment14446322Value, chunk6592SuffixChars00 ++ tail)).bind
        (chunk6592AfterValue00 (fuel + 599) acc) :=
      congrArg (fun result => result.bind (chunk6592AfterValue00 (fuel + 599) acc))
        (value_fragment14446322 (fuel + 266) (chunk6592SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 599) (SourceJson.white tail) (chunk6592Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6592_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6593_before_reader"
  err.flush

noncomputable def chunk6593LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk6593SuffixChars00 : List Char := [',']
noncomputable def chunk6593Chars00 : List Char := chunk6593LeadChars00 ++ fragment14448161Chars ++ chunk6593SuffixChars00
noncomputable def chunk6593Push00 (acc : List SourceJson) : List SourceJson := fragment14448161Value :: acc

noncomputable def chunk6593AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk6593_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 599)
      (SourceJson.white (chunk6593LeadChars00 ++ (fragment14448161Chars ++ rest))) acc =
      (SourceJson.value (fuel + 598) (fragment14448161Chars ++ rest)).bind
        (chunk6593AfterValue00 (fuel + 598) acc) := by rfl

theorem array_chunk6593 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 599) (SourceJson.white (chunk6593Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 598) (SourceJson.white tail) (chunk6593Push00 acc) := by
  have hinput : chunk6593Chars00 ++ tail = chunk6593LeadChars00 ++ (fragment14448161Chars ++ (chunk6593SuffixChars00 ++ tail)) := by
    simp only [chunk6593Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 599) (SourceJson.white (chunk6593Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 599)
          (SourceJson.white (chunk6593LeadChars00 ++ (fragment14448161Chars ++ (chunk6593SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 599) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 598) (fragment14448161Chars ++ (chunk6593SuffixChars00 ++ tail))).bind
        (chunk6593AfterValue00 (fuel + 598) acc) := array_chunk6593_head fuel (chunk6593SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment14448161Value, chunk6593SuffixChars00 ++ tail)).bind
        (chunk6593AfterValue00 (fuel + 598) acc) :=
      congrArg (fun result => result.bind (chunk6593AfterValue00 (fuel + 598) acc))
        (value_fragment14448161 (fuel + 320) (chunk6593SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 598) (SourceJson.white tail) (chunk6593Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6593_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6594_before_reader"
  err.flush

noncomputable def chunk6594LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk6594SuffixChars00 : List Char := [',']
noncomputable def chunk6594Chars00 : List Char := chunk6594LeadChars00 ++ fragment14449800Chars ++ chunk6594SuffixChars00
noncomputable def chunk6594Push00 (acc : List SourceJson) : List SourceJson := fragment14449800Value :: acc

noncomputable def chunk6594AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk6594_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 598)
      (SourceJson.white (chunk6594LeadChars00 ++ (fragment14449800Chars ++ rest))) acc =
      (SourceJson.value (fuel + 597) (fragment14449800Chars ++ rest)).bind
        (chunk6594AfterValue00 (fuel + 597) acc) := by rfl

theorem array_chunk6594 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 598) (SourceJson.white (chunk6594Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 597) (SourceJson.white tail) (chunk6594Push00 acc) := by
  have hinput : chunk6594Chars00 ++ tail = chunk6594LeadChars00 ++ (fragment14449800Chars ++ (chunk6594SuffixChars00 ++ tail)) := by
    simp only [chunk6594Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 598) (SourceJson.white (chunk6594Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 598)
          (SourceJson.white (chunk6594LeadChars00 ++ (fragment14449800Chars ++ (chunk6594SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 598) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 597) (fragment14449800Chars ++ (chunk6594SuffixChars00 ++ tail))).bind
        (chunk6594AfterValue00 (fuel + 597) acc) := array_chunk6594_head fuel (chunk6594SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment14449800Value, chunk6594SuffixChars00 ++ tail)).bind
        (chunk6594AfterValue00 (fuel + 597) acc) :=
      congrArg (fun result => result.bind (chunk6594AfterValue00 (fuel + 597) acc))
        (value_fragment14449800 (fuel + 317) (chunk6594SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 597) (SourceJson.white tail) (chunk6594Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6594_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6595_before_reader"
  err.flush

noncomputable def chunk6595LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk6595SuffixChars00 : List Char := [',']
noncomputable def chunk6595Chars00 : List Char := chunk6595LeadChars00 ++ fragment14451507Chars ++ chunk6595SuffixChars00
noncomputable def chunk6595Push00 (acc : List SourceJson) : List SourceJson := fragment14451507Value :: acc

noncomputable def chunk6595AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk6595_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 597)
      (SourceJson.white (chunk6595LeadChars00 ++ (fragment14451507Chars ++ rest))) acc =
      (SourceJson.value (fuel + 596) (fragment14451507Chars ++ rest)).bind
        (chunk6595AfterValue00 (fuel + 596) acc) := by rfl

theorem array_chunk6595 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 597) (SourceJson.white (chunk6595Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 596) (SourceJson.white tail) (chunk6595Push00 acc) := by
  have hinput : chunk6595Chars00 ++ tail = chunk6595LeadChars00 ++ (fragment14451507Chars ++ (chunk6595SuffixChars00 ++ tail)) := by
    simp only [chunk6595Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 597) (SourceJson.white (chunk6595Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 597)
          (SourceJson.white (chunk6595LeadChars00 ++ (fragment14451507Chars ++ (chunk6595SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 597) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 596) (fragment14451507Chars ++ (chunk6595SuffixChars00 ++ tail))).bind
        (chunk6595AfterValue00 (fuel + 596) acc) := array_chunk6595_head fuel (chunk6595SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment14451507Value, chunk6595SuffixChars00 ++ tail)).bind
        (chunk6595AfterValue00 (fuel + 596) acc) :=
      congrArg (fun result => result.bind (chunk6595AfterValue00 (fuel + 596) acc))
        (value_fragment14451507 (fuel + 139) (chunk6595SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 596) (SourceJson.white tail) (chunk6595Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6595_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6596_before_reader"
  err.flush

noncomputable def chunk6596LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk6596SuffixChars00 : List Char := [',']
noncomputable def chunk6596Chars00 : List Char := chunk6596LeadChars00 ++ fragment14453560Chars ++ chunk6596SuffixChars00
noncomputable def chunk6596Push00 (acc : List SourceJson) : List SourceJson := fragment14453560Value :: acc

noncomputable def chunk6596AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk6596_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 596)
      (SourceJson.white (chunk6596LeadChars00 ++ (fragment14453560Chars ++ rest))) acc =
      (SourceJson.value (fuel + 595) (fragment14453560Chars ++ rest)).bind
        (chunk6596AfterValue00 (fuel + 595) acc) := by rfl

theorem array_chunk6596 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 596) (SourceJson.white (chunk6596Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 595) (SourceJson.white tail) (chunk6596Push00 acc) := by
  have hinput : chunk6596Chars00 ++ tail = chunk6596LeadChars00 ++ (fragment14453560Chars ++ (chunk6596SuffixChars00 ++ tail)) := by
    simp only [chunk6596Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 596) (SourceJson.white (chunk6596Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 596)
          (SourceJson.white (chunk6596LeadChars00 ++ (fragment14453560Chars ++ (chunk6596SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 596) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 595) (fragment14453560Chars ++ (chunk6596SuffixChars00 ++ tail))).bind
        (chunk6596AfterValue00 (fuel + 595) acc) := array_chunk6596_head fuel (chunk6596SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment14453560Value, chunk6596SuffixChars00 ++ tail)).bind
        (chunk6596AfterValue00 (fuel + 595) acc) :=
      congrArg (fun result => result.bind (chunk6596AfterValue00 (fuel + 595) acc))
        (value_fragment14453560 (fuel + 283) (chunk6596SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 595) (SourceJson.white tail) (chunk6596Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6596_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6597_before_reader"
  err.flush

noncomputable def chunk6597LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk6597SuffixChars00 : List Char := [',']
noncomputable def chunk6597Chars00 : List Char := chunk6597LeadChars00 ++ fragment14455343Chars ++ chunk6597SuffixChars00
noncomputable def chunk6597Push00 (acc : List SourceJson) : List SourceJson := fragment14455343Value :: acc

noncomputable def chunk6597AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk6597_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 595)
      (SourceJson.white (chunk6597LeadChars00 ++ (fragment14455343Chars ++ rest))) acc =
      (SourceJson.value (fuel + 594) (fragment14455343Chars ++ rest)).bind
        (chunk6597AfterValue00 (fuel + 594) acc) := by rfl

theorem array_chunk6597 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 595) (SourceJson.white (chunk6597Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 594) (SourceJson.white tail) (chunk6597Push00 acc) := by
  have hinput : chunk6597Chars00 ++ tail = chunk6597LeadChars00 ++ (fragment14455343Chars ++ (chunk6597SuffixChars00 ++ tail)) := by
    simp only [chunk6597Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 595) (SourceJson.white (chunk6597Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 595)
          (SourceJson.white (chunk6597LeadChars00 ++ (fragment14455343Chars ++ (chunk6597SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 595) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 594) (fragment14455343Chars ++ (chunk6597SuffixChars00 ++ tail))).bind
        (chunk6597AfterValue00 (fuel + 594) acc) := array_chunk6597_head fuel (chunk6597SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment14455343Value, chunk6597SuffixChars00 ++ tail)).bind
        (chunk6597AfterValue00 (fuel + 594) acc) :=
      congrArg (fun result => result.bind (chunk6597AfterValue00 (fuel + 594) acc))
        (value_fragment14455343 (fuel + 335) (chunk6597SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 594) (SourceJson.white tail) (chunk6597Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6597_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6598_before_reader"
  err.flush

noncomputable def chunk6598LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk6598SuffixChars00 : List Char := [',']
noncomputable def chunk6598Chars00 : List Char := chunk6598LeadChars00 ++ fragment14456998Chars ++ chunk6598SuffixChars00
noncomputable def chunk6598Push00 (acc : List SourceJson) : List SourceJson := fragment14456998Value :: acc

noncomputable def chunk6598AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk6598_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 594)
      (SourceJson.white (chunk6598LeadChars00 ++ (fragment14456998Chars ++ rest))) acc =
      (SourceJson.value (fuel + 593) (fragment14456998Chars ++ rest)).bind
        (chunk6598AfterValue00 (fuel + 593) acc) := by rfl

theorem array_chunk6598 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 594) (SourceJson.white (chunk6598Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 593) (SourceJson.white tail) (chunk6598Push00 acc) := by
  have hinput : chunk6598Chars00 ++ tail = chunk6598LeadChars00 ++ (fragment14456998Chars ++ (chunk6598SuffixChars00 ++ tail)) := by
    simp only [chunk6598Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 594) (SourceJson.white (chunk6598Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 594)
          (SourceJson.white (chunk6598LeadChars00 ++ (fragment14456998Chars ++ (chunk6598SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 594) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 593) (fragment14456998Chars ++ (chunk6598SuffixChars00 ++ tail))).bind
        (chunk6598AfterValue00 (fuel + 593) acc) := array_chunk6598_head fuel (chunk6598SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment14456998Value, chunk6598SuffixChars00 ++ tail)).bind
        (chunk6598AfterValue00 (fuel + 593) acc) :=
      congrArg (fun result => result.bind (chunk6598AfterValue00 (fuel + 593) acc))
        (value_fragment14456998 (fuel + 253) (chunk6598SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 593) (SourceJson.white tail) (chunk6598Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6598_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6599_before_reader"
  err.flush

noncomputable def chunk6599LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk6599SuffixChars00 : List Char := ['\r', '\n', ' ', ' ', ']']
noncomputable def chunk6599Chars00 : List Char := chunk6599LeadChars00 ++ fragment14458765Chars ++ chunk6599SuffixChars00
noncomputable def chunk6599Push00 (acc : List SourceJson) : List SourceJson := fragment14458765Value :: acc

noncomputable def chunk6599AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk6599_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 593)
      (SourceJson.white (chunk6599LeadChars00 ++ (fragment14458765Chars ++ rest))) acc =
      (SourceJson.value (fuel + 592) (fragment14458765Chars ++ rest)).bind
        (chunk6599AfterValue00 (fuel + 592) acc) := by rfl

theorem array_chunk6599 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 593) (SourceJson.white (chunk6599Chars00 ++ tail)) acc =
      .ok (.arr ((chunk6599Push00 acc).reverse), tail) := by
  have hinput : chunk6599Chars00 ++ tail = chunk6599LeadChars00 ++ (fragment14458765Chars ++ (chunk6599SuffixChars00 ++ tail)) := by
    simp only [chunk6599Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 593) (SourceJson.white (chunk6599Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 593)
          (SourceJson.white (chunk6599LeadChars00 ++ (fragment14458765Chars ++ (chunk6599SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 593) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 592) (fragment14458765Chars ++ (chunk6599SuffixChars00 ++ tail))).bind
        (chunk6599AfterValue00 (fuel + 592) acc) := array_chunk6599_head fuel (chunk6599SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment14458765Value, chunk6599SuffixChars00 ++ tail)).bind
        (chunk6599AfterValue00 (fuel + 592) acc) :=
      congrArg (fun result => result.bind (chunk6599AfterValue00 (fuel + 592) acc))
        (value_fragment14458765 (fuel + 355) (chunk6599SuffixChars00 ++ tail))
    _ = .ok (.arr ((chunk6599Push00 acc).reverse), tail) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk6599_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk6592Chars00 ++ chunk6593Chars00 ++ chunk6594Chars00 ++ chunk6595Chars00 ++ chunk6596Chars00 ++ chunk6597Chars00 ++ chunk6598Chars00 ++ chunk6599Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk6599Push00 (chunk6598Push00 (chunk6597Push00 (chunk6596Push00 (chunk6595Push00 (chunk6594Push00 (chunk6593Push00 (chunk6592Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 600) (SourceJson.white (blockChars ++ tail)) acc =
      .ok (.arr ((blockPush acc).reverse), tail) := by
  have hinput : blockChars ++ tail = chunk6592Chars00 ++ (chunk6593Chars00 ++ (chunk6594Chars00 ++ (chunk6595Chars00 ++ (chunk6596Chars00 ++ (chunk6597Chars00 ++ (chunk6598Chars00 ++ (chunk6599Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 600) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 600) (SourceJson.white (chunk6592Chars00 ++ (chunk6593Chars00 ++ (chunk6594Chars00 ++ (chunk6595Chars00 ++ (chunk6596Chars00 ++ (chunk6597Chars00 ++ (chunk6598Chars00 ++ (chunk6599Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 600) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 599) (SourceJson.white (chunk6593Chars00 ++ (chunk6594Chars00 ++ (chunk6595Chars00 ++ (chunk6596Chars00 ++ (chunk6597Chars00 ++ (chunk6598Chars00 ++ (chunk6599Chars00 ++ (tail))))))))) (chunk6592Push00 (acc)) := array_chunk6592 fuel (chunk6593Chars00 ++ (chunk6594Chars00 ++ (chunk6595Chars00 ++ (chunk6596Chars00 ++ (chunk6597Chars00 ++ (chunk6598Chars00 ++ (chunk6599Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 598) (SourceJson.white (chunk6594Chars00 ++ (chunk6595Chars00 ++ (chunk6596Chars00 ++ (chunk6597Chars00 ++ (chunk6598Chars00 ++ (chunk6599Chars00 ++ (tail)))))))) (chunk6593Push00 (chunk6592Push00 (acc))) := array_chunk6593 fuel (chunk6594Chars00 ++ (chunk6595Chars00 ++ (chunk6596Chars00 ++ (chunk6597Chars00 ++ (chunk6598Chars00 ++ (chunk6599Chars00 ++ (tail))))))) (chunk6592Push00 (acc))
    _ = SourceJson.array (fuel + 597) (SourceJson.white (chunk6595Chars00 ++ (chunk6596Chars00 ++ (chunk6597Chars00 ++ (chunk6598Chars00 ++ (chunk6599Chars00 ++ (tail))))))) (chunk6594Push00 (chunk6593Push00 (chunk6592Push00 (acc)))) := array_chunk6594 fuel (chunk6595Chars00 ++ (chunk6596Chars00 ++ (chunk6597Chars00 ++ (chunk6598Chars00 ++ (chunk6599Chars00 ++ (tail)))))) (chunk6593Push00 (chunk6592Push00 (acc)))
    _ = SourceJson.array (fuel + 596) (SourceJson.white (chunk6596Chars00 ++ (chunk6597Chars00 ++ (chunk6598Chars00 ++ (chunk6599Chars00 ++ (tail)))))) (chunk6595Push00 (chunk6594Push00 (chunk6593Push00 (chunk6592Push00 (acc))))) := array_chunk6595 fuel (chunk6596Chars00 ++ (chunk6597Chars00 ++ (chunk6598Chars00 ++ (chunk6599Chars00 ++ (tail))))) (chunk6594Push00 (chunk6593Push00 (chunk6592Push00 (acc))))
    _ = SourceJson.array (fuel + 595) (SourceJson.white (chunk6597Chars00 ++ (chunk6598Chars00 ++ (chunk6599Chars00 ++ (tail))))) (chunk6596Push00 (chunk6595Push00 (chunk6594Push00 (chunk6593Push00 (chunk6592Push00 (acc)))))) := array_chunk6596 fuel (chunk6597Chars00 ++ (chunk6598Chars00 ++ (chunk6599Chars00 ++ (tail)))) (chunk6595Push00 (chunk6594Push00 (chunk6593Push00 (chunk6592Push00 (acc)))))
    _ = SourceJson.array (fuel + 594) (SourceJson.white (chunk6598Chars00 ++ (chunk6599Chars00 ++ (tail)))) (chunk6597Push00 (chunk6596Push00 (chunk6595Push00 (chunk6594Push00 (chunk6593Push00 (chunk6592Push00 (acc))))))) := array_chunk6597 fuel (chunk6598Chars00 ++ (chunk6599Chars00 ++ (tail))) (chunk6596Push00 (chunk6595Push00 (chunk6594Push00 (chunk6593Push00 (chunk6592Push00 (acc))))))
    _ = SourceJson.array (fuel + 593) (SourceJson.white (chunk6599Chars00 ++ (tail))) (chunk6598Push00 (chunk6597Push00 (chunk6596Push00 (chunk6595Push00 (chunk6594Push00 (chunk6593Push00 (chunk6592Push00 (acc)))))))) := array_chunk6598 fuel (chunk6599Chars00 ++ (tail)) (chunk6597Push00 (chunk6596Push00 (chunk6595Push00 (chunk6594Push00 (chunk6593Push00 (chunk6592Push00 (acc)))))))
    _ = .ok (.arr ((blockPush acc).reverse), tail) := array_chunk6599 fuel (tail) (chunk6598Push00 (chunk6597Push00 (chunk6596Push00 (chunk6595Push00 (chunk6594Push00 (chunk6593Push00 (chunk6592Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 14446316).take 14072 = blockChars := by rfl

theorem block_original_split : sourceRest 14446316 = blockChars ++ sourceRest 14460388 := by
  calc
    sourceRest 14446316 = (sourceRest 14446316).take 14072 ++ (sourceRest 14446316).drop 14072 :=
      (List.take_append_drop 14072 (sourceRest 14446316)).symm
    _ = blockChars ++ (sourceRest 14446316).drop 14072 :=
      congrArg (fun part => part ++ (sourceRest 14446316).drop 14072) block_original_prefix
    _ = blockChars ++ sourceRest 14460388 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 14446316 14072)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 600) (SourceJson.white (sourceRest 14446316)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 14460388) :=
  (congrArg (fun chars => SourceJson.array (fuel + 600) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 14460388) acc)

#print axioms object_fragment14446322_field_000
#print axioms object_fragment14446322_field_001
#print axioms object_fragment14446322_field_002
#print axioms object_fragment14446322_field_003
#print axioms object_fragment14446322_field_004
#print axioms object_fragment14446322_field_005
#print axioms object_fragment14446322_field_006
#print axioms object_fragment14446322_field_007
#print axioms object_fragment14446322_field_008
#print axioms object_fragment14446322_field_009
#print axioms value_fragment14446322
#print axioms object_fragment14448161_field_000
#print axioms object_fragment14448161_field_001
#print axioms object_fragment14448161_field_002
#print axioms object_fragment14448161_field_003
#print axioms object_fragment14448161_field_004
#print axioms object_fragment14448161_field_005
#print axioms object_fragment14448161_field_006
#print axioms object_fragment14448161_field_007
#print axioms object_fragment14448161_field_008
#print axioms object_fragment14448161_field_009
#print axioms value_fragment14448161
#print axioms object_fragment14449800_field_000
#print axioms object_fragment14449800_field_001
#print axioms object_fragment14449800_field_002
#print axioms object_fragment14449800_field_003
#print axioms object_fragment14449800_field_004
#print axioms object_fragment14449800_field_005
#print axioms object_fragment14449800_field_006
#print axioms object_fragment14449800_field_007
#print axioms object_fragment14449800_field_008
#print axioms object_fragment14449800_field_009
#print axioms value_fragment14449800
#print axioms object_fragment14451507_field_000
#print axioms object_fragment14451507_field_001
#print axioms object_fragment14451507_field_002
#print axioms object_fragment14451507_field_003
#print axioms object_fragment14451507_field_004
#print axioms object_fragment14451507_field_005
#print axioms object_fragment14451507_field_006
#print axioms object_fragment14451507_field_007
#print axioms object_fragment14451507_field_008
#print axioms object_fragment14451507_field_009
#print axioms value_fragment14451507
#print axioms object_fragment14453560_field_000
#print axioms object_fragment14453560_field_001
#print axioms object_fragment14453560_field_002
#print axioms object_fragment14453560_field_003
#print axioms object_fragment14453560_field_004
#print axioms object_fragment14453560_field_005
#print axioms object_fragment14453560_field_006
#print axioms object_fragment14453560_field_007
#print axioms object_fragment14453560_field_008
#print axioms object_fragment14453560_field_009
#print axioms value_fragment14453560
#print axioms object_fragment14455343_field_000
#print axioms object_fragment14455343_field_001
#print axioms object_fragment14455343_field_002
#print axioms object_fragment14455343_field_003
#print axioms object_fragment14455343_field_004
#print axioms object_fragment14455343_field_005
#print axioms object_fragment14455343_field_006
#print axioms object_fragment14455343_field_007
#print axioms object_fragment14455343_field_008
#print axioms object_fragment14455343_field_009
#print axioms value_fragment14455343
#print axioms object_fragment14456998_field_000
#print axioms object_fragment14456998_field_001
#print axioms object_fragment14456998_field_002
#print axioms object_fragment14456998_field_003
#print axioms object_fragment14456998_field_004
#print axioms object_fragment14456998_field_005
#print axioms object_fragment14456998_field_006
#print axioms object_fragment14456998_field_007
#print axioms object_fragment14456998_field_008
#print axioms object_fragment14456998_field_009
#print axioms value_fragment14456998
#print axioms object_fragment14458765_field_000
#print axioms object_fragment14458765_field_001
#print axioms object_fragment14458765_field_002
#print axioms object_fragment14458765_field_003
#print axioms object_fragment14458765_field_004
#print axioms object_fragment14458765_field_005
#print axioms object_fragment14458765_field_006
#print axioms object_fragment14458765_field_007
#print axioms object_fragment14458765_field_008
#print axioms object_fragment14458765_field_009
#print axioms value_fragment14458765
#print axioms array_chunk6592_head
#print axioms array_chunk6592
#print axioms array_chunk6593_head
#print axioms array_chunk6593
#print axioms array_chunk6594_head
#print axioms array_chunk6594
#print axioms array_chunk6595_head
#print axioms array_chunk6595
#print axioms array_chunk6596_head
#print axioms array_chunk6596
#print axioms array_chunk6597_head
#print axioms array_chunk6597
#print axioms array_chunk6598_head
#print axioms array_chunk6598
#print axioms array_chunk6599_head
#print axioms array_chunk6599
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock824

end ImbalancedChen.P2OriginalSaving19Geometry12ScalableParsing
