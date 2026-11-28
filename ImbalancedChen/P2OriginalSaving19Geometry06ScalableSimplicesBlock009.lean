import ImbalancedChen.P2OriginalSaving19Geometry06ScalableInput

/-! Original simplices grouped chunk transitions, including exact compact-input binding.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesBlock009

noncomputable def fragment0261427Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0261427Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0261427Field000Value00 : SourceJson := .number (String.ofList ['7', '2'])
noncomputable def fragment0261427Acc00100 : List (String × SourceJson) := (fragment0261427Field000Key00, fragment0261427Field000Value00) :: fragment0261427Acc00000
noncomputable def fragment0261427Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '2', ',']

theorem object_fragment0261427_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 381) (SourceJson.white (fragment0261427Field000Chars00 ++ tail)) fragment0261427Acc00000 =
      SourceJson.object (fuel + 380) (SourceJson.white tail) fragment0261427Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261427_object_field_000"
  err.flush

noncomputable def fragment0261427Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0261427Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0261427Acc00200 : List (String × SourceJson) := (fragment0261427Field001Key00, fragment0261427Field001Value00) :: fragment0261427Acc00100
noncomputable def fragment0261427Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0261427_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 380) (SourceJson.white (fragment0261427Field001Chars00 ++ tail)) fragment0261427Acc00100 =
      SourceJson.object (fuel + 379) (SourceJson.white tail) fragment0261427Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261427_object_field_001"
  err.flush

noncomputable def fragment0261427Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0261427Field002Value00 : SourceJson := .str (String.ofList ['2', '1', '7', '0', '3', '3', '0', '9', '8', '4', '6', '8', '9', '0', '1', '4', '1', '7', '3', '5', '4', '6', '6', '8', '6', '2', '4', '0', '1', '9', '1', '2', '1', '5', '6', '3', '3', '/', '3', '2', '6', '6', '6', '6', '0', '0', '1', '6', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0261427Acc00300 : List (String × SourceJson) := (fragment0261427Field002Key00, fragment0261427Field002Value00) :: fragment0261427Acc00200
noncomputable def fragment0261427Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '1', '7', '0', '3', '3', '0', '9', '8', '4', '6', '8', '9', '0', '1', '4', '1', '7', '3', '5', '4', '6', '6', '8', '6', '2', '4', '0', '1', '9', '1', '2', '1', '5', '6', '3', '3', '/', '3', '2', '6', '6', '6', '6', '0', '0', '1', '6', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0261427_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 379) (SourceJson.white (fragment0261427Field002Chars00 ++ tail)) fragment0261427Acc00200 =
      SourceJson.object (fuel + 378) (SourceJson.white tail) fragment0261427Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261427_object_field_002"
  err.flush

noncomputable def fragment0261427Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0261427Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0261427Acc00400 : List (String × SourceJson) := (fragment0261427Field003Key00, fragment0261427Field003Value00) :: fragment0261427Acc00300
noncomputable def fragment0261427Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0261427_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 378) (SourceJson.white (fragment0261427Field003Chars00 ++ tail)) fragment0261427Acc00300 =
      SourceJson.object (fuel + 377) (SourceJson.white tail) fragment0261427Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261427_object_field_003"
  err.flush

noncomputable def fragment0261427Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0261427Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0261427Acc00500 : List (String × SourceJson) := (fragment0261427Field004Key00, fragment0261427Field004Value00) :: fragment0261427Acc00400
noncomputable def fragment0261427Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0261427_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 377) (SourceJson.white (fragment0261427Field004Chars00 ++ tail)) fragment0261427Acc00400 =
      SourceJson.object (fuel + 376) (SourceJson.white tail) fragment0261427Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261427_object_field_004"
  err.flush

noncomputable def fragment0261427Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0261427Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '7', '5', '3', '1', '2', '1', '7', '3', '2', '0', '9', '7', '7', '6', '1', '1', '4', '5', '9', '7', '/', '3', '1', '9', '9', '1', '8', '2', '3', '6', '8', '2', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '2', '4', '2', '0', '4', '8', '7', '1', '6', '5', '5', '2', '6', '8', '2', '1', '7', '3', '/', '4', '5', '7', '0', '2', '6', '0', '5', '2', '6', '0', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '7', '2', '3', '6', '2', '0', '3', '7', '5', '3', '2', '1', '9', '7', '2', '1', '/', '6', '9', '5', '4', '7', '4', '4', '2', '7', '8', '7', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '0', '5', '9', '9', '3', '6', '3', '9', '6', '7', '4', '4', '2', '4', '9', '5', '5', '7', '/', '1', '0', '6', '6', '3', '9', '4', '1', '2', '2', '7', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '2', '6', '8', '1', '4', '1', '2', '5', '1', '5', '1', '9', '3', '6', '2', '7', '9', '/', '3', '5', '5', '4', '6', '4', '7', '0', '7', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '5', '0', '5', '0', '2', '8', '7', '9', '2', '5', '0', '8', '1', '2', '7', '1', '1', '/', '1', '4', '5', '4', '1', '7', '3', '8', '0', '3', '7', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '5', '6', '7', '3', '8', '0', '7', '8', '9', '4', '7', '5', '8', '2', '4', '1', '/', '2', '9', '0', '8', '3', '4', '7', '6', '0', '7', '4', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '4', '5', '6', '8', '8', '5', '2', '5', '4', '8', '4', '1', '2', '4', '2', '6', '1', '/', '2', '9', '0', '8', '3', '4', '7', '6', '0', '7', '4', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '8', '7', '5', '8', '6', '5', '3', '4', '5', '4', '4', '2', '1', '7', '8', '2', '1', '/', '2', '9', '0', '8', '3', '4', '7', '6', '0', '7', '4', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '3', '1', '3', '6', '8', '3', '5', '9', '0', '2', '4', '3', '0', '4', '4', '3', '1', '/', '4', '5', '7', '0', '2', '6', '0', '5', '2', '6', '0', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0261427Acc00600 : List (String × SourceJson) := (fragment0261427Field005Key00, fragment0261427Field005Value00) :: fragment0261427Acc00500
noncomputable def fragment0261427Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '3', '1', '2', '1', '7', '3', '2', '0', '9', '7', '7', '6', '1', '1', '4', '5', '9', '7', '/', '3', '1', '9', '9', '1', '8', '2', '3', '6', '8', '2', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '2', '4', '2', '0', '4', '8', '7', '1', '6', '5', '5', '2', '6', '8', '2', '1', '7', '3', '/', '4', '5', '7', '0', '2', '6', '0', '5', '2', '6', '0', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '7', '2', '3', '6', '2', '0', '3', '7', '5', '3', '2', '1', '9', '7', '2', '1', '/', '6', '9', '5', '4', '7', '4', '4', '2', '7', '8', '7', '9', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '0', '5', '9', '9', '3', '6', '3', '9', '6', '7', '4', '4', '2', '4', '9', '5', '5', '7', '/', '1', '0', '6', '6', '3', '9', '4', '1', '2', '2', '7', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '2', '6', '8', '1', '4', '1', '2', '5', '1', '5', '1', '9', '3', '6', '2', '7', '9', '/', '3', '5', '5', '4', '6', '4', '7', '0', '7', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '5', '0', '5', '0', '2', '8', '7', '9', '2', '5', '0', '8', '1', '2', '7', '1', '1', '/', '1', '4', '5', '4', '1', '7', '3', '8', '0', '3', '7', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '5', '6', '7', '3', '8', '0', '7', '8', '9', '4', '7', '5', '8', '2', '4', '1', '/', '2', '9', '0', '8', '3', '4', '7', '6', '0', '7', '4', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '4', '5', '6', '8', '8', '5', '2', '5', '4', '8', '4', '1', '2', '4', '2', '6', '1', '/', '2', '9', '0', '8', '3', '4', '7', '6', '0', '7', '4', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '8', '7', '5', '8', '6', '5', '3', '4', '5', '4', '4', '2', '1', '7', '8', '2', '1', '/', '2', '9', '0', '8', '3', '4', '7', '6', '0', '7', '4', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '3', '1', '3', '6', '8', '3', '5', '9', '0', '2', '4', '3', '0', '4', '4', '3', '1', '/', '4', '5', '7', '0', '2', '6', '0', '5', '2', '6', '0', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0261427_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 376) (SourceJson.white (fragment0261427Field005Chars00 ++ tail)) fragment0261427Acc00500 =
      SourceJson.object (fuel + 375) (SourceJson.white tail) fragment0261427Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261427_object_field_005"
  err.flush

noncomputable def fragment0261427Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0261427Field006Value00 : SourceJson := .str (String.ofList ['1', '2', '1', '5', '0', '3', '3', '9', '2', '2', '5', '1', '5', '6', '5', '7', '7', '1', '5', '1', '9', '0', '4', '2', '6', '2', '6', '3', '6', '5', '6', '8', '4', '0', '2', '9', '8', '0', '0', '1', '3', '3', '9', '9', '0', '/', '6', '8', '1', '0', '5', '8', '2', '3', '4', '7', '8', '7', '8', '4', '3', '0', '8', '9', '8', '2', '1', '3', '6', '4', '3', '5', '9', '3', '7', '7', '3', '8', '4', '5', '3', '2', '9', '2', '8', '1', '3', '7', '2', '6', '8', '7', '8', '0', '8', '4', '8', '3', '8', '4', '6', '8', '9', '3', '2', '1', '7'])
noncomputable def fragment0261427Acc00700 : List (String × SourceJson) := (fragment0261427Field006Key00, fragment0261427Field006Value00) :: fragment0261427Acc00600
noncomputable def fragment0261427Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '1', '5', '0', '3', '3', '9', '2', '2', '5', '1', '5', '6', '5', '7', '7', '1', '5', '1', '9', '0', '4', '2', '6', '2', '6', '3', '6', '5', '6', '8', '4', '0', '2', '9', '8', '0', '0', '1', '3', '3', '9', '9', '0', '/', '6', '8', '1', '0', '5', '8', '2', '3', '4', '7', '8', '7', '8', '4', '3', '0', '8', '9', '8', '2', '1', '3', '6', '4', '3', '5', '9', '3', '7', '7', '3', '8', '4', '5', '3', '2', '9', '2', '8', '1', '3', '7', '2', '6', '8', '7', '8', '0', '8', '4', '8', '3', '8', '4', '6', '8', '9', '3', '2', '1', '7', '"', ',']

theorem object_fragment0261427_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 375) (SourceJson.white (fragment0261427Field006Chars00 ++ tail)) fragment0261427Acc00600 =
      SourceJson.object (fuel + 374) (SourceJson.white tail) fragment0261427Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261427_object_field_006"
  err.flush

noncomputable def fragment0261427Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0261427Field007Value00 : SourceJson := .str (String.ofList ['2', '4', '7', '4', '8', '1', '1', '9', '8', '0', '9', '8', '3', '5', '3', '0', '4', '3', '0', '7', '6', '7', '1', '9', '9', '7', '9', '1', '3', '7', '1', '4', '2', '4', '5', '4', '9', '1', '7', '2', '0', '8', '4', '2', '8', '9', '5', '2', '1', '5', '4', '4', '7', '9', '2', '5', '5', '1', '2', '3', '4', '4', '8', '3', '6', '6', '8', '4', '3', '8', '1', '2', '6', '1', '2', '3', '0', '1', '8', '1', '4', '8', '6', '9', '1', '1', '3', '0', '7', '3', '0', '5', '5', '6', '8', '5', '7', '1', '6', '6', '9', '3', '2', '0', '8', '8', '5', '6', '3', '1', '0', '0', '9', '7', '5', '5', '7', '5', '7', '8', '0', '1', '2', '9', '5', '3', '6', '8', '6', '4', '1', '6', '8', '0', '8', '8', '8', '1', '7', '7', '2', '1', '0', '9', '2', '1', '8', '5', '2', '9', '8', '0', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '2', '5', '2', '3', '3', '7', '3', '5', '2', '5', '1', '3', '1', '0', '4', '5', '5', '1', '5', '0', '5', '5', '0', '6', '2', '7', '3', '5', '5', '1', '8', '9', '5', '7', '8', '3', '8', '7', '7', '9', '3', '3', '7', '6', '3', '1', '1', '8', '7', '0', '5', '3', '5', '2', '5', '8', '5', '9', '8', '0', '5', '0', '6', '0', '4', '9', '7', '3', '7', '5', '5', '3', '3', '3', '1', '9', '0', '0', '8', '3', '8', '4', '4', '2', '0', '0', '1', '0', '6', '5', '5', '5', '5', '4', '1', '7', '4', '1', '4', '8', '1', '0', '3', '1', '4', '0', '7', '1', '7', '2', '3', '1', '6', '2', '3', '3', '3', '8', '9', '3', '9', '8', '5', '6', '4', '3', '4', '2', '5', '9', '8', '8', '6', '9', '8', '5', '5', '5', '7', '7', '9', '8', '8', '5', '2', '7', '8', '9', '9', '6', '4', '7', '9', '9', '6', '9', '9', '1', '9', '5', '3', '7', '8', '4', '3', '0', '9', '6', '0', '6', '0', '6', '7', '3', '8', '6', '7', '2', '0', '0', '1', '0', '1', '5', '7', '3', '9', '1', '2', '0', '8', '3'])
noncomputable def fragment0261427Acc00800 : List (String × SourceJson) := (fragment0261427Field007Key00, fragment0261427Field007Value00) :: fragment0261427Acc00700
noncomputable def fragment0261427Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '4', '7', '4', '8', '1', '1', '9', '8', '0', '9', '8', '3', '5', '3', '0', '4', '3', '0', '7', '6', '7', '1', '9', '9', '7', '9', '1', '3', '7', '1', '4', '2', '4', '5', '4', '9', '1', '7', '2', '0', '8', '4', '2', '8', '9', '5', '2', '1', '5', '4', '4', '7', '9', '2', '5', '5', '1', '2', '3', '4', '4', '8', '3', '6', '6', '8', '4', '3', '8', '1', '2', '6', '1', '2', '3', '0', '1', '8', '1', '4', '8', '6', '9', '1', '1', '3', '0', '7', '3', '0', '5', '5', '6', '8', '5', '7', '1', '6', '6', '9', '3', '2', '0', '8', '8', '5', '6', '3', '1', '0', '0', '9', '7', '5', '5', '7', '5', '7', '8', '0', '1', '2', '9', '5', '3', '6', '8', '6', '4', '1', '6', '8', '0', '8', '8', '8', '1', '7', '7', '2', '1', '0', '9', '2', '1', '8', '5', '2', '9', '8', '0', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '2', '5', '2', '3', '3', '7', '3', '5', '2', '5', '1', '3', '1', '0', '4', '5', '5', '1', '5', '0', '5', '5', '0', '6', '2', '7', '3', '5', '5', '1', '8', '9', '5', '7', '8', '3', '8', '7', '7', '9', '3', '3', '7', '6', '3', '1', '1', '8', '7', '0', '5', '3', '5', '2', '5', '8', '5', '9', '8', '0', '5', '0', '6', '0', '4', '9', '7', '3', '7', '5', '5', '3', '3', '3', '1', '9', '0', '0', '8', '3', '8', '4', '4', '2', '0', '0', '1', '0', '6', '5', '5', '5', '5', '4', '1', '7', '4', '1', '4', '8', '1', '0', '3', '1', '4', '0', '7', '1', '7', '2', '3', '1', '6', '2', '3', '3', '3', '8', '9', '3', '9', '8', '5', '6', '4', '3', '4', '2', '5', '9', '8', '8', '6', '9', '8', '5', '5', '5', '7', '7', '9', '8', '8', '5', '2', '7', '8', '9', '9', '6', '4', '7', '9', '9', '6', '9', '9', '1', '9', '5', '3', '7', '8', '4', '3', '0', '9', '6', '0', '6', '0', '6', '7', '3', '8', '6', '7', '2', '0', '0', '1', '0', '1', '5', '7', '3', '9', '1', '2', '0', '8', '3', '"', ',']

theorem object_fragment0261427_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 374) (SourceJson.white (fragment0261427Field007Chars00 ++ tail)) fragment0261427Acc00700 =
      SourceJson.object (fuel + 373) (SourceJson.white tail) fragment0261427Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261427_object_field_007"
  err.flush

noncomputable def fragment0261427Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0261427Field008Value00 : SourceJson := .str (String.ofList ['1', '4', '1', '3', '4', '6', '0', '7', '0', '2', '1', '2', '9'])
noncomputable def fragment0261427Acc00900 : List (String × SourceJson) := (fragment0261427Field008Key00, fragment0261427Field008Value00) :: fragment0261427Acc00800
noncomputable def fragment0261427Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '1', '3', '4', '6', '0', '7', '0', '2', '1', '2', '9', '"', ',']

theorem object_fragment0261427_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 373) (SourceJson.white (fragment0261427Field008Chars00 ++ tail)) fragment0261427Acc00800 =
      SourceJson.object (fuel + 372) (SourceJson.white tail) fragment0261427Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261427_object_field_008"
  err.flush

noncomputable def fragment0261427Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0261427Field009Value00 : SourceJson := .str (String.ofList ['4', '6', '1', '0', '9', '8', '8', '9', '5', '8', '9', '4', '8'])
noncomputable def fragment0261427Acc01000 : List (String × SourceJson) := (fragment0261427Field009Key00, fragment0261427Field009Value00) :: fragment0261427Acc00900
noncomputable def fragment0261427Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '6', '1', '0', '9', '8', '8', '9', '5', '8', '9', '4', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0261427_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 372) (SourceJson.white (fragment0261427Field009Chars00 ++ tail)) fragment0261427Acc00900 =
      .ok (.obj (fragment0261427Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0261427_object_field_009"
  err.flush

noncomputable def fragment0261427Chars : List Char := '{' :: (fragment0261427Field000Chars00 ++ fragment0261427Field001Chars00 ++ fragment0261427Field002Chars00 ++ fragment0261427Field003Chars00 ++ fragment0261427Field004Chars00 ++ fragment0261427Field005Chars00 ++ fragment0261427Field006Chars00 ++ fragment0261427Field007Chars00 ++ fragment0261427Field008Chars00 ++ fragment0261427Field009Chars00)
noncomputable def fragment0261427Value : SourceJson := .obj (fragment0261427Acc01000.reverse)

theorem value_fragment0261427 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 382) (fragment0261427Chars ++ tail) =
      .ok (fragment0261427Value, tail) := by
  have hinput : fragment0261427Chars ++ tail = '{' :: (fragment0261427Field000Chars00 ++ (fragment0261427Field001Chars00 ++ (fragment0261427Field002Chars00 ++ (fragment0261427Field003Chars00 ++ (fragment0261427Field004Chars00 ++ (fragment0261427Field005Chars00 ++ (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0261427Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 382) (fragment0261427Chars ++ tail) =
        SourceJson.value (fuel + 382) ('{' :: (fragment0261427Field000Chars00 ++ (fragment0261427Field001Chars00 ++ (fragment0261427Field002Chars00 ++ (fragment0261427Field003Chars00 ++ (fragment0261427Field004Chars00 ++ (fragment0261427Field005Chars00 ++ (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 382)) hinput
    _ = SourceJson.object (fuel + 381) (SourceJson.white (fragment0261427Field000Chars00 ++ (fragment0261427Field001Chars00 ++ (fragment0261427Field002Chars00 ++ (fragment0261427Field003Chars00 ++ (fragment0261427Field004Chars00 ++ (fragment0261427Field005Chars00 ++ (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail)))))))))))) fragment0261427Acc00000 := by rfl
    _ = SourceJson.object (fuel + 380) (SourceJson.white (fragment0261427Field001Chars00 ++ (fragment0261427Field002Chars00 ++ (fragment0261427Field003Chars00 ++ (fragment0261427Field004Chars00 ++ (fragment0261427Field005Chars00 ++ (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail))))))))))) fragment0261427Acc00100 := object_fragment0261427_field_000 fuel (fragment0261427Field001Chars00 ++ (fragment0261427Field002Chars00 ++ (fragment0261427Field003Chars00 ++ (fragment0261427Field004Chars00 ++ (fragment0261427Field005Chars00 ++ (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 379) (SourceJson.white (fragment0261427Field002Chars00 ++ (fragment0261427Field003Chars00 ++ (fragment0261427Field004Chars00 ++ (fragment0261427Field005Chars00 ++ (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail)))))))))) fragment0261427Acc00200 := object_fragment0261427_field_001 fuel (fragment0261427Field002Chars00 ++ (fragment0261427Field003Chars00 ++ (fragment0261427Field004Chars00 ++ (fragment0261427Field005Chars00 ++ (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 378) (SourceJson.white (fragment0261427Field003Chars00 ++ (fragment0261427Field004Chars00 ++ (fragment0261427Field005Chars00 ++ (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail))))))))) fragment0261427Acc00300 := object_fragment0261427_field_002 fuel (fragment0261427Field003Chars00 ++ (fragment0261427Field004Chars00 ++ (fragment0261427Field005Chars00 ++ (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 377) (SourceJson.white (fragment0261427Field004Chars00 ++ (fragment0261427Field005Chars00 ++ (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail)))))))) fragment0261427Acc00400 := object_fragment0261427_field_003 fuel (fragment0261427Field004Chars00 ++ (fragment0261427Field005Chars00 ++ (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 376) (SourceJson.white (fragment0261427Field005Chars00 ++ (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail))))))) fragment0261427Acc00500 := object_fragment0261427_field_004 fuel (fragment0261427Field005Chars00 ++ (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 375) (SourceJson.white (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail)))))) fragment0261427Acc00600 := object_fragment0261427_field_005 fuel (fragment0261427Field006Chars00 ++ (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 374) (SourceJson.white (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail))))) fragment0261427Acc00700 := object_fragment0261427_field_006 fuel (fragment0261427Field007Chars00 ++ (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 373) (SourceJson.white (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail)))) fragment0261427Acc00800 := object_fragment0261427_field_007 fuel (fragment0261427Field008Chars00 ++ (fragment0261427Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 372) (SourceJson.white (fragment0261427Field009Chars00 ++ (tail))) fragment0261427Acc00900 := object_fragment0261427_field_008 fuel (fragment0261427Field009Chars00 ++ (tail))
    _ = .ok (fragment0261427Value, tail) := object_fragment0261427_field_009 fuel (tail)

noncomputable def fragment0263305Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0263305Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0263305Field000Value00 : SourceJson := .number (String.ofList ['7', '3'])
noncomputable def fragment0263305Acc00100 : List (String × SourceJson) := (fragment0263305Field000Key00, fragment0263305Field000Value00) :: fragment0263305Acc00000
noncomputable def fragment0263305Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '3', ',']

theorem object_fragment0263305_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0263305Field000Chars00 ++ tail)) fragment0263305Acc00000 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0263305Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263305_object_field_000"
  err.flush

noncomputable def fragment0263305Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0263305Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0263305Acc00200 : List (String × SourceJson) := (fragment0263305Field001Key00, fragment0263305Field001Value00) :: fragment0263305Acc00100
noncomputable def fragment0263305Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0263305_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0263305Field001Chars00 ++ tail)) fragment0263305Acc00100 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0263305Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263305_object_field_001"
  err.flush

noncomputable def fragment0263305Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0263305Field002Value00 : SourceJson := .str (String.ofList ['4', '8', '0', '2', '6', '8', '9', '6', '2', '2', '1', '5', '1', '8', '7', '4', '7', '7', '6', '7', '5', '2', '1', '2', '3', '2', '0', '6', '7', '2', '6', '8', '0', '4', '4', '4', '1', '3', '/', '7', '1', '9', '9', '9', '8', '5', '3', '4', '2', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0263305Acc00300 : List (String × SourceJson) := (fragment0263305Field002Key00, fragment0263305Field002Value00) :: fragment0263305Acc00200
noncomputable def fragment0263305Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '8', '0', '2', '6', '8', '9', '6', '2', '2', '1', '5', '1', '8', '7', '4', '7', '7', '6', '7', '5', '2', '1', '2', '3', '2', '0', '6', '7', '2', '6', '8', '0', '4', '4', '4', '1', '3', '/', '7', '1', '9', '9', '9', '8', '5', '3', '4', '2', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0263305_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0263305Field002Chars00 ++ tail)) fragment0263305Acc00200 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0263305Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263305_object_field_002"
  err.flush

noncomputable def fragment0263305Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0263305Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0263305Acc00400 : List (String × SourceJson) := (fragment0263305Field003Key00, fragment0263305Field003Value00) :: fragment0263305Acc00300
noncomputable def fragment0263305Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0263305_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0263305Field003Chars00 ++ tail)) fragment0263305Acc00300 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0263305Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263305_object_field_003"
  err.flush

noncomputable def fragment0263305Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0263305Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0263305Acc00500 : List (String × SourceJson) := (fragment0263305Field004Key00, fragment0263305Field004Value00) :: fragment0263305Acc00400
noncomputable def fragment0263305Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0263305_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0263305Field004Chars00 ++ tail)) fragment0263305Acc00400 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0263305Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263305_object_field_004"
  err.flush

noncomputable def fragment0263305Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0263305Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '7', '2', '1', '2', '6', '0', '1', '2', '5', '0', '9', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '3', '3', '6', '4', '6', '1', '6', '4', '7', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '0', '9', '9', '5', '2', '3', '2', '1', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '1', '2', '1', '8', '2', '4', '6', '0', '1', '/', '5', '9', '7', '7', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '3', '9', '8', '5', '0', '9', '4', '8', '3', '/', '2', '9', '8', '8', '5', '6', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '4', '5', '9', '3', '6', '8', '6', '1', '7', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '5', '4', '8', '8', '4', '3', '2', '6', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '0', '5', '1', '3', '0', '8', '7', '/', '3', '1', '0', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '2', '3', '6', '3', '3', '8', '5', '7', '/', '3', '1', '0', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '2', '9', '7', '7', '1', '4', '4', '9', '2', '7', '/', '9', '5', '6', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0263305Acc00600 : List (String × SourceJson) := (fragment0263305Field005Key00, fragment0263305Field005Value00) :: fragment0263305Acc00500
noncomputable def fragment0263305Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '1', '2', '6', '0', '1', '2', '5', '0', '9', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '3', '3', '6', '4', '6', '1', '6', '4', '7', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '0', '9', '9', '5', '2', '3', '2', '1', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '1', '2', '1', '8', '2', '4', '6', '0', '1', '/', '5', '9', '7', '7', '1', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '9', '8', '5', '0', '9', '4', '8', '3', '/', '2', '9', '8', '8', '5', '6', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '4', '5', '9', '3', '6', '8', '6', '1', '7', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '5', '4', '8', '8', '4', '3', '2', '6', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '0', '5', '1', '3', '0', '8', '7', '/', '3', '1', '0', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '3', '6', '3', '3', '8', '5', '7', '/', '3', '1', '0', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '2', '9', '7', '7', '1', '4', '4', '9', '2', '7', '/', '9', '5', '6', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0263305_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0263305Field005Chars00 ++ tail)) fragment0263305Acc00500 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0263305Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263305_object_field_005"
  err.flush

noncomputable def fragment0263305Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0263305Field006Value00 : SourceJson := .str (String.ofList ['1', '1', '7', '5', '1', '9', '7', '7', '2', '6', '4', '7', '1', '0', '1', '2', '7', '1', '2', '0', '0', '3', '7', '7', '2', '8', '8', '7', '0', '2', '5', '2', '5', '4', '1', '2', '4', '3', '7', '5', '6', '4', '3', '8', '4', '0', '0', '0', '/', '1', '6', '6', '0', '9', '2', '1', '1', '7', '8', '4', '8', '8', '0', '4', '0', '7', '1', '5', '8', '0', '0', '0', '1', '2', '9', '3', '0', '2', '7', '7', '8', '8', '9', '3', '9', '1', '3', '2', '5', '7', '4', '7', '3', '8', '1', '1', '7', '2', '2', '0', '1', '5', '8', '4', '5', '0', '6', '6', '9', '9', '5', '5', '9'])
noncomputable def fragment0263305Acc00700 : List (String × SourceJson) := (fragment0263305Field006Key00, fragment0263305Field006Value00) :: fragment0263305Acc00600
noncomputable def fragment0263305Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '7', '5', '1', '9', '7', '7', '2', '6', '4', '7', '1', '0', '1', '2', '7', '1', '2', '0', '0', '3', '7', '7', '2', '8', '8', '7', '0', '2', '5', '2', '5', '4', '1', '2', '4', '3', '7', '5', '6', '4', '3', '8', '4', '0', '0', '0', '/', '1', '6', '6', '0', '9', '2', '1', '1', '7', '8', '4', '8', '8', '0', '4', '0', '7', '1', '5', '8', '0', '0', '0', '1', '2', '9', '3', '0', '2', '7', '7', '8', '8', '9', '3', '9', '1', '3', '2', '5', '7', '4', '7', '3', '8', '1', '1', '7', '2', '2', '0', '1', '5', '8', '4', '5', '0', '6', '6', '9', '9', '5', '5', '9', '"', ',']

theorem object_fragment0263305_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0263305Field006Chars00 ++ tail)) fragment0263305Acc00600 =
      SourceJson.object (fuel + 194) (SourceJson.white tail) fragment0263305Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263305_object_field_006"
  err.flush

noncomputable def fragment0263305Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0263305Field007Value00 : SourceJson := .str (String.ofList ['3', '4', '9', '6', '9', '4', '3', '0', '1', '4', '8', '1', '6', '7', '2', '8', '9', '3', '5', '9', '6', '1', '0', '2', '5', '7', '5', '7', '9', '2', '0', '3', '2', '0', '0', '3', '4', '4', '7', '3', '5', '8', '0', '0', '6', '9', '2', '6', '2', '4', '3', '0', '2', '6', '0', '6', '0', '3', '5', '8', '3', '3', '6', '3', '0', '9', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '2', '6', '1', '1', '6', '9', '3', '0', '4', '3', '9', '0', '5', '8', '3', '6', '4', '6', '3', '1', '8', '3', '5', '9', '5', '6', '7', '3', '5', '0', '0', '7', '6', '8', '1', '3', '4', '9', '6', '4', '5', '2', '6', '5', '2', '0', '4', '5', '2', '8', '0', '2', '4', '2', '5', '6', '1', '4', '1', '3', '2', '1', '5', '7', '5', '6', '5', '5', '4', '8', '1', '8', '4', '3', '1', '7', '7', '9', '2', '0', '0', '4', '8', '1', '6', '7', '1', '0', '7', '5', '7', '8', '8', '4', '8', '8', '4', '9', '4', '4', '1'])
noncomputable def fragment0263305Acc00800 : List (String × SourceJson) := (fragment0263305Field007Key00, fragment0263305Field007Value00) :: fragment0263305Acc00700
noncomputable def fragment0263305Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '4', '9', '6', '9', '4', '3', '0', '1', '4', '8', '1', '6', '7', '2', '8', '9', '3', '5', '9', '6', '1', '0', '2', '5', '7', '5', '7', '9', '2', '0', '3', '2', '0', '0', '3', '4', '4', '7', '3', '5', '8', '0', '0', '6', '9', '2', '6', '2', '4', '3', '0', '2', '6', '0', '6', '0', '3', '5', '8', '3', '3', '6', '3', '0', '9', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '2', '6', '1', '1', '6', '9', '3', '0', '4', '3', '9', '0', '5', '8', '3', '6', '4', '6', '3', '1', '8', '3', '5', '9', '5', '6', '7', '3', '5', '0', '0', '7', '6', '8', '1', '3', '4', '9', '6', '4', '5', '2', '6', '5', '2', '0', '4', '5', '2', '8', '0', '2', '4', '2', '5', '6', '1', '4', '1', '3', '2', '1', '5', '7', '5', '6', '5', '5', '4', '8', '1', '8', '4', '3', '1', '7', '7', '9', '2', '0', '0', '4', '8', '1', '6', '7', '1', '0', '7', '5', '7', '8', '8', '4', '8', '8', '4', '9', '4', '4', '1', '"', ',']

theorem object_fragment0263305_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 194) (SourceJson.white (fragment0263305Field007Chars00 ++ tail)) fragment0263305Acc00700 =
      SourceJson.object (fuel + 193) (SourceJson.white tail) fragment0263305Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263305_object_field_007"
  err.flush

noncomputable def fragment0263305Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0263305Field008Value00 : SourceJson := .str (String.ofList ['5', '6', '0', '5', '8', '5', '0', '3', '9', '5', '8', '6', '2'])
noncomputable def fragment0263305Acc00900 : List (String × SourceJson) := (fragment0263305Field008Key00, fragment0263305Field008Value00) :: fragment0263305Acc00800
noncomputable def fragment0263305Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '6', '0', '5', '8', '5', '0', '3', '9', '5', '8', '6', '2', '"', ',']

theorem object_fragment0263305_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 193) (SourceJson.white (fragment0263305Field008Chars00 ++ tail)) fragment0263305Acc00800 =
      SourceJson.object (fuel + 192) (SourceJson.white tail) fragment0263305Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263305_object_field_008"
  err.flush

noncomputable def fragment0263305Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0263305Field009Value00 : SourceJson := .str (String.ofList ['2', '2', '5', '9', '6', '2', '4', '3', '6', '8', '6', '3', '0', '2'])
noncomputable def fragment0263305Acc01000 : List (String × SourceJson) := (fragment0263305Field009Key00, fragment0263305Field009Value00) :: fragment0263305Acc00900
noncomputable def fragment0263305Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '5', '9', '6', '2', '4', '3', '6', '8', '6', '3', '0', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0263305_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 192) (SourceJson.white (fragment0263305Field009Chars00 ++ tail)) fragment0263305Acc00900 =
      .ok (.obj (fragment0263305Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0263305_object_field_009"
  err.flush

noncomputable def fragment0263305Chars : List Char := '{' :: (fragment0263305Field000Chars00 ++ fragment0263305Field001Chars00 ++ fragment0263305Field002Chars00 ++ fragment0263305Field003Chars00 ++ fragment0263305Field004Chars00 ++ fragment0263305Field005Chars00 ++ fragment0263305Field006Chars00 ++ fragment0263305Field007Chars00 ++ fragment0263305Field008Chars00 ++ fragment0263305Field009Chars00)
noncomputable def fragment0263305Value : SourceJson := .obj (fragment0263305Acc01000.reverse)

theorem value_fragment0263305 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 202) (fragment0263305Chars ++ tail) =
      .ok (fragment0263305Value, tail) := by
  have hinput : fragment0263305Chars ++ tail = '{' :: (fragment0263305Field000Chars00 ++ (fragment0263305Field001Chars00 ++ (fragment0263305Field002Chars00 ++ (fragment0263305Field003Chars00 ++ (fragment0263305Field004Chars00 ++ (fragment0263305Field005Chars00 ++ (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0263305Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 202) (fragment0263305Chars ++ tail) =
        SourceJson.value (fuel + 202) ('{' :: (fragment0263305Field000Chars00 ++ (fragment0263305Field001Chars00 ++ (fragment0263305Field002Chars00 ++ (fragment0263305Field003Chars00 ++ (fragment0263305Field004Chars00 ++ (fragment0263305Field005Chars00 ++ (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 202)) hinput
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0263305Field000Chars00 ++ (fragment0263305Field001Chars00 ++ (fragment0263305Field002Chars00 ++ (fragment0263305Field003Chars00 ++ (fragment0263305Field004Chars00 ++ (fragment0263305Field005Chars00 ++ (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail)))))))))))) fragment0263305Acc00000 := by rfl
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0263305Field001Chars00 ++ (fragment0263305Field002Chars00 ++ (fragment0263305Field003Chars00 ++ (fragment0263305Field004Chars00 ++ (fragment0263305Field005Chars00 ++ (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail))))))))))) fragment0263305Acc00100 := object_fragment0263305_field_000 fuel (fragment0263305Field001Chars00 ++ (fragment0263305Field002Chars00 ++ (fragment0263305Field003Chars00 ++ (fragment0263305Field004Chars00 ++ (fragment0263305Field005Chars00 ++ (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0263305Field002Chars00 ++ (fragment0263305Field003Chars00 ++ (fragment0263305Field004Chars00 ++ (fragment0263305Field005Chars00 ++ (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail)))))))))) fragment0263305Acc00200 := object_fragment0263305_field_001 fuel (fragment0263305Field002Chars00 ++ (fragment0263305Field003Chars00 ++ (fragment0263305Field004Chars00 ++ (fragment0263305Field005Chars00 ++ (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0263305Field003Chars00 ++ (fragment0263305Field004Chars00 ++ (fragment0263305Field005Chars00 ++ (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail))))))))) fragment0263305Acc00300 := object_fragment0263305_field_002 fuel (fragment0263305Field003Chars00 ++ (fragment0263305Field004Chars00 ++ (fragment0263305Field005Chars00 ++ (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0263305Field004Chars00 ++ (fragment0263305Field005Chars00 ++ (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail)))))))) fragment0263305Acc00400 := object_fragment0263305_field_003 fuel (fragment0263305Field004Chars00 ++ (fragment0263305Field005Chars00 ++ (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0263305Field005Chars00 ++ (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail))))))) fragment0263305Acc00500 := object_fragment0263305_field_004 fuel (fragment0263305Field005Chars00 ++ (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail)))))) fragment0263305Acc00600 := object_fragment0263305_field_005 fuel (fragment0263305Field006Chars00 ++ (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 194) (SourceJson.white (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail))))) fragment0263305Acc00700 := object_fragment0263305_field_006 fuel (fragment0263305Field007Chars00 ++ (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 193) (SourceJson.white (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail)))) fragment0263305Acc00800 := object_fragment0263305_field_007 fuel (fragment0263305Field008Chars00 ++ (fragment0263305Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 192) (SourceJson.white (fragment0263305Field009Chars00 ++ (tail))) fragment0263305Acc00900 := object_fragment0263305_field_008 fuel (fragment0263305Field009Chars00 ++ (tail))
    _ = .ok (fragment0263305Value, tail) := object_fragment0263305_field_009 fuel (tail)

noncomputable def fragment0264837Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0264837Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0264837Field000Value00 : SourceJson := .number (String.ofList ['7', '4'])
noncomputable def fragment0264837Acc00100 : List (String × SourceJson) := (fragment0264837Field000Key00, fragment0264837Field000Value00) :: fragment0264837Acc00000
noncomputable def fragment0264837Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '4', ',']

theorem object_fragment0264837_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 359) (SourceJson.white (fragment0264837Field000Chars00 ++ tail)) fragment0264837Acc00000 =
      SourceJson.object (fuel + 358) (SourceJson.white tail) fragment0264837Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0264837_object_field_000"
  err.flush

noncomputable def fragment0264837Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0264837Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0264837Acc00200 : List (String × SourceJson) := (fragment0264837Field001Key00, fragment0264837Field001Value00) :: fragment0264837Acc00100
noncomputable def fragment0264837Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0264837_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 358) (SourceJson.white (fragment0264837Field001Chars00 ++ tail)) fragment0264837Acc00100 =
      SourceJson.object (fuel + 357) (SourceJson.white tail) fragment0264837Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0264837_object_field_001"
  err.flush

noncomputable def fragment0264837Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0264837Field002Value00 : SourceJson := .str (String.ofList ['5', '0', '7', '3', '4', '1', '0', '2', '7', '2', '3', '9', '8', '2', '2', '9', '5', '6', '3', '8', '2', '4', '1', '2', '3', '1', '0', '8', '6', '0', '5', '5', '7', '9', '3', '/', '1', '1', '9', '4', '4', '4', '2', '0', '1', '2', '8', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0264837Acc00300 : List (String × SourceJson) := (fragment0264837Field002Key00, fragment0264837Field002Value00) :: fragment0264837Acc00200
noncomputable def fragment0264837Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '0', '7', '3', '4', '1', '0', '2', '7', '2', '3', '9', '8', '2', '2', '9', '5', '6', '3', '8', '2', '4', '1', '2', '3', '1', '0', '8', '6', '0', '5', '5', '7', '9', '3', '/', '1', '1', '9', '4', '4', '4', '2', '0', '1', '2', '8', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0264837_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 357) (SourceJson.white (fragment0264837Field002Chars00 ++ tail)) fragment0264837Acc00200 =
      SourceJson.object (fuel + 356) (SourceJson.white tail) fragment0264837Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0264837_object_field_002"
  err.flush

noncomputable def fragment0264837Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0264837Field003Value00 : SourceJson := .str (String.ofList ['9', '6', '7', '0', '7', '3', '8', '9', '/', '6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0264837Acc00400 : List (String × SourceJson) := (fragment0264837Field003Key00, fragment0264837Field003Value00) :: fragment0264837Acc00300
noncomputable def fragment0264837Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '6', '7', '0', '7', '3', '8', '9', '/', '6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0264837_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 356) (SourceJson.white (fragment0264837Field003Chars00 ++ tail)) fragment0264837Acc00300 =
      SourceJson.object (fuel + 355) (SourceJson.white tail) fragment0264837Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0264837_object_field_003"
  err.flush

noncomputable def fragment0264837Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0264837Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0264837Acc00500 : List (String × SourceJson) := (fragment0264837Field004Key00, fragment0264837Field004Value00) :: fragment0264837Acc00400
noncomputable def fragment0264837Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0264837_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 355) (SourceJson.white (fragment0264837Field004Chars00 ++ tail)) fragment0264837Acc00400 =
      SourceJson.object (fuel + 354) (SourceJson.white tail) fragment0264837Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0264837_object_field_004"
  err.flush

noncomputable def fragment0264837Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0264837Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '8', '2', '0', '9', '5', '4', '6', '1', '0', '3', '6', '1', '6', '5', '2', '2', '0', '9', '7', '7', '/', '3', '3', '1', '4', '0', '5', '1', '0', '0', '7', '5', '3', '2', '6', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '4', '2', '4', '6', '1', '7', '5', '5', '0', '0', '2', '5', '1', '7', '7', '0', '1', '9', '/', '1', '5', '4', '1', '4', '1', '9', '0', '7', '3', '2', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '8', '5', '0', '3', '3', '2', '1', '8', '0', '1', '5', '6', '6', '5', '3', '9', '/', '6', '4', '0', '3', '9', '6', '3', '2', '9', '9', '5', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '4', '3', '4', '8', '5', '1', '0', '1', '6', '2', '3', '7', '7', '4', '8', '6', '1', '3', '/', '7', '8', '9', '0', '5', '9', '7', '6', '3', '6', '9', '8', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '3', '9', '9', '0', '7', '8', '8', '3', '7', '1', '1', '7', '0', '2', '6', '1', '/', '2', '6', '3', '0', '1', '9', '9', '2', '1', '2', '3', '2', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '1', '2', '9', '0', '7', '3', '5', '0', '5', '7', '4', '1', '3', '3', '5', '8', '2', '3', '/', '2', '0', '0', '8', '5', '1', '5', '7', '6', '2', '1', '4', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '8', '8', '6', '8', '0', '1', '7', '7', '7', '6', '4', '0', '4', '3', '7', '3', '9', '/', '2', '0', '0', '8', '5', '1', '5', '7', '6', '2', '1', '4', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '2', '6', '3', '5', '3', '2', '5', '6', '3', '6', '7', '6', '4', '4', '6', '3', '/', '2', '5', '1', '0', '6', '4', '4', '7', '0', '2', '6', '7', '6', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '7', '9', '7', '4', '1', '9', '4', '3', '4', '2', '9', '3', '0', '5', '1', '1', '/', '5', '0', '2', '1', '2', '8', '9', '4', '0', '5', '3', '5', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '8', '1', '9', '0', '6', '3', '7', '3', '5', '3', '9', '1', '8', '4', '9', '9', '3', '/', '1', '5', '4', '1', '4', '1', '9', '0', '7', '3', '2', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0264837Acc00600 : List (String × SourceJson) := (fragment0264837Field005Key00, fragment0264837Field005Value00) :: fragment0264837Acc00500
noncomputable def fragment0264837Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '2', '0', '9', '5', '4', '6', '1', '0', '3', '6', '1', '6', '5', '2', '2', '0', '9', '7', '7', '/', '3', '3', '1', '4', '0', '5', '1', '0', '0', '7', '5', '3', '2', '6', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '2', '4', '6', '1', '7', '5', '5', '0', '0', '2', '5', '1', '7', '7', '0', '1', '9', '/', '1', '5', '4', '1', '4', '1', '9', '0', '7', '3', '2', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '8', '5', '0', '3', '3', '2', '1', '8', '0', '1', '5', '6', '6', '5', '3', '9', '/', '6', '4', '0', '3', '9', '6', '3', '2', '9', '9', '5', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '3', '4', '8', '5', '1', '0', '1', '6', '2', '3', '7', '7', '4', '8', '6', '1', '3', '/', '7', '8', '9', '0', '5', '9', '7', '6', '3', '6', '9', '8', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '3', '9', '9', '0', '7', '8', '8', '3', '7', '1', '1', '7', '0', '2', '6', '1', '/', '2', '6', '3', '0', '1', '9', '9', '2', '1', '2', '3', '2', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '2', '9', '0', '7', '3', '5', '0', '5', '7', '4', '1', '3', '3', '5', '8', '2', '3', '/', '2', '0', '0', '8', '5', '1', '5', '7', '6', '2', '1', '4', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '8', '8', '6', '8', '0', '1', '7', '7', '7', '6', '4', '0', '4', '3', '7', '3', '9', '/', '2', '0', '0', '8', '5', '1', '5', '7', '6', '2', '1', '4', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '2', '6', '3', '5', '3', '2', '5', '6', '3', '6', '7', '6', '4', '4', '6', '3', '/', '2', '5', '1', '0', '6', '4', '4', '7', '0', '2', '6', '7', '6', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '7', '9', '7', '4', '1', '9', '4', '3', '4', '2', '9', '3', '0', '5', '1', '1', '/', '5', '0', '2', '1', '2', '8', '9', '4', '0', '5', '3', '5', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '8', '1', '9', '0', '6', '3', '7', '3', '5', '3', '9', '1', '8', '4', '9', '9', '3', '/', '1', '5', '4', '1', '4', '1', '9', '0', '7', '3', '2', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0264837_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 354) (SourceJson.white (fragment0264837Field005Chars00 ++ tail)) fragment0264837Acc00500 =
      SourceJson.object (fuel + 353) (SourceJson.white tail) fragment0264837Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0264837_object_field_005"
  err.flush

noncomputable def fragment0264837Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0264837Field006Value00 : SourceJson := .str (String.ofList ['2', '6', '8', '1', '2', '6', '6', '3', '4', '2', '4', '2', '7', '8', '7', '9', '2', '3', '1', '4', '1', '4', '0', '6', '0', '4', '8', '2', '9', '9', '8', '8', '7', '3', '5', '9', '1', '0', '2', '1', '1', '9', '6', '6', '2', '5', '/', '1', '8', '6', '6', '9', '5', '6', '7', '0', '8', '9', '9', '9', '1', '3', '7', '6', '7', '9', '6', '2', '5', '3', '4', '4', '2', '1', '3', '0', '8', '8', '8', '2', '3', '1', '5', '8', '2', '8', '0', '5', '9', '4', '0', '7', '1', '3', '3', '6', '2', '3', '9', '1', '5', '3', '2', '9', '8', '2', '8', '0', '4', '4'])
noncomputable def fragment0264837Acc00700 : List (String × SourceJson) := (fragment0264837Field006Key00, fragment0264837Field006Value00) :: fragment0264837Acc00600
noncomputable def fragment0264837Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '6', '8', '1', '2', '6', '6', '3', '4', '2', '4', '2', '7', '8', '7', '9', '2', '3', '1', '4', '1', '4', '0', '6', '0', '4', '8', '2', '9', '9', '8', '8', '7', '3', '5', '9', '1', '0', '2', '1', '1', '9', '6', '6', '2', '5', '/', '1', '8', '6', '6', '9', '5', '6', '7', '0', '8', '9', '9', '9', '1', '3', '7', '6', '7', '9', '6', '2', '5', '3', '4', '4', '2', '1', '3', '0', '8', '8', '8', '2', '3', '1', '5', '8', '2', '8', '0', '5', '9', '4', '0', '7', '1', '3', '3', '6', '2', '3', '9', '1', '5', '3', '2', '9', '8', '2', '8', '0', '4', '4', '"', ',']

theorem object_fragment0264837_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 353) (SourceJson.white (fragment0264837Field006Chars00 ++ tail)) fragment0264837Acc00600 =
      SourceJson.object (fuel + 352) (SourceJson.white tail) fragment0264837Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0264837_object_field_006"
  err.flush

noncomputable def fragment0264837Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0264837Field007Value00 : SourceJson := .str (String.ofList ['3', '5', '3', '5', '4', '3', '1', '3', '3', '2', '3', '9', '5', '1', '3', '2', '0', '0', '6', '5', '8', '4', '0', '2', '1', '1', '4', '2', '5', '6', '6', '4', '4', '7', '0', '8', '5', '8', '3', '9', '5', '0', '2', '5', '6', '1', '8', '4', '0', '3', '2', '3', '1', '6', '3', '1', '1', '6', '5', '1', '3', '0', '5', '9', '7', '9', '0', '8', '9', '9', '4', '0', '4', '2', '3', '3', '8', '7', '7', '4', '7', '4', '5', '7', '9', '6', '0', '1', '6', '8', '6', '2', '8', '2', '5', '1', '1', '8', '7', '3', '9', '2', '7', '6', '9', '4', '4', '5', '9', '9', '9', '0', '0', '3', '6', '4', '2', '6', '3', '8', '1', '5', '0', '8', '6', '3', '7', '9', '2', '1', '3', '6', '8', '8', '7', '4', '9', '5', '8', '6', '7', '9', '8', '8', '4', '7', '2', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '1', '8', '5', '5', '2', '1', '0', '5', '1', '9', '5', '3', '9', '0', '7', '8', '7', '7', '2', '0', '0', '7', '3', '5', '8', '4', '3', '3', '5', '5', '6', '0', '8', '8', '5', '0', '1', '9', '7', '2', '4', '5', '1', '6', '2', '8', '8', '6', '2', '1', '7', '1', '5', '3', '9', '5', '2', '0', '4', '4', '7', '2', '0', '9', '6', '5', '8', '4', '5', '2', '5', '8', '1', '9', '6', '6', '1', '9', '0', '8', '6', '8', '5', '9', '3', '3', '9', '7', '2', '7', '1', '0', '7', '1', '3', '1', '5', '5', '0', '3', '2', '4', '4', '3', '8', '9', '7', '1', '3', '6', '3', '9', '8', '7', '1', '6', '6', '6', '5', '3', '8', '9', '2', '9', '0', '8', '8', '0', '2', '9', '6', '2', '9', '7', '5', '0', '8', '9', '9', '3', '3', '3', '3', '7', '4', '5', '2', '9', '9', '7', '0', '5', '7', '7', '2', '3', '6', '9', '3', '2', '5', '1', '2', '5', '5', '0', '5', '8', '3', '6', '5', '3', '8', '5', '3', '7', '3', '2', '3', '3', '9'])
noncomputable def fragment0264837Acc00800 : List (String × SourceJson) := (fragment0264837Field007Key00, fragment0264837Field007Value00) :: fragment0264837Acc00700
noncomputable def fragment0264837Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '5', '3', '5', '4', '3', '1', '3', '3', '2', '3', '9', '5', '1', '3', '2', '0', '0', '6', '5', '8', '4', '0', '2', '1', '1', '4', '2', '5', '6', '6', '4', '4', '7', '0', '8', '5', '8', '3', '9', '5', '0', '2', '5', '6', '1', '8', '4', '0', '3', '2', '3', '1', '6', '3', '1', '1', '6', '5', '1', '3', '0', '5', '9', '7', '9', '0', '8', '9', '9', '4', '0', '4', '2', '3', '3', '8', '7', '7', '4', '7', '4', '5', '7', '9', '6', '0', '1', '6', '8', '6', '2', '8', '2', '5', '1', '1', '8', '7', '3', '9', '2', '7', '6', '9', '4', '4', '5', '9', '9', '9', '0', '0', '3', '6', '4', '2', '6', '3', '8', '1', '5', '0', '8', '6', '3', '7', '9', '2', '1', '3', '6', '8', '8', '7', '4', '9', '5', '8', '6', '7', '9', '8', '8', '4', '7', '2', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '1', '8', '5', '5', '2', '1', '0', '5', '1', '9', '5', '3', '9', '0', '7', '8', '7', '7', '2', '0', '0', '7', '3', '5', '8', '4', '3', '3', '5', '5', '6', '0', '8', '8', '5', '0', '1', '9', '7', '2', '4', '5', '1', '6', '2', '8', '8', '6', '2', '1', '7', '1', '5', '3', '9', '5', '2', '0', '4', '4', '7', '2', '0', '9', '6', '5', '8', '4', '5', '2', '5', '8', '1', '9', '6', '6', '1', '9', '0', '8', '6', '8', '5', '9', '3', '3', '9', '7', '2', '7', '1', '0', '7', '1', '3', '1', '5', '5', '0', '3', '2', '4', '4', '3', '8', '9', '7', '1', '3', '6', '3', '9', '8', '7', '1', '6', '6', '6', '5', '3', '8', '9', '2', '9', '0', '8', '8', '0', '2', '9', '6', '2', '9', '7', '5', '0', '8', '9', '9', '3', '3', '3', '3', '7', '4', '5', '2', '9', '9', '7', '0', '5', '7', '7', '2', '3', '6', '9', '3', '2', '5', '1', '2', '5', '5', '0', '5', '8', '3', '6', '5', '3', '8', '5', '3', '7', '3', '2', '3', '3', '9', '"', ',']

theorem object_fragment0264837_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 352) (SourceJson.white (fragment0264837Field007Chars00 ++ tail)) fragment0264837Acc00700 =
      SourceJson.object (fuel + 351) (SourceJson.white tail) fragment0264837Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0264837_object_field_007"
  err.flush

noncomputable def fragment0264837Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0264837Field008Value00 : SourceJson := .str (String.ofList ['1', '1', '3', '7', '8', '5', '0', '7', '3', '0', '5', '3', '8'])
noncomputable def fragment0264837Acc00900 : List (String × SourceJson) := (fragment0264837Field008Key00, fragment0264837Field008Value00) :: fragment0264837Acc00800
noncomputable def fragment0264837Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '3', '7', '8', '5', '0', '7', '3', '0', '5', '3', '8', '"', ',']

theorem object_fragment0264837_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 351) (SourceJson.white (fragment0264837Field008Chars00 ++ tail)) fragment0264837Acc00800 =
      SourceJson.object (fuel + 350) (SourceJson.white tail) fragment0264837Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0264837_object_field_008"
  err.flush

noncomputable def fragment0264837Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0264837Field009Value00 : SourceJson := .str (String.ofList ['3', '0', '4', '9', '4', '2', '6', '6', '6', '3', '7', '3', '2'])
noncomputable def fragment0264837Acc01000 : List (String × SourceJson) := (fragment0264837Field009Key00, fragment0264837Field009Value00) :: fragment0264837Acc00900
noncomputable def fragment0264837Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '0', '4', '9', '4', '2', '6', '6', '6', '3', '7', '3', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0264837_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 350) (SourceJson.white (fragment0264837Field009Chars00 ++ tail)) fragment0264837Acc00900 =
      .ok (.obj (fragment0264837Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0264837_object_field_009"
  err.flush

noncomputable def fragment0264837Chars : List Char := '{' :: (fragment0264837Field000Chars00 ++ fragment0264837Field001Chars00 ++ fragment0264837Field002Chars00 ++ fragment0264837Field003Chars00 ++ fragment0264837Field004Chars00 ++ fragment0264837Field005Chars00 ++ fragment0264837Field006Chars00 ++ fragment0264837Field007Chars00 ++ fragment0264837Field008Chars00 ++ fragment0264837Field009Chars00)
noncomputable def fragment0264837Value : SourceJson := .obj (fragment0264837Acc01000.reverse)

theorem value_fragment0264837 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 360) (fragment0264837Chars ++ tail) =
      .ok (fragment0264837Value, tail) := by
  have hinput : fragment0264837Chars ++ tail = '{' :: (fragment0264837Field000Chars00 ++ (fragment0264837Field001Chars00 ++ (fragment0264837Field002Chars00 ++ (fragment0264837Field003Chars00 ++ (fragment0264837Field004Chars00 ++ (fragment0264837Field005Chars00 ++ (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0264837Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 360) (fragment0264837Chars ++ tail) =
        SourceJson.value (fuel + 360) ('{' :: (fragment0264837Field000Chars00 ++ (fragment0264837Field001Chars00 ++ (fragment0264837Field002Chars00 ++ (fragment0264837Field003Chars00 ++ (fragment0264837Field004Chars00 ++ (fragment0264837Field005Chars00 ++ (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 360)) hinput
    _ = SourceJson.object (fuel + 359) (SourceJson.white (fragment0264837Field000Chars00 ++ (fragment0264837Field001Chars00 ++ (fragment0264837Field002Chars00 ++ (fragment0264837Field003Chars00 ++ (fragment0264837Field004Chars00 ++ (fragment0264837Field005Chars00 ++ (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail)))))))))))) fragment0264837Acc00000 := by rfl
    _ = SourceJson.object (fuel + 358) (SourceJson.white (fragment0264837Field001Chars00 ++ (fragment0264837Field002Chars00 ++ (fragment0264837Field003Chars00 ++ (fragment0264837Field004Chars00 ++ (fragment0264837Field005Chars00 ++ (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail))))))))))) fragment0264837Acc00100 := object_fragment0264837_field_000 fuel (fragment0264837Field001Chars00 ++ (fragment0264837Field002Chars00 ++ (fragment0264837Field003Chars00 ++ (fragment0264837Field004Chars00 ++ (fragment0264837Field005Chars00 ++ (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 357) (SourceJson.white (fragment0264837Field002Chars00 ++ (fragment0264837Field003Chars00 ++ (fragment0264837Field004Chars00 ++ (fragment0264837Field005Chars00 ++ (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail)))))))))) fragment0264837Acc00200 := object_fragment0264837_field_001 fuel (fragment0264837Field002Chars00 ++ (fragment0264837Field003Chars00 ++ (fragment0264837Field004Chars00 ++ (fragment0264837Field005Chars00 ++ (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 356) (SourceJson.white (fragment0264837Field003Chars00 ++ (fragment0264837Field004Chars00 ++ (fragment0264837Field005Chars00 ++ (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail))))))))) fragment0264837Acc00300 := object_fragment0264837_field_002 fuel (fragment0264837Field003Chars00 ++ (fragment0264837Field004Chars00 ++ (fragment0264837Field005Chars00 ++ (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 355) (SourceJson.white (fragment0264837Field004Chars00 ++ (fragment0264837Field005Chars00 ++ (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail)))))))) fragment0264837Acc00400 := object_fragment0264837_field_003 fuel (fragment0264837Field004Chars00 ++ (fragment0264837Field005Chars00 ++ (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 354) (SourceJson.white (fragment0264837Field005Chars00 ++ (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail))))))) fragment0264837Acc00500 := object_fragment0264837_field_004 fuel (fragment0264837Field005Chars00 ++ (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 353) (SourceJson.white (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail)))))) fragment0264837Acc00600 := object_fragment0264837_field_005 fuel (fragment0264837Field006Chars00 ++ (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 352) (SourceJson.white (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail))))) fragment0264837Acc00700 := object_fragment0264837_field_006 fuel (fragment0264837Field007Chars00 ++ (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 351) (SourceJson.white (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail)))) fragment0264837Acc00800 := object_fragment0264837_field_007 fuel (fragment0264837Field008Chars00 ++ (fragment0264837Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 350) (SourceJson.white (fragment0264837Field009Chars00 ++ (tail))) fragment0264837Acc00900 := object_fragment0264837_field_008 fuel (fragment0264837Field009Chars00 ++ (tail))
    _ = .ok (fragment0264837Value, tail) := object_fragment0264837_field_009 fuel (tail)

noncomputable def fragment0266682Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0266682Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0266682Field000Value00 : SourceJson := .number (String.ofList ['7', '5'])
noncomputable def fragment0266682Acc00100 : List (String × SourceJson) := (fragment0266682Field000Key00, fragment0266682Field000Value00) :: fragment0266682Acc00000
noncomputable def fragment0266682Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '5', ',']

theorem object_fragment0266682_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0266682Field000Chars00 ++ tail)) fragment0266682Acc00000 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0266682Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266682_object_field_000"
  err.flush

noncomputable def fragment0266682Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0266682Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0266682Acc00200 : List (String × SourceJson) := (fragment0266682Field001Key00, fragment0266682Field001Value00) :: fragment0266682Acc00100
noncomputable def fragment0266682Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0266682_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0266682Field001Chars00 ++ tail)) fragment0266682Acc00100 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0266682Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266682_object_field_001"
  err.flush

noncomputable def fragment0266682Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0266682Field002Value00 : SourceJson := .str (String.ofList ['3', '7', '4', '2', '3', '4', '9', '4', '6', '1', '8', '5', '7', '5', '0', '0', '0', '5', '9', '0', '0', '4', '4', '2', '6', '1', '6', '8', '4', '6', '7', '3', '5', '3', '4', '3', '/', '8', '5', '7', '1', '4', '1', '1', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0266682Acc00300 : List (String × SourceJson) := (fragment0266682Field002Key00, fragment0266682Field002Value00) :: fragment0266682Acc00200
noncomputable def fragment0266682Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '7', '4', '2', '3', '4', '9', '4', '6', '1', '8', '5', '7', '5', '0', '0', '0', '5', '9', '0', '0', '4', '4', '2', '6', '1', '6', '8', '4', '6', '7', '3', '5', '3', '4', '3', '/', '8', '5', '7', '1', '4', '1', '1', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0266682_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0266682Field002Chars00 ++ tail)) fragment0266682Acc00200 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0266682Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266682_object_field_002"
  err.flush

noncomputable def fragment0266682Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0266682Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0266682Acc00400 : List (String × SourceJson) := (fragment0266682Field003Key00, fragment0266682Field003Value00) :: fragment0266682Acc00300
noncomputable def fragment0266682Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0266682_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0266682Field003Chars00 ++ tail)) fragment0266682Acc00300 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0266682Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266682_object_field_003"
  err.flush

noncomputable def fragment0266682Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0266682Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0266682Acc00500 : List (String × SourceJson) := (fragment0266682Field004Key00, fragment0266682Field004Value00) :: fragment0266682Acc00400
noncomputable def fragment0266682Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0266682_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0266682Field004Chars00 ++ tail)) fragment0266682Acc00400 =
      SourceJson.object (fuel + 194) (SourceJson.white tail) fragment0266682Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266682_object_field_004"
  err.flush

noncomputable def fragment0266682Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0266682Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '3', '4', '5', '3', '5', '0', '3', '1', '0', '9', '7', '/', '1', '5', '9', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '3', '2', '0', '1', '2', '7', '8', '3', '3', '/', '7', '9', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '9', '5', '5', '7', '8', '5', '1', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '9', '1', '8', '0', '1', '1', '1', '1', '9', '/', '6', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '5', '4', '6', '8', '0', '4', '6', '7', '9', '/', '6', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '7', '4', '2', '1', '6', '7', '9', '9', '/', '1', '0', '8', '6', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '6', '7', '0', '8', '7', '5', '8', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '3', '5', '0', '4', '8', '7', '8', '9', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '8', '7', '7', '8', '6', '9', '4', '5', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '9', '8', '0', '2', '9', '8', '6', '5', '3', '/', '2', '3', '9', '0', '8', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0266682Acc00600 : List (String × SourceJson) := (fragment0266682Field005Key00, fragment0266682Field005Value00) :: fragment0266682Acc00500
noncomputable def fragment0266682Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '5', '3', '5', '0', '3', '1', '0', '9', '7', '/', '1', '5', '9', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '3', '2', '0', '1', '2', '7', '8', '3', '3', '/', '7', '9', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '9', '5', '5', '7', '8', '5', '1', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '9', '1', '8', '0', '1', '1', '1', '1', '9', '/', '6', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '5', '4', '6', '8', '0', '4', '6', '7', '9', '/', '6', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '7', '4', '2', '1', '6', '7', '9', '9', '/', '1', '0', '8', '6', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '6', '7', '0', '8', '7', '5', '8', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '3', '5', '0', '4', '8', '7', '8', '9', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '8', '7', '7', '8', '6', '9', '4', '5', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '9', '8', '0', '2', '9', '8', '6', '5', '3', '/', '2', '3', '9', '0', '8', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0266682_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 194) (SourceJson.white (fragment0266682Field005Chars00 ++ tail)) fragment0266682Acc00500 =
      SourceJson.object (fuel + 193) (SourceJson.white tail) fragment0266682Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266682_object_field_005"
  err.flush

noncomputable def fragment0266682Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0266682Field006Value00 : SourceJson := .str (String.ofList ['6', '3', '2', '6', '9', '1', '0', '1', '7', '1', '3', '3', '7', '2', '9', '3', '4', '3', '2', '1', '1', '8', '0', '0', '4', '0', '0', '9', '9', '7', '1', '2', '1', '9', '6', '8', '7', '2', '5', '1', '5', '8', '4', '0', '0', '0', '/', '1', '1', '5', '5', '9', '7', '9', '2', '7', '2', '9', '9', '8', '0', '6', '1', '6', '1', '8', '5', '3', '4', '3', '4', '6', '3', '2', '4', '7', '2', '1', '8', '5', '9', '1', '4', '3', '7', '2', '8', '7', '1', '2', '0', '9', '4', '6', '6', '8', '6', '2', '9', '5', '7', '2', '4', '4', '9', '6', '2', '3', '8', '9'])
noncomputable def fragment0266682Acc00700 : List (String × SourceJson) := (fragment0266682Field006Key00, fragment0266682Field006Value00) :: fragment0266682Acc00600
noncomputable def fragment0266682Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '3', '2', '6', '9', '1', '0', '1', '7', '1', '3', '3', '7', '2', '9', '3', '4', '3', '2', '1', '1', '8', '0', '0', '4', '0', '0', '9', '9', '7', '1', '2', '1', '9', '6', '8', '7', '2', '5', '1', '5', '8', '4', '0', '0', '0', '/', '1', '1', '5', '5', '9', '7', '9', '2', '7', '2', '9', '9', '8', '0', '6', '1', '6', '1', '8', '5', '3', '4', '3', '4', '6', '3', '2', '4', '7', '2', '1', '8', '5', '9', '1', '4', '3', '7', '2', '8', '7', '1', '2', '0', '9', '4', '6', '6', '8', '6', '2', '9', '5', '7', '2', '4', '4', '9', '6', '2', '3', '8', '9', '"', ',']

theorem object_fragment0266682_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 193) (SourceJson.white (fragment0266682Field006Chars00 ++ tail)) fragment0266682Acc00600 =
      SourceJson.object (fuel + 192) (SourceJson.white tail) fragment0266682Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266682_object_field_006"
  err.flush

noncomputable def fragment0266682Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0266682Field007Value00 : SourceJson := .str (String.ofList ['3', '5', '7', '9', '5', '9', '4', '3', '1', '8', '6', '3', '6', '5', '9', '6', '5', '9', '6', '9', '3', '3', '3', '0', '0', '2', '2', '2', '7', '0', '4', '1', '9', '7', '3', '3', '4', '8', '8', '5', '1', '7', '3', '5', '9', '2', '3', '1', '8', '4', '4', '5', '7', '2', '1', '0', '7', '6', '2', '7', '8', '4', '1', '8', '4', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '3', '1', '3', '9', '5', '9', '8', '7', '1', '4', '9', '4', '5', '7', '6', '0', '4', '4', '5', '9', '0', '3', '3', '4', '4', '1', '7', '0', '8', '1', '9', '7', '9', '4', '6', '2', '2', '1', '7', '8', '1', '8', '3', '0', '4', '4', '8', '9', '8', '9', '6', '8', '5', '5', '3', '3', '6', '2', '8', '4', '4', '5', '1', '4', '1', '0', '7', '0', '3', '9', '8', '9', '4', '6', '1', '9', '3', '7', '0', '2', '0', '4', '7', '3', '9', '3', '8', '4', '8', '7', '3', '6', '6', '6', '2', '4', '4', '8', '4', '9'])
noncomputable def fragment0266682Acc00800 : List (String × SourceJson) := (fragment0266682Field007Key00, fragment0266682Field007Value00) :: fragment0266682Acc00700
noncomputable def fragment0266682Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '5', '7', '9', '5', '9', '4', '3', '1', '8', '6', '3', '6', '5', '9', '6', '5', '9', '6', '9', '3', '3', '3', '0', '0', '2', '2', '2', '7', '0', '4', '1', '9', '7', '3', '3', '4', '8', '8', '5', '1', '7', '3', '5', '9', '2', '3', '1', '8', '4', '4', '5', '7', '2', '1', '0', '7', '6', '2', '7', '8', '4', '1', '8', '4', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '3', '1', '3', '9', '5', '9', '8', '7', '1', '4', '9', '4', '5', '7', '6', '0', '4', '4', '5', '9', '0', '3', '3', '4', '4', '1', '7', '0', '8', '1', '9', '7', '9', '4', '6', '2', '2', '1', '7', '8', '1', '8', '3', '0', '4', '4', '8', '9', '8', '9', '6', '8', '5', '5', '3', '3', '6', '2', '8', '4', '4', '5', '1', '4', '1', '0', '7', '0', '3', '9', '8', '9', '4', '6', '1', '9', '3', '7', '0', '2', '0', '4', '7', '3', '9', '3', '8', '4', '8', '7', '3', '6', '6', '6', '2', '4', '4', '8', '4', '9', '"', ',']

theorem object_fragment0266682_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 192) (SourceJson.white (fragment0266682Field007Chars00 ++ tail)) fragment0266682Acc00700 =
      SourceJson.object (fuel + 191) (SourceJson.white tail) fragment0266682Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266682_object_field_007"
  err.flush

noncomputable def fragment0266682Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0266682Field008Value00 : SourceJson := .str (String.ofList ['4', '3', '3', '6', '3', '1', '8', '8', '1', '6', '2', '3', '4'])
noncomputable def fragment0266682Acc00900 : List (String × SourceJson) := (fragment0266682Field008Key00, fragment0266682Field008Value00) :: fragment0266682Acc00800
noncomputable def fragment0266682Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '3', '3', '6', '3', '1', '8', '8', '1', '6', '2', '3', '4', '"', ',']

theorem object_fragment0266682_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 191) (SourceJson.white (fragment0266682Field008Chars00 ++ tail)) fragment0266682Acc00800 =
      SourceJson.object (fuel + 190) (SourceJson.white tail) fragment0266682Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266682_object_field_008"
  err.flush

noncomputable def fragment0266682Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0266682Field009Value00 : SourceJson := .str (String.ofList ['1', '5', '4', '8', '5', '7', '1', '0', '4', '8', '5', '4', '4', '8'])
noncomputable def fragment0266682Acc01000 : List (String × SourceJson) := (fragment0266682Field009Key00, fragment0266682Field009Value00) :: fragment0266682Acc00900
noncomputable def fragment0266682Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '4', '8', '5', '7', '1', '0', '4', '8', '5', '4', '4', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0266682_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 190) (SourceJson.white (fragment0266682Field009Chars00 ++ tail)) fragment0266682Acc00900 =
      .ok (.obj (fragment0266682Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266682_object_field_009"
  err.flush

noncomputable def fragment0266682Chars : List Char := '{' :: (fragment0266682Field000Chars00 ++ fragment0266682Field001Chars00 ++ fragment0266682Field002Chars00 ++ fragment0266682Field003Chars00 ++ fragment0266682Field004Chars00 ++ fragment0266682Field005Chars00 ++ fragment0266682Field006Chars00 ++ fragment0266682Field007Chars00 ++ fragment0266682Field008Chars00 ++ fragment0266682Field009Chars00)
noncomputable def fragment0266682Value : SourceJson := .obj (fragment0266682Acc01000.reverse)

theorem value_fragment0266682 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 200) (fragment0266682Chars ++ tail) =
      .ok (fragment0266682Value, tail) := by
  have hinput : fragment0266682Chars ++ tail = '{' :: (fragment0266682Field000Chars00 ++ (fragment0266682Field001Chars00 ++ (fragment0266682Field002Chars00 ++ (fragment0266682Field003Chars00 ++ (fragment0266682Field004Chars00 ++ (fragment0266682Field005Chars00 ++ (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0266682Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 200) (fragment0266682Chars ++ tail) =
        SourceJson.value (fuel + 200) ('{' :: (fragment0266682Field000Chars00 ++ (fragment0266682Field001Chars00 ++ (fragment0266682Field002Chars00 ++ (fragment0266682Field003Chars00 ++ (fragment0266682Field004Chars00 ++ (fragment0266682Field005Chars00 ++ (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 200)) hinput
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0266682Field000Chars00 ++ (fragment0266682Field001Chars00 ++ (fragment0266682Field002Chars00 ++ (fragment0266682Field003Chars00 ++ (fragment0266682Field004Chars00 ++ (fragment0266682Field005Chars00 ++ (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail)))))))))))) fragment0266682Acc00000 := by rfl
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0266682Field001Chars00 ++ (fragment0266682Field002Chars00 ++ (fragment0266682Field003Chars00 ++ (fragment0266682Field004Chars00 ++ (fragment0266682Field005Chars00 ++ (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail))))))))))) fragment0266682Acc00100 := object_fragment0266682_field_000 fuel (fragment0266682Field001Chars00 ++ (fragment0266682Field002Chars00 ++ (fragment0266682Field003Chars00 ++ (fragment0266682Field004Chars00 ++ (fragment0266682Field005Chars00 ++ (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0266682Field002Chars00 ++ (fragment0266682Field003Chars00 ++ (fragment0266682Field004Chars00 ++ (fragment0266682Field005Chars00 ++ (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail)))))))))) fragment0266682Acc00200 := object_fragment0266682_field_001 fuel (fragment0266682Field002Chars00 ++ (fragment0266682Field003Chars00 ++ (fragment0266682Field004Chars00 ++ (fragment0266682Field005Chars00 ++ (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0266682Field003Chars00 ++ (fragment0266682Field004Chars00 ++ (fragment0266682Field005Chars00 ++ (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail))))))))) fragment0266682Acc00300 := object_fragment0266682_field_002 fuel (fragment0266682Field003Chars00 ++ (fragment0266682Field004Chars00 ++ (fragment0266682Field005Chars00 ++ (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0266682Field004Chars00 ++ (fragment0266682Field005Chars00 ++ (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail)))))))) fragment0266682Acc00400 := object_fragment0266682_field_003 fuel (fragment0266682Field004Chars00 ++ (fragment0266682Field005Chars00 ++ (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 194) (SourceJson.white (fragment0266682Field005Chars00 ++ (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail))))))) fragment0266682Acc00500 := object_fragment0266682_field_004 fuel (fragment0266682Field005Chars00 ++ (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 193) (SourceJson.white (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail)))))) fragment0266682Acc00600 := object_fragment0266682_field_005 fuel (fragment0266682Field006Chars00 ++ (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 192) (SourceJson.white (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail))))) fragment0266682Acc00700 := object_fragment0266682_field_006 fuel (fragment0266682Field007Chars00 ++ (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 191) (SourceJson.white (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail)))) fragment0266682Acc00800 := object_fragment0266682_field_007 fuel (fragment0266682Field008Chars00 ++ (fragment0266682Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 190) (SourceJson.white (fragment0266682Field009Chars00 ++ (tail))) fragment0266682Acc00900 := object_fragment0266682_field_008 fuel (fragment0266682Field009Chars00 ++ (tail))
    _ = .ok (fragment0266682Value, tail) := object_fragment0266682_field_009 fuel (tail)

noncomputable def fragment0268202Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0268202Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0268202Field000Value00 : SourceJson := .number (String.ofList ['7', '6'])
noncomputable def fragment0268202Acc00100 : List (String × SourceJson) := (fragment0268202Field000Key00, fragment0268202Field000Value00) :: fragment0268202Acc00000
noncomputable def fragment0268202Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '6', ',']

theorem object_fragment0268202_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 209) (SourceJson.white (fragment0268202Field000Chars00 ++ tail)) fragment0268202Acc00000 =
      SourceJson.object (fuel + 208) (SourceJson.white tail) fragment0268202Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268202_object_field_000"
  err.flush

noncomputable def fragment0268202Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0268202Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '1']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0268202Acc00200 : List (String × SourceJson) := (fragment0268202Field001Key00, fragment0268202Field001Value00) :: fragment0268202Acc00100
noncomputable def fragment0268202Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0268202_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 208) (SourceJson.white (fragment0268202Field001Chars00 ++ tail)) fragment0268202Acc00100 =
      SourceJson.object (fuel + 207) (SourceJson.white tail) fragment0268202Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268202_object_field_001"
  err.flush

noncomputable def fragment0268202Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0268202Field002Value00 : SourceJson := .str (String.ofList ['1', '5', '7', '8', '4', '3', '9', '7', '4', '8', '3', '4', '5', '7', '2', '5', '4', '5', '6', '6', '6', '8', '9', '1', '9', '0', '9', '5', '0', '9', '2', '4', '0', '7', '1', '/', '3', '9', '9', '2', '8', '9', '3', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0268202Acc00300 : List (String × SourceJson) := (fragment0268202Field002Key00, fragment0268202Field002Value00) :: fragment0268202Acc00200
noncomputable def fragment0268202Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '5', '7', '8', '4', '3', '9', '7', '4', '8', '3', '4', '5', '7', '2', '5', '4', '5', '6', '6', '6', '8', '9', '1', '9', '0', '9', '5', '0', '9', '2', '4', '0', '7', '1', '/', '3', '9', '9', '2', '8', '9', '3', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0268202_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 207) (SourceJson.white (fragment0268202Field002Chars00 ++ tail)) fragment0268202Acc00200 =
      SourceJson.object (fuel + 206) (SourceJson.white tail) fragment0268202Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268202_object_field_002"
  err.flush

noncomputable def fragment0268202Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0268202Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0268202Acc00400 : List (String × SourceJson) := (fragment0268202Field003Key00, fragment0268202Field003Value00) :: fragment0268202Acc00300
noncomputable def fragment0268202Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0268202_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 206) (SourceJson.white (fragment0268202Field003Chars00 ++ tail)) fragment0268202Acc00300 =
      SourceJson.object (fuel + 205) (SourceJson.white tail) fragment0268202Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268202_object_field_003"
  err.flush

noncomputable def fragment0268202Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0268202Field004Value00 : SourceJson := .arr [.str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '7', '1', '7', '0', '7', '/', '1', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0268202Acc00500 : List (String × SourceJson) := (fragment0268202Field004Key00, fragment0268202Field004Value00) :: fragment0268202Acc00400
noncomputable def fragment0268202Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '7', '1', '7', '0', '7', '/', '1', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0268202_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 205) (SourceJson.white (fragment0268202Field004Chars00 ++ tail)) fragment0268202Acc00400 =
      SourceJson.object (fuel + 204) (SourceJson.white tail) fragment0268202Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268202_object_field_004"
  err.flush

noncomputable def fragment0268202Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0268202Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '6', '2', '3', '4', '6', '6', '4', '3', '6', '1', '3', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '6', '5', '5', '7', '0', '9', '2', '7', '5', '1', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '8', '4', '4', '8', '2', '6', '3', '1', '4', '7', '/', '4', '7', '8', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '8', '5', '4', '3', '6', '7', '4', '1', '3', '/', '1', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '1', '1', '1', '9', '5', '4', '5', '3', '3', '/', '1', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '9', '8', '1', '7', '3', '8', '6', '2', '9', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '9', '7', '5', '9', '7', '9', '5', '0', '7', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '0', '8', '8', '3', '9', '8', '3', '1', '/', '2', '1', '7', '3', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '9', '0', '6', '8', '5', '2', '2', '1', '/', '2', '1', '7', '3', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '3', '1', '9', '7', '7', '7', '6', '0', '3', '1', '/', '9', '5', '6', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0268202Acc00600 : List (String × SourceJson) := (fragment0268202Field005Key00, fragment0268202Field005Value00) :: fragment0268202Acc00500
noncomputable def fragment0268202Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '2', '3', '4', '6', '6', '4', '3', '6', '1', '3', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '6', '5', '5', '7', '0', '9', '2', '7', '5', '1', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '8', '4', '4', '8', '2', '6', '3', '1', '4', '7', '/', '4', '7', '8', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '8', '5', '4', '3', '6', '7', '4', '1', '3', '/', '1', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '1', '1', '1', '9', '5', '4', '5', '3', '3', '/', '1', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '9', '8', '1', '7', '3', '8', '6', '2', '9', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '7', '5', '9', '7', '9', '5', '0', '7', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '0', '8', '8', '3', '9', '8', '3', '1', '/', '2', '1', '7', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '9', '0', '6', '8', '5', '2', '2', '1', '/', '2', '1', '7', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '1', '9', '7', '7', '7', '6', '0', '3', '1', '/', '9', '5', '6', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0268202_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0268202Field005Chars00 ++ tail)) fragment0268202Acc00500 =
      SourceJson.object (fuel + 203) (SourceJson.white tail) fragment0268202Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268202_object_field_005"
  err.flush

noncomputable def fragment0268202Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0268202Field006Value00 : SourceJson := .str (String.ofList ['1', '3', '6', '6', '2', '9', '7', '5', '7', '8', '4', '1', '2', '6', '1', '1', '9', '6', '2', '1', '4', '9', '0', '3', '2', '8', '1', '1', '0', '8', '2', '5', '1', '8', '3', '1', '6', '4', '1', '1', '1', '2', '5', '7', '6', '0', '0', '/', '2', '5', '7', '3', '8', '5', '7', '8', '3', '7', '8', '0', '2', '7', '0', '4', '7', '5', '9', '7', '7', '5', '0', '7', '9', '4', '1', '7', '6', '7', '0', '5', '3', '9', '6', '3', '8', '8', '1', '2', '8', '5', '0', '0', '3', '4', '3', '0', '3', '6', '8', '5', '5', '6', '0', '9', '3', '0', '9', '6', '5', '2', '7'])
noncomputable def fragment0268202Acc00700 : List (String × SourceJson) := (fragment0268202Field006Key00, fragment0268202Field006Value00) :: fragment0268202Acc00600
noncomputable def fragment0268202Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '6', '6', '2', '9', '7', '5', '7', '8', '4', '1', '2', '6', '1', '1', '9', '6', '2', '1', '4', '9', '0', '3', '2', '8', '1', '1', '0', '8', '2', '5', '1', '8', '3', '1', '6', '4', '1', '1', '1', '2', '5', '7', '6', '0', '0', '/', '2', '5', '7', '3', '8', '5', '7', '8', '3', '7', '8', '0', '2', '7', '0', '4', '7', '5', '9', '7', '7', '5', '0', '7', '9', '4', '1', '7', '6', '7', '0', '5', '3', '9', '6', '3', '8', '8', '1', '2', '8', '5', '0', '0', '3', '4', '3', '0', '3', '6', '8', '5', '5', '6', '0', '9', '3', '0', '9', '6', '5', '2', '7', '"', ',']

theorem object_fragment0268202_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0268202Field006Chars00 ++ tail)) fragment0268202Acc00600 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0268202Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268202_object_field_006"
  err.flush

noncomputable def fragment0268202Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0268202Field007Value00 : SourceJson := .str (String.ofList ['3', '7', '5', '8', '9', '8', '9', '8', '2', '3', '8', '3', '0', '0', '4', '0', '7', '2', '6', '9', '0', '5', '2', '4', '2', '6', '1', '7', '0', '6', '5', '1', '2', '6', '0', '2', '6', '8', '1', '4', '3', '1', '2', '0', '5', '9', '6', '4', '4', '5', '6', '2', '3', '2', '8', '1', '9', '8', '5', '4', '1', '6', '5', '9', '0', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '1', '6', '6', '2', '2', '2', '5', '0', '9', '5', '1', '9', '9', '0', '0', '9', '9', '4', '2', '9', '2', '1', '7', '4', '2', '7', '1', '2', '3', '4', '7', '6', '9', '3', '1', '6', '1', '7', '5', '4', '3', '9', '4', '2', '2', '6', '3', '6', '8', '7', '1', '6', '1', '6', '3', '0', '1', '9', '6', '8', '5', '9', '8', '7', '2', '3', '5', '4', '6', '5', '7', '9', '6', '5', '1', '3', '1', '2', '8', '2', '4', '5', '9', '5', '9', '6', '3', '8', '5', '1', '7', '3', '9', '7', '6', '9', '0', '9', '9', '6', '2', '9', '6', '5', '3'])
noncomputable def fragment0268202Acc00800 : List (String × SourceJson) := (fragment0268202Field007Key00, fragment0268202Field007Value00) :: fragment0268202Acc00700
noncomputable def fragment0268202Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '7', '5', '8', '9', '8', '9', '8', '2', '3', '8', '3', '0', '0', '4', '0', '7', '2', '6', '9', '0', '5', '2', '4', '2', '6', '1', '7', '0', '6', '5', '1', '2', '6', '0', '2', '6', '8', '1', '4', '3', '1', '2', '0', '5', '9', '6', '4', '4', '5', '6', '2', '3', '2', '8', '1', '9', '8', '5', '4', '1', '6', '5', '9', '0', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '1', '6', '6', '2', '2', '2', '5', '0', '9', '5', '1', '9', '9', '0', '0', '9', '9', '4', '2', '9', '2', '1', '7', '4', '2', '7', '1', '2', '3', '4', '7', '6', '9', '3', '1', '6', '1', '7', '5', '4', '3', '9', '4', '2', '2', '6', '3', '6', '8', '7', '1', '6', '1', '6', '3', '0', '1', '9', '6', '8', '5', '9', '8', '7', '2', '3', '5', '4', '6', '5', '7', '9', '6', '5', '1', '3', '1', '2', '8', '2', '4', '5', '9', '5', '9', '6', '3', '8', '5', '1', '7', '3', '9', '7', '6', '9', '0', '9', '9', '6', '2', '9', '6', '5', '3', '"', ',']

theorem object_fragment0268202_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0268202Field007Chars00 ++ tail)) fragment0268202Acc00700 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0268202Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268202_object_field_007"
  err.flush

noncomputable def fragment0268202Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0268202Field008Value00 : SourceJson := .str (String.ofList ['4', '2', '0', '5', '7', '1', '9', '7', '1', '7', '5', '1', '6'])
noncomputable def fragment0268202Acc00900 : List (String × SourceJson) := (fragment0268202Field008Key00, fragment0268202Field008Value00) :: fragment0268202Acc00800
noncomputable def fragment0268202Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '2', '0', '5', '7', '1', '9', '7', '1', '7', '5', '1', '6', '"', ',']

theorem object_fragment0268202_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0268202Field008Chars00 ++ tail)) fragment0268202Acc00800 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0268202Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268202_object_field_008"
  err.flush

noncomputable def fragment0268202Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0268202Field009Value00 : SourceJson := .str (String.ofList ['1', '4', '7', '6', '8', '1', '5', '2', '8', '6', '1', '1', '1', '6'])
noncomputable def fragment0268202Acc01000 : List (String × SourceJson) := (fragment0268202Field009Key00, fragment0268202Field009Value00) :: fragment0268202Acc00900
noncomputable def fragment0268202Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '7', '6', '8', '1', '5', '2', '8', '6', '1', '1', '1', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0268202_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0268202Field009Chars00 ++ tail)) fragment0268202Acc00900 =
      .ok (.obj (fragment0268202Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268202_object_field_009"
  err.flush

noncomputable def fragment0268202Chars : List Char := '{' :: (fragment0268202Field000Chars00 ++ fragment0268202Field001Chars00 ++ fragment0268202Field002Chars00 ++ fragment0268202Field003Chars00 ++ fragment0268202Field004Chars00 ++ fragment0268202Field005Chars00 ++ fragment0268202Field006Chars00 ++ fragment0268202Field007Chars00 ++ fragment0268202Field008Chars00 ++ fragment0268202Field009Chars00)
noncomputable def fragment0268202Value : SourceJson := .obj (fragment0268202Acc01000.reverse)

theorem value_fragment0268202 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 210) (fragment0268202Chars ++ tail) =
      .ok (fragment0268202Value, tail) := by
  have hinput : fragment0268202Chars ++ tail = '{' :: (fragment0268202Field000Chars00 ++ (fragment0268202Field001Chars00 ++ (fragment0268202Field002Chars00 ++ (fragment0268202Field003Chars00 ++ (fragment0268202Field004Chars00 ++ (fragment0268202Field005Chars00 ++ (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0268202Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 210) (fragment0268202Chars ++ tail) =
        SourceJson.value (fuel + 210) ('{' :: (fragment0268202Field000Chars00 ++ (fragment0268202Field001Chars00 ++ (fragment0268202Field002Chars00 ++ (fragment0268202Field003Chars00 ++ (fragment0268202Field004Chars00 ++ (fragment0268202Field005Chars00 ++ (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 210)) hinput
    _ = SourceJson.object (fuel + 209) (SourceJson.white (fragment0268202Field000Chars00 ++ (fragment0268202Field001Chars00 ++ (fragment0268202Field002Chars00 ++ (fragment0268202Field003Chars00 ++ (fragment0268202Field004Chars00 ++ (fragment0268202Field005Chars00 ++ (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail)))))))))))) fragment0268202Acc00000 := by rfl
    _ = SourceJson.object (fuel + 208) (SourceJson.white (fragment0268202Field001Chars00 ++ (fragment0268202Field002Chars00 ++ (fragment0268202Field003Chars00 ++ (fragment0268202Field004Chars00 ++ (fragment0268202Field005Chars00 ++ (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail))))))))))) fragment0268202Acc00100 := object_fragment0268202_field_000 fuel (fragment0268202Field001Chars00 ++ (fragment0268202Field002Chars00 ++ (fragment0268202Field003Chars00 ++ (fragment0268202Field004Chars00 ++ (fragment0268202Field005Chars00 ++ (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 207) (SourceJson.white (fragment0268202Field002Chars00 ++ (fragment0268202Field003Chars00 ++ (fragment0268202Field004Chars00 ++ (fragment0268202Field005Chars00 ++ (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail)))))))))) fragment0268202Acc00200 := object_fragment0268202_field_001 fuel (fragment0268202Field002Chars00 ++ (fragment0268202Field003Chars00 ++ (fragment0268202Field004Chars00 ++ (fragment0268202Field005Chars00 ++ (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 206) (SourceJson.white (fragment0268202Field003Chars00 ++ (fragment0268202Field004Chars00 ++ (fragment0268202Field005Chars00 ++ (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail))))))))) fragment0268202Acc00300 := object_fragment0268202_field_002 fuel (fragment0268202Field003Chars00 ++ (fragment0268202Field004Chars00 ++ (fragment0268202Field005Chars00 ++ (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 205) (SourceJson.white (fragment0268202Field004Chars00 ++ (fragment0268202Field005Chars00 ++ (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail)))))))) fragment0268202Acc00400 := object_fragment0268202_field_003 fuel (fragment0268202Field004Chars00 ++ (fragment0268202Field005Chars00 ++ (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0268202Field005Chars00 ++ (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail))))))) fragment0268202Acc00500 := object_fragment0268202_field_004 fuel (fragment0268202Field005Chars00 ++ (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail)))))) fragment0268202Acc00600 := object_fragment0268202_field_005 fuel (fragment0268202Field006Chars00 ++ (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail))))) fragment0268202Acc00700 := object_fragment0268202_field_006 fuel (fragment0268202Field007Chars00 ++ (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail)))) fragment0268202Acc00800 := object_fragment0268202_field_007 fuel (fragment0268202Field008Chars00 ++ (fragment0268202Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0268202Field009Chars00 ++ (tail))) fragment0268202Acc00900 := object_fragment0268202_field_008 fuel (fragment0268202Field009Chars00 ++ (tail))
    _ = .ok (fragment0268202Value, tail) := object_fragment0268202_field_009 fuel (tail)

noncomputable def fragment0269747Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0269747Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0269747Field000Value00 : SourceJson := .number (String.ofList ['7', '7'])
noncomputable def fragment0269747Acc00100 : List (String × SourceJson) := (fragment0269747Field000Key00, fragment0269747Field000Value00) :: fragment0269747Acc00000
noncomputable def fragment0269747Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '7', ',']

theorem object_fragment0269747_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 452) (SourceJson.white (fragment0269747Field000Chars00 ++ tail)) fragment0269747Acc00000 =
      SourceJson.object (fuel + 451) (SourceJson.white tail) fragment0269747Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269747_object_field_000"
  err.flush

noncomputable def fragment0269747Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0269747Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['4']), .number (String.ofList ['3']), .number (String.ofList ['0'])]
noncomputable def fragment0269747Acc00200 : List (String × SourceJson) := (fragment0269747Field001Key00, fragment0269747Field001Value00) :: fragment0269747Acc00100
noncomputable def fragment0269747Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0269747_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 451) (SourceJson.white (fragment0269747Field001Chars00 ++ tail)) fragment0269747Acc00100 =
      SourceJson.object (fuel + 450) (SourceJson.white tail) fragment0269747Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269747_object_field_001"
  err.flush

noncomputable def fragment0269747Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0269747Field002Value00 : SourceJson := .str (String.ofList ['1', '3', '6', '4', '9', '1', '0', '6', '4', '3', '9', '5', '3', '6', '3', '6', '9', '8', '5', '8', '2', '9', '9', '4', '9', '3', '5', '4', '3', '2', '7', '0', '6', '1', '6', '4', '0', '0', '4', '1', '/', '8', '2', '0', '7', '5', '5', '2', '6', '4', '9', '8', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0269747Acc00300 : List (String × SourceJson) := (fragment0269747Field002Key00, fragment0269747Field002Value00) :: fragment0269747Acc00200
noncomputable def fragment0269747Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '3', '6', '4', '9', '1', '0', '6', '4', '3', '9', '5', '3', '6', '3', '6', '9', '8', '5', '8', '2', '9', '9', '4', '9', '3', '5', '4', '3', '2', '7', '0', '6', '1', '6', '4', '0', '0', '4', '1', '/', '8', '2', '0', '7', '5', '5', '2', '6', '4', '9', '8', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0269747_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 450) (SourceJson.white (fragment0269747Field002Chars00 ++ tail)) fragment0269747Acc00200 =
      SourceJson.object (fuel + 449) (SourceJson.white tail) fragment0269747Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269747_object_field_002"
  err.flush

noncomputable def fragment0269747Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0269747Field003Value00 : SourceJson := .str (String.ofList ['3', '3', '0', '3', '6', '8', '0', '3', '9', '/', '1', '4', '8', '9', '9', '5', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0269747Acc00400 : List (String × SourceJson) := (fragment0269747Field003Key00, fragment0269747Field003Value00) :: fragment0269747Acc00300
noncomputable def fragment0269747Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '3', '0', '3', '6', '8', '0', '3', '9', '/', '1', '4', '8', '9', '9', '5', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0269747_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 449) (SourceJson.white (fragment0269747Field003Chars00 ++ tail)) fragment0269747Acc00300 =
      SourceJson.object (fuel + 448) (SourceJson.white tail) fragment0269747Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269747_object_field_003"
  err.flush

noncomputable def fragment0269747Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0269747Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0269747Acc00500 : List (String × SourceJson) := (fragment0269747Field004Key00, fragment0269747Field004Value00) :: fragment0269747Acc00400
noncomputable def fragment0269747Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0269747_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 448) (SourceJson.white (fragment0269747Field004Chars00 ++ tail)) fragment0269747Acc00400 =
      SourceJson.object (fuel + 447) (SourceJson.white tail) fragment0269747Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269747_object_field_004"
  err.flush

noncomputable def fragment0269747Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0269747Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '2', '2', '4', '6', '3', '5', '0', '5', '5', '8', '1', '9', '5', '1', '4', '2', '2', '6', '7', '7', '9', '2', '7', '/', '6', '0', '6', '8', '2', '3', '4', '3', '6', '6', '4', '8', '0', '8', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '3', '2', '6', '3', '6', '5', '7', '1', '4', '4', '0', '0', '6', '1', '3', '9', '3', '7', '4', '6', '7', '/', '7', '5', '8', '5', '2', '9', '2', '9', '5', '8', '1', '0', '1', '0', '5', '0', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '9', '5', '6', '2', '3', '6', '3', '8', '4', '1', '7', '4', '7', '6', '7', '8', '0', '1', '8', '1', '3', '/', '1', '2', '1', '3', '6', '4', '6', '8', '7', '3', '2', '9', '6', '1', '6', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '2', '1', '2', '3', '0', '0', '2', '1', '7', '9', '9', '9', '4', '0', '2', '8', '4', '1', '5', '7', '/', '9', '6', '3', '2', '1', '1', '8', '0', '4', '2', '0', '3', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '9', '0', '6', '6', '6', '3', '0', '8', '9', '2', '0', '1', '1', '8', '8', '0', '0', '2', '7', '1', '1', '/', '2', '8', '8', '9', '6', '3', '5', '4', '1', '2', '6', '0', '9', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '1', '0', '8', '9', '3', '2', '6', '6', '9', '7', '8', '0', '2', '6', '3', '0', '5', '0', '4', '8', '7', '/', '5', '5', '1', '6', '5', '7', '6', '6', '9', '6', '8', '0', '0', '7', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '4', '7', '8', '3', '0', '2', '9', '4', '3', '3', '3', '8', '4', '1', '0', '7', '7', '6', '6', '2', '7', '/', '1', '1', '0', '3', '3', '1', '5', '3', '3', '9', '3', '6', '0', '1', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '7', '5', '4', '5', '7', '5', '0', '0', '0', '0', '6', '7', '0', '5', '4', '7', '2', '1', '3', '0', '7', '/', '1', '1', '0', '3', '3', '1', '5', '3', '3', '9', '3', '6', '0', '1', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '7', '0', '5', '0', '0', '4', '0', '7', '2', '3', '7', '9', '2', '3', '8', '5', '8', '2', '8', '0', '1', '/', '5', '5', '1', '6', '5', '7', '6', '6', '9', '6', '8', '0', '0', '7', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '8', '3', '3', '4', '1', '0', '3', '3', '9', '6', '9', '2', '5', '5', '3', '9', '4', '9', '/', '7', '5', '8', '5', '2', '9', '2', '9', '5', '8', '1', '0', '1', '0', '5', '0', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0269747Acc00600 : List (String × SourceJson) := (fragment0269747Field005Key00, fragment0269747Field005Value00) :: fragment0269747Acc00500
noncomputable def fragment0269747Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '2', '4', '6', '3', '5', '0', '5', '5', '8', '1', '9', '5', '1', '4', '2', '2', '6', '7', '7', '9', '2', '7', '/', '6', '0', '6', '8', '2', '3', '4', '3', '6', '6', '4', '8', '0', '8', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '3', '2', '6', '3', '6', '5', '7', '1', '4', '4', '0', '0', '6', '1', '3', '9', '3', '7', '4', '6', '7', '/', '7', '5', '8', '5', '2', '9', '2', '9', '5', '8', '1', '0', '1', '0', '5', '0', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '9', '5', '6', '2', '3', '6', '3', '8', '4', '1', '7', '4', '7', '6', '7', '8', '0', '1', '8', '1', '3', '/', '1', '2', '1', '3', '6', '4', '6', '8', '7', '3', '2', '9', '6', '1', '6', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '2', '1', '2', '3', '0', '0', '2', '1', '7', '9', '9', '9', '4', '0', '2', '8', '4', '1', '5', '7', '/', '9', '6', '3', '2', '1', '1', '8', '0', '4', '2', '0', '3', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '9', '0', '6', '6', '6', '3', '0', '8', '9', '2', '0', '1', '1', '8', '8', '0', '0', '2', '7', '1', '1', '/', '2', '8', '8', '9', '6', '3', '5', '4', '1', '2', '6', '0', '9', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '1', '0', '8', '9', '3', '2', '6', '6', '9', '7', '8', '0', '2', '6', '3', '0', '5', '0', '4', '8', '7', '/', '5', '5', '1', '6', '5', '7', '6', '6', '9', '6', '8', '0', '0', '7', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '4', '7', '8', '3', '0', '2', '9', '4', '3', '3', '3', '8', '4', '1', '0', '7', '7', '6', '6', '2', '7', '/', '1', '1', '0', '3', '3', '1', '5', '3', '3', '9', '3', '6', '0', '1', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '7', '5', '4', '5', '7', '5', '0', '0', '0', '0', '6', '7', '0', '5', '4', '7', '2', '1', '3', '0', '7', '/', '1', '1', '0', '3', '3', '1', '5', '3', '3', '9', '3', '6', '0', '1', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '7', '0', '5', '0', '0', '4', '0', '7', '2', '3', '7', '9', '2', '3', '8', '5', '8', '2', '8', '0', '1', '/', '5', '5', '1', '6', '5', '7', '6', '6', '9', '6', '8', '0', '0', '7', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '8', '3', '3', '4', '1', '0', '3', '3', '9', '6', '9', '2', '5', '5', '3', '9', '4', '9', '/', '7', '5', '8', '5', '2', '9', '2', '9', '5', '8', '1', '0', '1', '0', '5', '0', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0269747_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 447) (SourceJson.white (fragment0269747Field005Chars00 ++ tail)) fragment0269747Acc00500 =
      SourceJson.object (fuel + 446) (SourceJson.white tail) fragment0269747Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269747_object_field_005"
  err.flush

noncomputable def fragment0269747Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0269747Field006Value00 : SourceJson := .str (String.ofList ['2', '5', '8', '1', '4', '2', '0', '7', '2', '9', '9', '7', '4', '3', '8', '4', '1', '2', '5', '9', '9', '3', '8', '4', '5', '2', '8', '5', '6', '5', '9', '4', '3', '0', '5', '4', '2', '1', '6', '3', '5', '3', '9', '9', '9', '0', '6', '8', '8', '7', '6', '4', '3', '4', '0', '6', '2', '5', '/', '3', '2', '7', '5', '6', '5', '2', '3', '4', '4', '7', '9', '8', '0', '8', '3', '9', '6', '7', '7', '7', '5', '3', '6', '2', '4', '7', '1', '4', '2', '7', '0', '5', '9', '4', '7', '0', '9', '5', '9', '8', '3', '0', '1', '9', '2', '1', '4', '7', '1', '5', '4', '0', '1', '7', '9', '5', '7', '9', '8', '0', '9', '6', '3', '0', '3', '3', '2', '3', '8', '4'])
noncomputable def fragment0269747Acc00700 : List (String × SourceJson) := (fragment0269747Field006Key00, fragment0269747Field006Value00) :: fragment0269747Acc00600
noncomputable def fragment0269747Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '5', '8', '1', '4', '2', '0', '7', '2', '9', '9', '7', '4', '3', '8', '4', '1', '2', '5', '9', '9', '3', '8', '4', '5', '2', '8', '5', '6', '5', '9', '4', '3', '0', '5', '4', '2', '1', '6', '3', '5', '3', '9', '9', '9', '0', '6', '8', '8', '7', '6', '4', '3', '4', '0', '6', '2', '5', '/', '3', '2', '7', '5', '6', '5', '2', '3', '4', '4', '7', '9', '8', '0', '8', '3', '9', '6', '7', '7', '7', '5', '3', '6', '2', '4', '7', '1', '4', '2', '7', '0', '5', '9', '4', '7', '0', '9', '5', '9', '8', '3', '0', '1', '9', '2', '1', '4', '7', '1', '5', '4', '0', '1', '7', '9', '5', '7', '9', '8', '0', '9', '6', '3', '0', '3', '3', '2', '3', '8', '4', '"', ',']

theorem object_fragment0269747_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 446) (SourceJson.white (fragment0269747Field006Chars00 ++ tail)) fragment0269747Acc00600 =
      SourceJson.object (fuel + 445) (SourceJson.white tail) fragment0269747Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269747_object_field_006"
  err.flush

noncomputable def fragment0269747Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0269747Field007Value00 : SourceJson := .str (String.ofList ['6', '4', '4', '4', '3', '5', '9', '3', '6', '6', '3', '9', '8', '9', '1', '1', '5', '4', '0', '3', '0', '7', '0', '6', '2', '8', '6', '6', '0', '4', '4', '3', '8', '1', '1', '4', '9', '6', '3', '6', '9', '6', '5', '9', '6', '7', '0', '5', '0', '8', '0', '7', '7', '7', '0', '2', '2', '5', '3', '1', '5', '8', '1', '2', '5', '8', '2', '5', '3', '6', '5', '4', '6', '7', '4', '0', '8', '4', '8', '3', '0', '7', '4', '7', '5', '6', '0', '4', '3', '1', '0', '6', '0', '0', '7', '0', '0', '4', '6', '2', '9', '7', '5', '4', '7', '4', '2', '3', '4', '1', '6', '2', '4', '0', '0', '3', '6', '2', '6', '0', '4', '1', '6', '9', '2', '0', '2', '8', '2', '6', '2', '6', '4', '9', '2', '6', '8', '6', '4', '8', '0', '0', '1', '9', '6', '0', '2', '8', '2', '9', '0', '5', '0', '1', '9', '1', '6', '4', '0', '3', '2', '4', '0', '3', '3', '5', '4', '3', '9', '8', '9', '6', '8', '1', '4', '9', '2', '2', '4', '2', '1', '8', '4', '6', '0', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '9', '1', '3', '6', '4', '2', '1', '2', '0', '6', '3', '7', '1', '0', '3', '1', '5', '4', '6', '1', '4', '6', '3', '6', '8', '3', '1', '0', '8', '9', '0', '8', '8', '6', '8', '5', '9', '5', '2', '6', '9', '3', '2', '1', '2', '9', '3', '3', '8', '2', '1', '6', '8', '4', '8', '9', '2', '9', '5', '2', '8', '8', '1', '1', '1', '8', '3', '4', '2', '0', '0', '5', '4', '3', '1', '5', '8', '6', '3', '3', '0', '4', '5', '1', '1', '3', '1', '5', '8', '6', '9', '8', '5', '8', '9', '0', '6', '8', '8', '9', '1', '9', '2', '6', '7', '8', '8', '8', '1', '0', '5', '9', '7', '4', '4', '9', '6', '9', '2', '2', '8', '8', '8', '7', '3', '5', '3', '9', '4', '3', '4', '2', '4', '2', '9', '7', '9', '9', '1', '8', '4', '6', '1', '0', '9', '3', '1', '3', '1', '0', '0', '8', '8', '8', '3', '5', '9', '5', '5', '6', '8', '7', '0', '7', '3', '6', '9', '0', '7', '0', '3', '2', '4', '7', '0', '2', '2', '1', '6', '5', '4', '8', '9', '9', '3', '7', '5', '9', '6', '3', '7', '5', '5', '1', '2', '1', '8', '6', '0', '6', '2', '5', '9', '7', '3', '3', '6', '3', '9', '5', '4', '1', '5', '6', '3', '3', '7', '4', '3', '6', '1', '4', '6', '3', '1', '3'])
noncomputable def fragment0269747Acc00800 : List (String × SourceJson) := (fragment0269747Field007Key00, fragment0269747Field007Value00) :: fragment0269747Acc00700
noncomputable def fragment0269747Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '4', '4', '4', '3', '5', '9', '3', '6', '6', '3', '9', '8', '9', '1', '1', '5', '4', '0', '3', '0', '7', '0', '6', '2', '8', '6', '6', '0', '4', '4', '3', '8', '1', '1', '4', '9', '6', '3', '6', '9', '6', '5', '9', '6', '7', '0', '5', '0', '8', '0', '7', '7', '7', '0', '2', '2', '5', '3', '1', '5', '8', '1', '2', '5', '8', '2', '5', '3', '6', '5', '4', '6', '7', '4', '0', '8', '4', '8', '3', '0', '7', '4', '7', '5', '6', '0', '4', '3', '1', '0', '6', '0', '0', '7', '0', '0', '4', '6', '2', '9', '7', '5', '4', '7', '4', '2', '3', '4', '1', '6', '2', '4', '0', '0', '3', '6', '2', '6', '0', '4', '1', '6', '9', '2', '0', '2', '8', '2', '6', '2', '6', '4', '9', '2', '6', '8', '6', '4', '8', '0', '0', '1', '9', '6', '0', '2', '8', '2', '9', '0', '5', '0', '1', '9', '1', '6', '4', '0', '3', '2', '4', '0', '3', '3', '5', '4', '3', '9', '8', '9', '6', '8', '1', '4', '9', '2', '2', '4', '2', '1', '8', '4', '6', '0', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '9', '1', '3', '6', '4', '2', '1', '2', '0', '6', '3', '7', '1', '0', '3', '1', '5', '4', '6', '1', '4', '6', '3', '6', '8', '3', '1', '0', '8', '9', '0', '8', '8', '6', '8', '5', '9', '5', '2', '6', '9', '3', '2', '1', '2', '9', '3', '3', '8', '2', '1', '6', '8', '4', '8', '9', '2', '9', '5', '2', '8', '8', '1', '1', '1', '8', '3', '4', '2', '0', '0', '5', '4', '3', '1', '5', '8', '6', '3', '3', '0', '4', '5', '1', '1', '3', '1', '5', '8', '6', '9', '8', '5', '8', '9', '0', '6', '8', '8', '9', '1', '9', '2', '6', '7', '8', '8', '8', '1', '0', '5', '9', '7', '4', '4', '9', '6', '9', '2', '2', '8', '8', '8', '7', '3', '5', '3', '9', '4', '3', '4', '2', '4', '2', '9', '7', '9', '9', '1', '8', '4', '6', '1', '0', '9', '3', '1', '3', '1', '0', '0', '8', '8', '8', '3', '5', '9', '5', '5', '6', '8', '7', '0', '7', '3', '6', '9', '0', '7', '0', '3', '2', '4', '7', '0', '2', '2', '1', '6', '5', '4', '8', '9', '9', '3', '7', '5', '9', '6', '3', '7', '5', '5', '1', '2', '1', '8', '6', '0', '6', '2', '5', '9', '7', '3', '3', '6', '3', '9', '5', '4', '1', '5', '6', '3', '3', '7', '4', '3', '6', '1', '4', '6', '3', '1', '3', '"', ',']

theorem object_fragment0269747_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 445) (SourceJson.white (fragment0269747Field007Chars00 ++ tail)) fragment0269747Acc00700 =
      SourceJson.object (fuel + 444) (SourceJson.white tail) fragment0269747Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269747_object_field_007"
  err.flush

noncomputable def fragment0269747Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0269747Field008Value00 : SourceJson := .str (String.ofList ['6', '2', '4', '3', '6', '7', '9', '1', '0', '8', '2', '8', '1', '8', '1', '5'])
noncomputable def fragment0269747Acc00900 : List (String × SourceJson) := (fragment0269747Field008Key00, fragment0269747Field008Value00) :: fragment0269747Acc00800
noncomputable def fragment0269747Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '2', '4', '3', '6', '7', '9', '1', '0', '8', '2', '8', '1', '8', '1', '5', '"', ',']

theorem object_fragment0269747_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 444) (SourceJson.white (fragment0269747Field008Chars00 ++ tail)) fragment0269747Acc00800 =
      SourceJson.object (fuel + 443) (SourceJson.white tail) fragment0269747Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269747_object_field_008"
  err.flush

noncomputable def fragment0269747Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0269747Field009Value00 : SourceJson := .str (String.ofList ['1', '7', '5', '2', '3', '5', '9', '1', '7', '8', '1', '0', '5', '6', '8', '7', '0'])
noncomputable def fragment0269747Acc01000 : List (String × SourceJson) := (fragment0269747Field009Key00, fragment0269747Field009Value00) :: fragment0269747Acc00900
noncomputable def fragment0269747Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '5', '2', '3', '5', '9', '1', '7', '8', '1', '0', '5', '6', '8', '7', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0269747_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 443) (SourceJson.white (fragment0269747Field009Chars00 ++ tail)) fragment0269747Acc00900 =
      .ok (.obj (fragment0269747Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269747_object_field_009"
  err.flush

noncomputable def fragment0269747Chars : List Char := '{' :: (fragment0269747Field000Chars00 ++ fragment0269747Field001Chars00 ++ fragment0269747Field002Chars00 ++ fragment0269747Field003Chars00 ++ fragment0269747Field004Chars00 ++ fragment0269747Field005Chars00 ++ fragment0269747Field006Chars00 ++ fragment0269747Field007Chars00 ++ fragment0269747Field008Chars00 ++ fragment0269747Field009Chars00)
noncomputable def fragment0269747Value : SourceJson := .obj (fragment0269747Acc01000.reverse)

theorem value_fragment0269747 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 453) (fragment0269747Chars ++ tail) =
      .ok (fragment0269747Value, tail) := by
  have hinput : fragment0269747Chars ++ tail = '{' :: (fragment0269747Field000Chars00 ++ (fragment0269747Field001Chars00 ++ (fragment0269747Field002Chars00 ++ (fragment0269747Field003Chars00 ++ (fragment0269747Field004Chars00 ++ (fragment0269747Field005Chars00 ++ (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0269747Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 453) (fragment0269747Chars ++ tail) =
        SourceJson.value (fuel + 453) ('{' :: (fragment0269747Field000Chars00 ++ (fragment0269747Field001Chars00 ++ (fragment0269747Field002Chars00 ++ (fragment0269747Field003Chars00 ++ (fragment0269747Field004Chars00 ++ (fragment0269747Field005Chars00 ++ (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 453)) hinput
    _ = SourceJson.object (fuel + 452) (SourceJson.white (fragment0269747Field000Chars00 ++ (fragment0269747Field001Chars00 ++ (fragment0269747Field002Chars00 ++ (fragment0269747Field003Chars00 ++ (fragment0269747Field004Chars00 ++ (fragment0269747Field005Chars00 ++ (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail)))))))))))) fragment0269747Acc00000 := by rfl
    _ = SourceJson.object (fuel + 451) (SourceJson.white (fragment0269747Field001Chars00 ++ (fragment0269747Field002Chars00 ++ (fragment0269747Field003Chars00 ++ (fragment0269747Field004Chars00 ++ (fragment0269747Field005Chars00 ++ (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail))))))))))) fragment0269747Acc00100 := object_fragment0269747_field_000 fuel (fragment0269747Field001Chars00 ++ (fragment0269747Field002Chars00 ++ (fragment0269747Field003Chars00 ++ (fragment0269747Field004Chars00 ++ (fragment0269747Field005Chars00 ++ (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 450) (SourceJson.white (fragment0269747Field002Chars00 ++ (fragment0269747Field003Chars00 ++ (fragment0269747Field004Chars00 ++ (fragment0269747Field005Chars00 ++ (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail)))))))))) fragment0269747Acc00200 := object_fragment0269747_field_001 fuel (fragment0269747Field002Chars00 ++ (fragment0269747Field003Chars00 ++ (fragment0269747Field004Chars00 ++ (fragment0269747Field005Chars00 ++ (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 449) (SourceJson.white (fragment0269747Field003Chars00 ++ (fragment0269747Field004Chars00 ++ (fragment0269747Field005Chars00 ++ (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail))))))))) fragment0269747Acc00300 := object_fragment0269747_field_002 fuel (fragment0269747Field003Chars00 ++ (fragment0269747Field004Chars00 ++ (fragment0269747Field005Chars00 ++ (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 448) (SourceJson.white (fragment0269747Field004Chars00 ++ (fragment0269747Field005Chars00 ++ (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail)))))))) fragment0269747Acc00400 := object_fragment0269747_field_003 fuel (fragment0269747Field004Chars00 ++ (fragment0269747Field005Chars00 ++ (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 447) (SourceJson.white (fragment0269747Field005Chars00 ++ (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail))))))) fragment0269747Acc00500 := object_fragment0269747_field_004 fuel (fragment0269747Field005Chars00 ++ (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 446) (SourceJson.white (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail)))))) fragment0269747Acc00600 := object_fragment0269747_field_005 fuel (fragment0269747Field006Chars00 ++ (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 445) (SourceJson.white (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail))))) fragment0269747Acc00700 := object_fragment0269747_field_006 fuel (fragment0269747Field007Chars00 ++ (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 444) (SourceJson.white (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail)))) fragment0269747Acc00800 := object_fragment0269747_field_007 fuel (fragment0269747Field008Chars00 ++ (fragment0269747Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 443) (SourceJson.white (fragment0269747Field009Chars00 ++ (tail))) fragment0269747Acc00900 := object_fragment0269747_field_008 fuel (fragment0269747Field009Chars00 ++ (tail))
    _ = .ok (fragment0269747Value, tail) := object_fragment0269747_field_009 fuel (tail)

noncomputable def fragment0271793Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0271793Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0271793Field000Value00 : SourceJson := .number (String.ofList ['7', '8'])
noncomputable def fragment0271793Acc00100 : List (String × SourceJson) := (fragment0271793Field000Key00, fragment0271793Field000Value00) :: fragment0271793Acc00000
noncomputable def fragment0271793Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '8', ',']

theorem object_fragment0271793_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 433) (SourceJson.white (fragment0271793Field000Chars00 ++ tail)) fragment0271793Acc00000 =
      SourceJson.object (fuel + 432) (SourceJson.white tail) fragment0271793Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271793_object_field_000"
  err.flush

noncomputable def fragment0271793Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0271793Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '1']), .number (String.ofList ['3']), .number (String.ofList ['0'])]
noncomputable def fragment0271793Acc00200 : List (String × SourceJson) := (fragment0271793Field001Key00, fragment0271793Field001Value00) :: fragment0271793Acc00100
noncomputable def fragment0271793Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0271793_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 432) (SourceJson.white (fragment0271793Field001Chars00 ++ tail)) fragment0271793Acc00100 =
      SourceJson.object (fuel + 431) (SourceJson.white tail) fragment0271793Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271793_object_field_001"
  err.flush

noncomputable def fragment0271793Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0271793Field002Value00 : SourceJson := .str (String.ofList ['3', '6', '1', '6', '7', '4', '9', '7', '9', '4', '3', '2', '5', '7', '4', '9', '4', '1', '2', '1', '6', '2', '9', '8', '4', '1', '2', '8', '9', '7', '9', '0', '1', '6', '0', '7', '2', '3', '/', '2', '5', '4', '4', '9', '7', '7', '5', '6', '5', '8', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0271793Acc00300 : List (String × SourceJson) := (fragment0271793Field002Key00, fragment0271793Field002Value00) :: fragment0271793Acc00200
noncomputable def fragment0271793Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '6', '1', '6', '7', '4', '9', '7', '9', '4', '3', '2', '5', '7', '4', '9', '4', '1', '2', '1', '6', '2', '9', '8', '4', '1', '2', '8', '9', '7', '9', '0', '1', '6', '0', '7', '2', '3', '/', '2', '5', '4', '4', '9', '7', '7', '5', '6', '5', '8', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0271793_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 431) (SourceJson.white (fragment0271793Field002Chars00 ++ tail)) fragment0271793Acc00200 =
      SourceJson.object (fuel + 430) (SourceJson.white tail) fragment0271793Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271793_object_field_002"
  err.flush

noncomputable def fragment0271793Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0271793Field003Value00 : SourceJson := .str (String.ofList ['3', '1', '7', '2', '9', '3', '8', '7', '/', '2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0271793Acc00400 : List (String × SourceJson) := (fragment0271793Field003Key00, fragment0271793Field003Value00) :: fragment0271793Acc00300
noncomputable def fragment0271793Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '1', '7', '2', '9', '3', '8', '7', '/', '2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0271793_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 430) (SourceJson.white (fragment0271793Field003Chars00 ++ tail)) fragment0271793Acc00300 =
      SourceJson.object (fuel + 429) (SourceJson.white tail) fragment0271793Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271793_object_field_003"
  err.flush

noncomputable def fragment0271793Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0271793Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0271793Acc00500 : List (String × SourceJson) := (fragment0271793Field004Key00, fragment0271793Field004Value00) :: fragment0271793Acc00400
noncomputable def fragment0271793Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0271793_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 429) (SourceJson.white (fragment0271793Field004Chars00 ++ tail)) fragment0271793Acc00400 =
      SourceJson.object (fuel + 428) (SourceJson.white tail) fragment0271793Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271793_object_field_004"
  err.flush

noncomputable def fragment0271793Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0271793Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '0', '5', '6', '0', '4', '7', '9', '1', '2', '6', '7', '0', '5', '1', '6', '1', '2', '3', '4', '4', '6', '1', '/', '5', '8', '2', '8', '0', '8', '6', '6', '7', '5', '8', '0', '4', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '3', '3', '3', '5', '9', '4', '2', '0', '1', '2', '3', '3', '5', '7', '5', '9', '7', '3', '7', '7', '/', '1', '4', '5', '7', '0', '2', '1', '6', '6', '8', '9', '5', '1', '2', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '8', '2', '1', '4', '7', '1', '1', '7', '0', '4', '4', '9', '5', '4', '2', '6', '9', '7', '8', '7', '/', '1', '6', '6', '5', '1', '6', '7', '6', '2', '1', '6', '5', '8', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '0', '2', '4', '3', '5', '2', '9', '6', '3', '3', '6', '2', '8', '4', '7', '8', '2', '3', '9', '2', '1', '/', '1', '9', '4', '2', '6', '9', '5', '5', '5', '8', '6', '0', '1', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '7', '2', '9', '2', '8', '0', '2', '3', '7', '3', '5', '8', '7', '4', '9', '7', '3', '7', '8', '7', '/', '6', '4', '7', '5', '6', '5', '1', '8', '6', '2', '0', '0', '5', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '3', '7', '6', '3', '1', '4', '6', '6', '2', '1', '9', '0', '8', '1', '7', '6', '3', '1', '3', '/', '7', '5', '6', '8', '9', '4', '3', '7', '3', '4', '8', '1', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '4', '1', '8', '1', '7', '2', '8', '7', '1', '9', '1', '2', '3', '2', '4', '6', '2', '8', '1', '1', '/', '1', '0', '5', '9', '6', '5', '2', '1', '2', '2', '8', '7', '3', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '7', '6', '2', '6', '6', '0', '6', '9', '9', '4', '7', '8', '1', '4', '7', '2', '9', '2', '5', '1', '/', '1', '0', '5', '9', '6', '5', '2', '1', '2', '2', '8', '7', '3', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '7', '2', '1', '2', '3', '3', '1', '5', '5', '3', '9', '8', '6', '7', '3', '8', '1', '5', '2', '3', '/', '5', '2', '9', '8', '2', '6', '0', '6', '1', '4', '3', '6', '8', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '1', '2', '2', '9', '3', '2', '3', '2', '8', '4', '9', '1', '3', '8', '8', '1', '6', '8', '1', '9', '/', '1', '4', '5', '7', '0', '2', '1', '6', '6', '8', '9', '5', '1', '2', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0271793Acc00600 : List (String × SourceJson) := (fragment0271793Field005Key00, fragment0271793Field005Value00) :: fragment0271793Acc00500
noncomputable def fragment0271793Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '5', '6', '0', '4', '7', '9', '1', '2', '6', '7', '0', '5', '1', '6', '1', '2', '3', '4', '4', '6', '1', '/', '5', '8', '2', '8', '0', '8', '6', '6', '7', '5', '8', '0', '4', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '3', '3', '3', '5', '9', '4', '2', '0', '1', '2', '3', '3', '5', '7', '5', '9', '7', '3', '7', '7', '/', '1', '4', '5', '7', '0', '2', '1', '6', '6', '8', '9', '5', '1', '2', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '8', '2', '1', '4', '7', '1', '1', '7', '0', '4', '4', '9', '5', '4', '2', '6', '9', '7', '8', '7', '/', '1', '6', '6', '5', '1', '6', '7', '6', '2', '1', '6', '5', '8', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '0', '2', '4', '3', '5', '2', '9', '6', '3', '3', '6', '2', '8', '4', '7', '8', '2', '3', '9', '2', '1', '/', '1', '9', '4', '2', '6', '9', '5', '5', '5', '8', '6', '0', '1', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '7', '2', '9', '2', '8', '0', '2', '3', '7', '3', '5', '8', '7', '4', '9', '7', '3', '7', '8', '7', '/', '6', '4', '7', '5', '6', '5', '1', '8', '6', '2', '0', '0', '5', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '3', '7', '6', '3', '1', '4', '6', '6', '2', '1', '9', '0', '8', '1', '7', '6', '3', '1', '3', '/', '7', '5', '6', '8', '9', '4', '3', '7', '3', '4', '8', '1', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '4', '1', '8', '1', '7', '2', '8', '7', '1', '9', '1', '2', '3', '2', '4', '6', '2', '8', '1', '1', '/', '1', '0', '5', '9', '6', '5', '2', '1', '2', '2', '8', '7', '3', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '7', '6', '2', '6', '6', '0', '6', '9', '9', '4', '7', '8', '1', '4', '7', '2', '9', '2', '5', '1', '/', '1', '0', '5', '9', '6', '5', '2', '1', '2', '2', '8', '7', '3', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '2', '1', '2', '3', '3', '1', '5', '5', '3', '9', '8', '6', '7', '3', '8', '1', '5', '2', '3', '/', '5', '2', '9', '8', '2', '6', '0', '6', '1', '4', '3', '6', '8', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '1', '2', '2', '9', '3', '2', '3', '2', '8', '4', '9', '1', '3', '8', '8', '1', '6', '8', '1', '9', '/', '1', '4', '5', '7', '0', '2', '1', '6', '6', '8', '9', '5', '1', '2', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0271793_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 428) (SourceJson.white (fragment0271793Field005Chars00 ++ tail)) fragment0271793Acc00500 =
      SourceJson.object (fuel + 427) (SourceJson.white tail) fragment0271793Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271793_object_field_005"
  err.flush

noncomputable def fragment0271793Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0271793Field006Value00 : SourceJson := .str (String.ofList ['4', '2', '5', '7', '3', '9', '9', '2', '7', '9', '2', '1', '9', '2', '1', '3', '4', '6', '3', '2', '8', '2', '1', '4', '2', '7', '8', '6', '1', '9', '0', '1', '9', '3', '8', '5', '9', '4', '4', '8', '8', '4', '7', '6', '6', '0', '9', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '8', '1', '4', '1', '2', '5', '9', '0', '0', '3', '8', '2', '0', '1', '6', '7', '7', '1', '0', '2', '4', '9', '9', '3', '1', '7', '0', '5', '8', '2', '5', '9', '7', '6', '7', '9', '5', '6', '5', '4', '0', '6', '6', '5', '4', '2', '0', '2', '5', '4', '5', '5', '8', '9', '1', '3', '9', '2', '7', '6', '8', '7', '6', '9', '7', '1'])
noncomputable def fragment0271793Acc00700 : List (String × SourceJson) := (fragment0271793Field006Key00, fragment0271793Field006Value00) :: fragment0271793Acc00600
noncomputable def fragment0271793Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '2', '5', '7', '3', '9', '9', '2', '7', '9', '2', '1', '9', '2', '1', '3', '4', '6', '3', '2', '8', '2', '1', '4', '2', '7', '8', '6', '1', '9', '0', '1', '9', '3', '8', '5', '9', '4', '4', '8', '8', '4', '7', '6', '6', '0', '9', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '8', '1', '4', '1', '2', '5', '9', '0', '0', '3', '8', '2', '0', '1', '6', '7', '7', '1', '0', '2', '4', '9', '9', '3', '1', '7', '0', '5', '8', '2', '5', '9', '7', '6', '7', '9', '5', '6', '5', '4', '0', '6', '6', '5', '4', '2', '0', '2', '5', '4', '5', '5', '8', '9', '1', '3', '9', '2', '7', '6', '8', '7', '6', '9', '7', '1', '"', ',']

theorem object_fragment0271793_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 427) (SourceJson.white (fragment0271793Field006Chars00 ++ tail)) fragment0271793Acc00600 =
      SourceJson.object (fuel + 426) (SourceJson.white tail) fragment0271793Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271793_object_field_006"
  err.flush

noncomputable def fragment0271793Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0271793Field007Value00 : SourceJson := .str (String.ofList ['1', '4', '1', '2', '8', '1', '0', '5', '3', '6', '9', '5', '7', '5', '6', '5', '3', '6', '6', '8', '6', '0', '1', '2', '6', '1', '6', '3', '3', '7', '6', '4', '0', '7', '2', '6', '4', '3', '2', '5', '3', '9', '4', '9', '8', '8', '0', '3', '0', '9', '5', '3', '0', '0', '8', '7', '1', '6', '2', '8', '3', '4', '4', '0', '9', '8', '9', '6', '4', '9', '1', '8', '3', '2', '3', '2', '8', '1', '6', '6', '7', '9', '6', '1', '8', '1', '5', '7', '8', '5', '6', '5', '9', '6', '4', '8', '5', '4', '8', '0', '1', '1', '5', '9', '3', '3', '6', '5', '2', '3', '9', '4', '2', '4', '6', '7', '4', '1', '5', '6', '4', '2', '9', '9', '3', '1', '1', '7', '4', '5', '0', '1', '3', '0', '2', '6', '5', '0', '7', '0', '1', '8', '5', '9', '5', '9', '3', '6', '9', '4', '2', '8', '8', '2', '3', '9', '8', '2', '7', '5', '5', '4', '6', '4', '2', '9', '6', '8', '5', '8', '2', '7', '8', '9', '4', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '2', '9', '5', '1', '8', '6', '8', '5', '2', '1', '3', '3', '8', '6', '4', '7', '2', '0', '1', '9', '0', '3', '5', '3', '7', '1', '0', '5', '0', '9', '1', '8', '7', '0', '0', '1', '2', '1', '1', '8', '6', '7', '3', '2', '3', '2', '9', '3', '3', '5', '4', '6', '2', '4', '0', '4', '9', '4', '6', '2', '4', '3', '2', '4', '7', '8', '7', '1', '4', '8', '8', '0', '0', '3', '9', '0', '5', '4', '7', '7', '2', '8', '8', '0', '2', '5', '0', '5', '4', '2', '0', '8', '2', '2', '4', '4', '1', '2', '7', '1', '4', '0', '8', '9', '9', '9', '5', '6', '2', '5', '5', '6', '1', '6', '9', '6', '2', '4', '3', '3', '7', '8', '8', '3', '6', '5', '7', '4', '8', '7', '0', '3', '1', '7', '5', '5', '1', '5', '2', '6', '9', '5', '6', '6', '9', '5', '6', '3', '0', '6', '1', '8', '7', '0', '4', '2', '6', '9', '2', '2', '9', '9', '4', '5', '7', '2', '4', '9', '7', '7', '3', '8', '0', '0', '7', '8', '2', '5', '2', '1', '8', '2', '2', '3', '1', '5', '7', '3', '1', '9', '4', '0', '2', '3', '6', '8', '6', '5', '7', '5', '6', '8', '9', '8', '5', '5', '2', '3', '5', '7', '6', '0', '7', '3', '9'])
noncomputable def fragment0271793Acc00800 : List (String × SourceJson) := (fragment0271793Field007Key00, fragment0271793Field007Value00) :: fragment0271793Acc00700
noncomputable def fragment0271793Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '1', '2', '8', '1', '0', '5', '3', '6', '9', '5', '7', '5', '6', '5', '3', '6', '6', '8', '6', '0', '1', '2', '6', '1', '6', '3', '3', '7', '6', '4', '0', '7', '2', '6', '4', '3', '2', '5', '3', '9', '4', '9', '8', '8', '0', '3', '0', '9', '5', '3', '0', '0', '8', '7', '1', '6', '2', '8', '3', '4', '4', '0', '9', '8', '9', '6', '4', '9', '1', '8', '3', '2', '3', '2', '8', '1', '6', '6', '7', '9', '6', '1', '8', '1', '5', '7', '8', '5', '6', '5', '9', '6', '4', '8', '5', '4', '8', '0', '1', '1', '5', '9', '3', '3', '6', '5', '2', '3', '9', '4', '2', '4', '6', '7', '4', '1', '5', '6', '4', '2', '9', '9', '3', '1', '1', '7', '4', '5', '0', '1', '3', '0', '2', '6', '5', '0', '7', '0', '1', '8', '5', '9', '5', '9', '3', '6', '9', '4', '2', '8', '8', '2', '3', '9', '8', '2', '7', '5', '5', '4', '6', '4', '2', '9', '6', '8', '5', '8', '2', '7', '8', '9', '4', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '2', '9', '5', '1', '8', '6', '8', '5', '2', '1', '3', '3', '8', '6', '4', '7', '2', '0', '1', '9', '0', '3', '5', '3', '7', '1', '0', '5', '0', '9', '1', '8', '7', '0', '0', '1', '2', '1', '1', '8', '6', '7', '3', '2', '3', '2', '9', '3', '3', '5', '4', '6', '2', '4', '0', '4', '9', '4', '6', '2', '4', '3', '2', '4', '7', '8', '7', '1', '4', '8', '8', '0', '0', '3', '9', '0', '5', '4', '7', '7', '2', '8', '8', '0', '2', '5', '0', '5', '4', '2', '0', '8', '2', '2', '4', '4', '1', '2', '7', '1', '4', '0', '8', '9', '9', '9', '5', '6', '2', '5', '5', '6', '1', '6', '9', '6', '2', '4', '3', '3', '7', '8', '8', '3', '6', '5', '7', '4', '8', '7', '0', '3', '1', '7', '5', '5', '1', '5', '2', '6', '9', '5', '6', '6', '9', '5', '6', '3', '0', '6', '1', '8', '7', '0', '4', '2', '6', '9', '2', '2', '9', '9', '4', '5', '7', '2', '4', '9', '7', '7', '3', '8', '0', '0', '7', '8', '2', '5', '2', '1', '8', '2', '2', '3', '1', '5', '7', '3', '1', '9', '4', '0', '2', '3', '6', '8', '6', '5', '7', '5', '6', '8', '9', '8', '5', '5', '2', '3', '5', '7', '6', '0', '7', '3', '9', '"', ',']

theorem object_fragment0271793_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 426) (SourceJson.white (fragment0271793Field007Chars00 ++ tail)) fragment0271793Acc00700 =
      SourceJson.object (fuel + 425) (SourceJson.white tail) fragment0271793Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271793_object_field_007"
  err.flush

noncomputable def fragment0271793Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0271793Field008Value00 : SourceJson := .str (String.ofList ['3', '1', '1', '9', '1', '2', '3', '3', '1', '2', '3', '1', '6', '6', '8', '1', '3'])
noncomputable def fragment0271793Acc00900 : List (String × SourceJson) := (fragment0271793Field008Key00, fragment0271793Field008Value00) :: fragment0271793Acc00800
noncomputable def fragment0271793Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '1', '9', '1', '2', '3', '3', '1', '2', '3', '1', '6', '6', '8', '1', '3', '"', ',']

theorem object_fragment0271793_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 425) (SourceJson.white (fragment0271793Field008Chars00 ++ tail)) fragment0271793Acc00800 =
      SourceJson.object (fuel + 424) (SourceJson.white tail) fragment0271793Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271793_object_field_008"
  err.flush

noncomputable def fragment0271793Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0271793Field009Value00 : SourceJson := .str (String.ofList ['9', '9', '0', '9', '9', '1', '8', '6', '4', '8', '4', '7', '2', '1', '6', '9', '8'])
noncomputable def fragment0271793Acc01000 : List (String × SourceJson) := (fragment0271793Field009Key00, fragment0271793Field009Value00) :: fragment0271793Acc00900
noncomputable def fragment0271793Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '9', '0', '9', '9', '1', '8', '6', '4', '8', '4', '7', '2', '1', '6', '9', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0271793_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 424) (SourceJson.white (fragment0271793Field009Chars00 ++ tail)) fragment0271793Acc00900 =
      .ok (.obj (fragment0271793Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271793_object_field_009"
  err.flush

noncomputable def fragment0271793Chars : List Char := '{' :: (fragment0271793Field000Chars00 ++ fragment0271793Field001Chars00 ++ fragment0271793Field002Chars00 ++ fragment0271793Field003Chars00 ++ fragment0271793Field004Chars00 ++ fragment0271793Field005Chars00 ++ fragment0271793Field006Chars00 ++ fragment0271793Field007Chars00 ++ fragment0271793Field008Chars00 ++ fragment0271793Field009Chars00)
noncomputable def fragment0271793Value : SourceJson := .obj (fragment0271793Acc01000.reverse)

theorem value_fragment0271793 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 434) (fragment0271793Chars ++ tail) =
      .ok (fragment0271793Value, tail) := by
  have hinput : fragment0271793Chars ++ tail = '{' :: (fragment0271793Field000Chars00 ++ (fragment0271793Field001Chars00 ++ (fragment0271793Field002Chars00 ++ (fragment0271793Field003Chars00 ++ (fragment0271793Field004Chars00 ++ (fragment0271793Field005Chars00 ++ (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0271793Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 434) (fragment0271793Chars ++ tail) =
        SourceJson.value (fuel + 434) ('{' :: (fragment0271793Field000Chars00 ++ (fragment0271793Field001Chars00 ++ (fragment0271793Field002Chars00 ++ (fragment0271793Field003Chars00 ++ (fragment0271793Field004Chars00 ++ (fragment0271793Field005Chars00 ++ (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 434)) hinput
    _ = SourceJson.object (fuel + 433) (SourceJson.white (fragment0271793Field000Chars00 ++ (fragment0271793Field001Chars00 ++ (fragment0271793Field002Chars00 ++ (fragment0271793Field003Chars00 ++ (fragment0271793Field004Chars00 ++ (fragment0271793Field005Chars00 ++ (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail)))))))))))) fragment0271793Acc00000 := by rfl
    _ = SourceJson.object (fuel + 432) (SourceJson.white (fragment0271793Field001Chars00 ++ (fragment0271793Field002Chars00 ++ (fragment0271793Field003Chars00 ++ (fragment0271793Field004Chars00 ++ (fragment0271793Field005Chars00 ++ (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail))))))))))) fragment0271793Acc00100 := object_fragment0271793_field_000 fuel (fragment0271793Field001Chars00 ++ (fragment0271793Field002Chars00 ++ (fragment0271793Field003Chars00 ++ (fragment0271793Field004Chars00 ++ (fragment0271793Field005Chars00 ++ (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 431) (SourceJson.white (fragment0271793Field002Chars00 ++ (fragment0271793Field003Chars00 ++ (fragment0271793Field004Chars00 ++ (fragment0271793Field005Chars00 ++ (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail)))))))))) fragment0271793Acc00200 := object_fragment0271793_field_001 fuel (fragment0271793Field002Chars00 ++ (fragment0271793Field003Chars00 ++ (fragment0271793Field004Chars00 ++ (fragment0271793Field005Chars00 ++ (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 430) (SourceJson.white (fragment0271793Field003Chars00 ++ (fragment0271793Field004Chars00 ++ (fragment0271793Field005Chars00 ++ (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail))))))))) fragment0271793Acc00300 := object_fragment0271793_field_002 fuel (fragment0271793Field003Chars00 ++ (fragment0271793Field004Chars00 ++ (fragment0271793Field005Chars00 ++ (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 429) (SourceJson.white (fragment0271793Field004Chars00 ++ (fragment0271793Field005Chars00 ++ (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail)))))))) fragment0271793Acc00400 := object_fragment0271793_field_003 fuel (fragment0271793Field004Chars00 ++ (fragment0271793Field005Chars00 ++ (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 428) (SourceJson.white (fragment0271793Field005Chars00 ++ (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail))))))) fragment0271793Acc00500 := object_fragment0271793_field_004 fuel (fragment0271793Field005Chars00 ++ (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 427) (SourceJson.white (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail)))))) fragment0271793Acc00600 := object_fragment0271793_field_005 fuel (fragment0271793Field006Chars00 ++ (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 426) (SourceJson.white (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail))))) fragment0271793Acc00700 := object_fragment0271793_field_006 fuel (fragment0271793Field007Chars00 ++ (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 425) (SourceJson.white (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail)))) fragment0271793Acc00800 := object_fragment0271793_field_007 fuel (fragment0271793Field008Chars00 ++ (fragment0271793Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 424) (SourceJson.white (fragment0271793Field009Chars00 ++ (tail))) fragment0271793Acc00900 := object_fragment0271793_field_008 fuel (fragment0271793Field009Chars00 ++ (tail))
    _ = .ok (fragment0271793Value, tail) := object_fragment0271793_field_009 fuel (tail)

noncomputable def fragment0273801Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0273801Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0273801Field000Value00 : SourceJson := .number (String.ofList ['7', '9'])
noncomputable def fragment0273801Acc00100 : List (String × SourceJson) := (fragment0273801Field000Key00, fragment0273801Field000Value00) :: fragment0273801Acc00000
noncomputable def fragment0273801Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '9', ',']

theorem object_fragment0273801_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0273801Field000Chars00 ++ tail)) fragment0273801Acc00000 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0273801Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273801_object_field_000"
  err.flush

noncomputable def fragment0273801Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0273801Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '1']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0273801Acc00200 : List (String × SourceJson) := (fragment0273801Field001Key00, fragment0273801Field001Value00) :: fragment0273801Acc00100
noncomputable def fragment0273801Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0273801_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0273801Field001Chars00 ++ tail)) fragment0273801Acc00100 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0273801Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273801_object_field_001"
  err.flush

noncomputable def fragment0273801Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0273801Field002Value00 : SourceJson := .str (String.ofList ['2', '0', '0', '0', '9', '3', '7', '1', '0', '4', '3', '4', '7', '0', '2', '4', '3', '0', '6', '5', '1', '2', '4', '3', '1', '8', '4', '8', '6', '7', '7', '1', '8', '9', '3', '9', '3', '0', '5', '0', '9', '/', '3', '1', '9', '6', '0', '1', '8', '3', '3', '8', '5', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0273801Acc00300 : List (String × SourceJson) := (fragment0273801Field002Key00, fragment0273801Field002Value00) :: fragment0273801Acc00200
noncomputable def fragment0273801Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '0', '0', '0', '9', '3', '7', '1', '0', '4', '3', '4', '7', '0', '2', '4', '3', '0', '6', '5', '1', '2', '4', '3', '1', '8', '4', '8', '6', '7', '7', '1', '8', '9', '3', '9', '3', '0', '5', '0', '9', '/', '3', '1', '9', '6', '0', '1', '8', '3', '3', '8', '5', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0273801_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0273801Field002Chars00 ++ tail)) fragment0273801Acc00200 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0273801Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273801_object_field_002"
  err.flush

noncomputable def fragment0273801Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0273801Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0273801Acc00400 : List (String × SourceJson) := (fragment0273801Field003Key00, fragment0273801Field003Value00) :: fragment0273801Acc00300
noncomputable def fragment0273801Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0273801_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0273801Field003Chars00 ++ tail)) fragment0273801Acc00300 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0273801Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273801_object_field_003"
  err.flush

noncomputable def fragment0273801Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0273801Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0273801Acc00500 : List (String × SourceJson) := (fragment0273801Field004Key00, fragment0273801Field004Value00) :: fragment0273801Acc00400
noncomputable def fragment0273801Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0273801_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0273801Field004Chars00 ++ tail)) fragment0273801Acc00400 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0273801Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273801_object_field_004"
  err.flush

noncomputable def fragment0273801Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0273801Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '8', '3', '3', '2', '0', '8', '4', '2', '8', '9', '7', '9', '3', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '6', '1', '4', '1', '8', '4', '3', '8', '2', '0', '3', '9', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '8', '2', '7', '1', '9', '4', '4', '5', '5', '2', '9', '/', '1', '8', '3', '0', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '7', '8', '7', '4', '4', '0', '6', '0', '0', '9', '9', '/', '8', '0', '0', '9', '3', '4', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '3', '5', '2', '2', '0', '1', '0', '5', '0', '0', '9', '/', '8', '0', '0', '9', '3', '4', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '0', '7', '7', '3', '4', '0', '9', '5', '3', '4', '7', '/', '8', '3', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '9', '3', '1', '4', '0', '6', '5', '3', '1', '5', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '1', '1', '1', '3', '1', '3', '8', '6', '4', '1', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '4', '9', '0', '7', '9', '3', '0', '1', '2', '1', '/', '2', '9', '1', '2', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '0', '5', '9', '1', '1', '0', '1', '6', '1', '7', '9', '9', '/', '6', '4', '0', '7', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0273801Acc00600 : List (String × SourceJson) := (fragment0273801Field005Key00, fragment0273801Field005Value00) :: fragment0273801Acc00500
noncomputable def fragment0273801Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '3', '2', '0', '8', '4', '2', '8', '9', '7', '9', '3', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '1', '4', '1', '8', '4', '3', '8', '2', '0', '3', '9', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '8', '2', '7', '1', '9', '4', '4', '5', '5', '2', '9', '/', '1', '8', '3', '0', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '7', '8', '7', '4', '4', '0', '6', '0', '0', '9', '9', '/', '8', '0', '0', '9', '3', '4', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '3', '5', '2', '2', '0', '1', '0', '5', '0', '0', '9', '/', '8', '0', '0', '9', '3', '4', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '7', '7', '3', '4', '0', '9', '5', '3', '4', '7', '/', '8', '3', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '9', '3', '1', '4', '0', '6', '5', '3', '1', '5', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '1', '1', '1', '3', '1', '3', '8', '6', '4', '1', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '4', '9', '0', '7', '9', '3', '0', '1', '2', '1', '/', '2', '9', '1', '2', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '5', '9', '1', '1', '0', '1', '6', '1', '7', '9', '9', '/', '6', '4', '0', '7', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0273801_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0273801Field005Chars00 ++ tail)) fragment0273801Acc00500 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0273801Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273801_object_field_005"
  err.flush

noncomputable def fragment0273801Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0273801Field006Value00 : SourceJson := .str (String.ofList ['2', '2', '2', '4', '4', '4', '5', '0', '1', '0', '7', '5', '7', '0', '7', '9', '2', '6', '6', '5', '9', '8', '7', '3', '1', '9', '1', '9', '6', '3', '4', '6', '6', '7', '9', '4', '5', '2', '1', '2', '8', '0', '3', '4', '9', '9', '2', '0', '0', '8', '1', '2', '5', '0', '/', '3', '1', '4', '7', '5', '5', '1', '9', '8', '8', '8', '5', '3', '3', '7', '5', '0', '9', '1', '6', '8', '6', '5', '7', '4', '9', '8', '2', '0', '9', '5', '4', '0', '2', '5', '5', '3', '5', '4', '3', '5', '1', '3', '9', '5', '4', '6', '4', '6', '5', '7', '8', '4', '9', '1', '3', '5', '8', '7', '7', '2', '5', '3', '8', '8', '7'])
noncomputable def fragment0273801Acc00700 : List (String × SourceJson) := (fragment0273801Field006Key00, fragment0273801Field006Value00) :: fragment0273801Acc00600
noncomputable def fragment0273801Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '2', '2', '4', '4', '4', '5', '0', '1', '0', '7', '5', '7', '0', '7', '9', '2', '6', '6', '5', '9', '8', '7', '3', '1', '9', '1', '9', '6', '3', '4', '6', '6', '7', '9', '4', '5', '2', '1', '2', '8', '0', '3', '4', '9', '9', '2', '0', '0', '8', '1', '2', '5', '0', '/', '3', '1', '4', '7', '5', '5', '1', '9', '8', '8', '8', '5', '3', '3', '7', '5', '0', '9', '1', '6', '8', '6', '5', '7', '4', '9', '8', '2', '0', '9', '5', '4', '0', '2', '5', '5', '3', '5', '4', '3', '5', '1', '3', '9', '5', '4', '6', '4', '6', '5', '7', '8', '4', '9', '1', '3', '5', '8', '7', '7', '2', '5', '3', '8', '8', '7', '"', ',']

theorem object_fragment0273801_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0273801Field006Chars00 ++ tail)) fragment0273801Acc00600 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0273801Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273801_object_field_006"
  err.flush

noncomputable def fragment0273801Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0273801Field007Value00 : SourceJson := .str (String.ofList ['7', '2', '2', '9', '5', '1', '3', '0', '8', '4', '5', '1', '7', '0', '3', '3', '8', '7', '5', '4', '0', '9', '3', '1', '4', '3', '8', '4', '6', '3', '4', '2', '4', '7', '1', '5', '8', '1', '1', '1', '7', '4', '7', '3', '8', '5', '5', '3', '5', '8', '6', '1', '0', '6', '1', '7', '6', '2', '9', '7', '5', '1', '6', '7', '6', '3', '9', '3', '3', '2', '6', '1', '5', '9', '5', '2', '3', '1', '1', '9', '6', '7', '5', '3', '3', '3', '2', '4', '2', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '7', '1', '3', '3', '7', '4', '0', '3', '1', '2', '0', '7', '8', '6', '6', '6', '8', '4', '1', '4', '4', '2', '7', '7', '5', '8', '7', '9', '8', '9', '6', '0', '4', '5', '0', '2', '4', '4', '6', '2', '6', '7', '6', '0', '6', '3', '7', '4', '0', '7', '7', '3', '8', '4', '1', '2', '6', '0', '9', '4', '4', '1', '4', '5', '5', '2', '4', '7', '9', '5', '7', '6', '0', '5', '4', '9', '1', '8', '7', '8', '4', '8', '8', '7', '6', '9', '8', '4', '7', '8', '0', '6', '7', '4', '1', '0', '3', '1', '1', '6', '8', '1', '2', '7', '8', '2', '1', '8', '2', '8', '3', '1', '7', '1', '3', '2', '1', '5', '8', '4', '7', '9', '8', '7'])
noncomputable def fragment0273801Acc00800 : List (String × SourceJson) := (fragment0273801Field007Key00, fragment0273801Field007Value00) :: fragment0273801Acc00700
noncomputable def fragment0273801Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '2', '2', '9', '5', '1', '3', '0', '8', '4', '5', '1', '7', '0', '3', '3', '8', '7', '5', '4', '0', '9', '3', '1', '4', '3', '8', '4', '6', '3', '4', '2', '4', '7', '1', '5', '8', '1', '1', '1', '7', '4', '7', '3', '8', '5', '5', '3', '5', '8', '6', '1', '0', '6', '1', '7', '6', '2', '9', '7', '5', '1', '6', '7', '6', '3', '9', '3', '3', '2', '6', '1', '5', '9', '5', '2', '3', '1', '1', '9', '6', '7', '5', '3', '3', '3', '2', '4', '2', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '7', '1', '3', '3', '7', '4', '0', '3', '1', '2', '0', '7', '8', '6', '6', '6', '8', '4', '1', '4', '4', '2', '7', '7', '5', '8', '7', '9', '8', '9', '6', '0', '4', '5', '0', '2', '4', '4', '6', '2', '6', '7', '6', '0', '6', '3', '7', '4', '0', '7', '7', '3', '8', '4', '1', '2', '6', '0', '9', '4', '4', '1', '4', '5', '5', '2', '4', '7', '9', '5', '7', '6', '0', '5', '4', '9', '1', '8', '7', '8', '4', '8', '8', '7', '6', '9', '8', '4', '7', '8', '0', '6', '7', '4', '1', '0', '3', '1', '1', '6', '8', '1', '2', '7', '8', '2', '1', '8', '2', '8', '3', '1', '7', '1', '3', '2', '1', '5', '8', '4', '7', '9', '8', '7', '"', ',']

theorem object_fragment0273801_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0273801Field007Chars00 ++ tail)) fragment0273801Acc00700 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0273801Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273801_object_field_007"
  err.flush

noncomputable def fragment0273801Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0273801Field008Value00 : SourceJson := .str (String.ofList ['5', '5', '9', '9', '2', '3', '0', '4', '9', '5', '3', '3', '1', '9', '7', '7', '9'])
noncomputable def fragment0273801Acc00900 : List (String × SourceJson) := (fragment0273801Field008Key00, fragment0273801Field008Value00) :: fragment0273801Acc00800
noncomputable def fragment0273801Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '5', '9', '9', '2', '3', '0', '4', '9', '5', '3', '3', '1', '9', '7', '7', '9', '"', ',']

theorem object_fragment0273801_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0273801Field008Chars00 ++ tail)) fragment0273801Acc00800 =
      SourceJson.object (fuel + 240) (SourceJson.white tail) fragment0273801Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273801_object_field_008"
  err.flush

noncomputable def fragment0273801Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0273801Field009Value00 : SourceJson := .str (String.ofList ['2', '1', '1', '0', '9', '5', '4', '9', '6', '2', '2', '3', '9', '9', '1', '2', '0', '2'])
noncomputable def fragment0273801Acc01000 : List (String × SourceJson) := (fragment0273801Field009Key00, fragment0273801Field009Value00) :: fragment0273801Acc00900
noncomputable def fragment0273801Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '1', '1', '0', '9', '5', '4', '9', '6', '2', '2', '3', '9', '9', '1', '2', '0', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0273801_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 240) (SourceJson.white (fragment0273801Field009Chars00 ++ tail)) fragment0273801Acc00900 =
      .ok (.obj (fragment0273801Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273801_object_field_009"
  err.flush

noncomputable def fragment0273801Chars : List Char := '{' :: (fragment0273801Field000Chars00 ++ fragment0273801Field001Chars00 ++ fragment0273801Field002Chars00 ++ fragment0273801Field003Chars00 ++ fragment0273801Field004Chars00 ++ fragment0273801Field005Chars00 ++ fragment0273801Field006Chars00 ++ fragment0273801Field007Chars00 ++ fragment0273801Field008Chars00 ++ fragment0273801Field009Chars00)
noncomputable def fragment0273801Value : SourceJson := .obj (fragment0273801Acc01000.reverse)

theorem value_fragment0273801 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 250) (fragment0273801Chars ++ tail) =
      .ok (fragment0273801Value, tail) := by
  have hinput : fragment0273801Chars ++ tail = '{' :: (fragment0273801Field000Chars00 ++ (fragment0273801Field001Chars00 ++ (fragment0273801Field002Chars00 ++ (fragment0273801Field003Chars00 ++ (fragment0273801Field004Chars00 ++ (fragment0273801Field005Chars00 ++ (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0273801Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 250) (fragment0273801Chars ++ tail) =
        SourceJson.value (fuel + 250) ('{' :: (fragment0273801Field000Chars00 ++ (fragment0273801Field001Chars00 ++ (fragment0273801Field002Chars00 ++ (fragment0273801Field003Chars00 ++ (fragment0273801Field004Chars00 ++ (fragment0273801Field005Chars00 ++ (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 250)) hinput
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0273801Field000Chars00 ++ (fragment0273801Field001Chars00 ++ (fragment0273801Field002Chars00 ++ (fragment0273801Field003Chars00 ++ (fragment0273801Field004Chars00 ++ (fragment0273801Field005Chars00 ++ (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail)))))))))))) fragment0273801Acc00000 := by rfl
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0273801Field001Chars00 ++ (fragment0273801Field002Chars00 ++ (fragment0273801Field003Chars00 ++ (fragment0273801Field004Chars00 ++ (fragment0273801Field005Chars00 ++ (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail))))))))))) fragment0273801Acc00100 := object_fragment0273801_field_000 fuel (fragment0273801Field001Chars00 ++ (fragment0273801Field002Chars00 ++ (fragment0273801Field003Chars00 ++ (fragment0273801Field004Chars00 ++ (fragment0273801Field005Chars00 ++ (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0273801Field002Chars00 ++ (fragment0273801Field003Chars00 ++ (fragment0273801Field004Chars00 ++ (fragment0273801Field005Chars00 ++ (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail)))))))))) fragment0273801Acc00200 := object_fragment0273801_field_001 fuel (fragment0273801Field002Chars00 ++ (fragment0273801Field003Chars00 ++ (fragment0273801Field004Chars00 ++ (fragment0273801Field005Chars00 ++ (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0273801Field003Chars00 ++ (fragment0273801Field004Chars00 ++ (fragment0273801Field005Chars00 ++ (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail))))))))) fragment0273801Acc00300 := object_fragment0273801_field_002 fuel (fragment0273801Field003Chars00 ++ (fragment0273801Field004Chars00 ++ (fragment0273801Field005Chars00 ++ (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0273801Field004Chars00 ++ (fragment0273801Field005Chars00 ++ (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail)))))))) fragment0273801Acc00400 := object_fragment0273801_field_003 fuel (fragment0273801Field004Chars00 ++ (fragment0273801Field005Chars00 ++ (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0273801Field005Chars00 ++ (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail))))))) fragment0273801Acc00500 := object_fragment0273801_field_004 fuel (fragment0273801Field005Chars00 ++ (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail)))))) fragment0273801Acc00600 := object_fragment0273801_field_005 fuel (fragment0273801Field006Chars00 ++ (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail))))) fragment0273801Acc00700 := object_fragment0273801_field_006 fuel (fragment0273801Field007Chars00 ++ (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail)))) fragment0273801Acc00800 := object_fragment0273801_field_007 fuel (fragment0273801Field008Chars00 ++ (fragment0273801Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 240) (SourceJson.white (fragment0273801Field009Chars00 ++ (tail))) fragment0273801Acc00900 := object_fragment0273801_field_008 fuel (fragment0273801Field009Chars00 ++ (tail))
    _ = .ok (fragment0273801Value, tail) := object_fragment0273801_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0072_before_reader"
  err.flush

noncomputable def chunk0072LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0072SuffixChars00 : List Char := [',']
noncomputable def chunk0072Chars00 : List Char := chunk0072LeadChars00 ++ fragment0261427Chars ++ chunk0072SuffixChars00
noncomputable def chunk0072Push00 (acc : List SourceJson) : List SourceJson := fragment0261427Value :: acc

noncomputable def chunk0072AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0072_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 585)
      (SourceJson.white (chunk0072LeadChars00 ++ (fragment0261427Chars ++ rest))) acc =
      (SourceJson.value (fuel + 584) (fragment0261427Chars ++ rest)).bind
        (chunk0072AfterValue00 (fuel + 584) acc) := by rfl

theorem array_chunk0072 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 585) (SourceJson.white (chunk0072Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 584) (SourceJson.white tail) (chunk0072Push00 acc) := by
  have hinput : chunk0072Chars00 ++ tail = chunk0072LeadChars00 ++ (fragment0261427Chars ++ (chunk0072SuffixChars00 ++ tail)) := by
    simp only [chunk0072Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 585) (SourceJson.white (chunk0072Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 585)
          (SourceJson.white (chunk0072LeadChars00 ++ (fragment0261427Chars ++ (chunk0072SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 585) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 584) (fragment0261427Chars ++ (chunk0072SuffixChars00 ++ tail))).bind
        (chunk0072AfterValue00 (fuel + 584) acc) := array_chunk0072_head fuel (chunk0072SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0261427Value, chunk0072SuffixChars00 ++ tail)).bind
        (chunk0072AfterValue00 (fuel + 584) acc) :=
      congrArg (fun result => result.bind (chunk0072AfterValue00 (fuel + 584) acc))
        (value_fragment0261427 (fuel + 202) (chunk0072SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 584) (SourceJson.white tail) (chunk0072Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0072_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0073_before_reader"
  err.flush

noncomputable def chunk0073LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0073SuffixChars00 : List Char := [',']
noncomputable def chunk0073Chars00 : List Char := chunk0073LeadChars00 ++ fragment0263305Chars ++ chunk0073SuffixChars00
noncomputable def chunk0073Push00 (acc : List SourceJson) : List SourceJson := fragment0263305Value :: acc

noncomputable def chunk0073AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0073_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 584)
      (SourceJson.white (chunk0073LeadChars00 ++ (fragment0263305Chars ++ rest))) acc =
      (SourceJson.value (fuel + 583) (fragment0263305Chars ++ rest)).bind
        (chunk0073AfterValue00 (fuel + 583) acc) := by rfl

theorem array_chunk0073 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 584) (SourceJson.white (chunk0073Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 583) (SourceJson.white tail) (chunk0073Push00 acc) := by
  have hinput : chunk0073Chars00 ++ tail = chunk0073LeadChars00 ++ (fragment0263305Chars ++ (chunk0073SuffixChars00 ++ tail)) := by
    simp only [chunk0073Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 584) (SourceJson.white (chunk0073Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 584)
          (SourceJson.white (chunk0073LeadChars00 ++ (fragment0263305Chars ++ (chunk0073SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 584) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 583) (fragment0263305Chars ++ (chunk0073SuffixChars00 ++ tail))).bind
        (chunk0073AfterValue00 (fuel + 583) acc) := array_chunk0073_head fuel (chunk0073SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0263305Value, chunk0073SuffixChars00 ++ tail)).bind
        (chunk0073AfterValue00 (fuel + 583) acc) :=
      congrArg (fun result => result.bind (chunk0073AfterValue00 (fuel + 583) acc))
        (value_fragment0263305 (fuel + 381) (chunk0073SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 583) (SourceJson.white tail) (chunk0073Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0073_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0074_before_reader"
  err.flush

noncomputable def chunk0074LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0074SuffixChars00 : List Char := [',']
noncomputable def chunk0074Chars00 : List Char := chunk0074LeadChars00 ++ fragment0264837Chars ++ chunk0074SuffixChars00
noncomputable def chunk0074Push00 (acc : List SourceJson) : List SourceJson := fragment0264837Value :: acc

noncomputable def chunk0074AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0074_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 583)
      (SourceJson.white (chunk0074LeadChars00 ++ (fragment0264837Chars ++ rest))) acc =
      (SourceJson.value (fuel + 582) (fragment0264837Chars ++ rest)).bind
        (chunk0074AfterValue00 (fuel + 582) acc) := by rfl

theorem array_chunk0074 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 583) (SourceJson.white (chunk0074Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 582) (SourceJson.white tail) (chunk0074Push00 acc) := by
  have hinput : chunk0074Chars00 ++ tail = chunk0074LeadChars00 ++ (fragment0264837Chars ++ (chunk0074SuffixChars00 ++ tail)) := by
    simp only [chunk0074Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 583) (SourceJson.white (chunk0074Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 583)
          (SourceJson.white (chunk0074LeadChars00 ++ (fragment0264837Chars ++ (chunk0074SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 583) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 582) (fragment0264837Chars ++ (chunk0074SuffixChars00 ++ tail))).bind
        (chunk0074AfterValue00 (fuel + 582) acc) := array_chunk0074_head fuel (chunk0074SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0264837Value, chunk0074SuffixChars00 ++ tail)).bind
        (chunk0074AfterValue00 (fuel + 582) acc) :=
      congrArg (fun result => result.bind (chunk0074AfterValue00 (fuel + 582) acc))
        (value_fragment0264837 (fuel + 222) (chunk0074SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 582) (SourceJson.white tail) (chunk0074Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0074_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0075_before_reader"
  err.flush

noncomputable def chunk0075LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0075SuffixChars00 : List Char := [',']
noncomputable def chunk0075Chars00 : List Char := chunk0075LeadChars00 ++ fragment0266682Chars ++ chunk0075SuffixChars00
noncomputable def chunk0075Push00 (acc : List SourceJson) : List SourceJson := fragment0266682Value :: acc

noncomputable def chunk0075AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0075_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 582)
      (SourceJson.white (chunk0075LeadChars00 ++ (fragment0266682Chars ++ rest))) acc =
      (SourceJson.value (fuel + 581) (fragment0266682Chars ++ rest)).bind
        (chunk0075AfterValue00 (fuel + 581) acc) := by rfl

theorem array_chunk0075 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 582) (SourceJson.white (chunk0075Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 581) (SourceJson.white tail) (chunk0075Push00 acc) := by
  have hinput : chunk0075Chars00 ++ tail = chunk0075LeadChars00 ++ (fragment0266682Chars ++ (chunk0075SuffixChars00 ++ tail)) := by
    simp only [chunk0075Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 582) (SourceJson.white (chunk0075Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 582)
          (SourceJson.white (chunk0075LeadChars00 ++ (fragment0266682Chars ++ (chunk0075SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 582) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 581) (fragment0266682Chars ++ (chunk0075SuffixChars00 ++ tail))).bind
        (chunk0075AfterValue00 (fuel + 581) acc) := array_chunk0075_head fuel (chunk0075SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0266682Value, chunk0075SuffixChars00 ++ tail)).bind
        (chunk0075AfterValue00 (fuel + 581) acc) :=
      congrArg (fun result => result.bind (chunk0075AfterValue00 (fuel + 581) acc))
        (value_fragment0266682 (fuel + 381) (chunk0075SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 581) (SourceJson.white tail) (chunk0075Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0075_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0076_before_reader"
  err.flush

noncomputable def chunk0076LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0076SuffixChars00 : List Char := [',']
noncomputable def chunk0076Chars00 : List Char := chunk0076LeadChars00 ++ fragment0268202Chars ++ chunk0076SuffixChars00
noncomputable def chunk0076Push00 (acc : List SourceJson) : List SourceJson := fragment0268202Value :: acc

noncomputable def chunk0076AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0076_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 581)
      (SourceJson.white (chunk0076LeadChars00 ++ (fragment0268202Chars ++ rest))) acc =
      (SourceJson.value (fuel + 580) (fragment0268202Chars ++ rest)).bind
        (chunk0076AfterValue00 (fuel + 580) acc) := by rfl

theorem array_chunk0076 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 581) (SourceJson.white (chunk0076Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 580) (SourceJson.white tail) (chunk0076Push00 acc) := by
  have hinput : chunk0076Chars00 ++ tail = chunk0076LeadChars00 ++ (fragment0268202Chars ++ (chunk0076SuffixChars00 ++ tail)) := by
    simp only [chunk0076Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 581) (SourceJson.white (chunk0076Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 581)
          (SourceJson.white (chunk0076LeadChars00 ++ (fragment0268202Chars ++ (chunk0076SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 581) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 580) (fragment0268202Chars ++ (chunk0076SuffixChars00 ++ tail))).bind
        (chunk0076AfterValue00 (fuel + 580) acc) := array_chunk0076_head fuel (chunk0076SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0268202Value, chunk0076SuffixChars00 ++ tail)).bind
        (chunk0076AfterValue00 (fuel + 580) acc) :=
      congrArg (fun result => result.bind (chunk0076AfterValue00 (fuel + 580) acc))
        (value_fragment0268202 (fuel + 370) (chunk0076SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 580) (SourceJson.white tail) (chunk0076Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0076_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0077_before_reader"
  err.flush

noncomputable def chunk0077LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0077SuffixChars00 : List Char := [',']
noncomputable def chunk0077Chars00 : List Char := chunk0077LeadChars00 ++ fragment0269747Chars ++ chunk0077SuffixChars00
noncomputable def chunk0077Push00 (acc : List SourceJson) : List SourceJson := fragment0269747Value :: acc

noncomputable def chunk0077AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0077_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 580)
      (SourceJson.white (chunk0077LeadChars00 ++ (fragment0269747Chars ++ rest))) acc =
      (SourceJson.value (fuel + 579) (fragment0269747Chars ++ rest)).bind
        (chunk0077AfterValue00 (fuel + 579) acc) := by rfl

theorem array_chunk0077 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 580) (SourceJson.white (chunk0077Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 579) (SourceJson.white tail) (chunk0077Push00 acc) := by
  have hinput : chunk0077Chars00 ++ tail = chunk0077LeadChars00 ++ (fragment0269747Chars ++ (chunk0077SuffixChars00 ++ tail)) := by
    simp only [chunk0077Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 580) (SourceJson.white (chunk0077Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 580)
          (SourceJson.white (chunk0077LeadChars00 ++ (fragment0269747Chars ++ (chunk0077SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 580) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 579) (fragment0269747Chars ++ (chunk0077SuffixChars00 ++ tail))).bind
        (chunk0077AfterValue00 (fuel + 579) acc) := array_chunk0077_head fuel (chunk0077SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0269747Value, chunk0077SuffixChars00 ++ tail)).bind
        (chunk0077AfterValue00 (fuel + 579) acc) :=
      congrArg (fun result => result.bind (chunk0077AfterValue00 (fuel + 579) acc))
        (value_fragment0269747 (fuel + 126) (chunk0077SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 579) (SourceJson.white tail) (chunk0077Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0077_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0078_before_reader"
  err.flush

noncomputable def chunk0078LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0078SuffixChars00 : List Char := [',']
noncomputable def chunk0078Chars00 : List Char := chunk0078LeadChars00 ++ fragment0271793Chars ++ chunk0078SuffixChars00
noncomputable def chunk0078Push00 (acc : List SourceJson) : List SourceJson := fragment0271793Value :: acc

noncomputable def chunk0078AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0078_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 579)
      (SourceJson.white (chunk0078LeadChars00 ++ (fragment0271793Chars ++ rest))) acc =
      (SourceJson.value (fuel + 578) (fragment0271793Chars ++ rest)).bind
        (chunk0078AfterValue00 (fuel + 578) acc) := by rfl

theorem array_chunk0078 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 579) (SourceJson.white (chunk0078Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 578) (SourceJson.white tail) (chunk0078Push00 acc) := by
  have hinput : chunk0078Chars00 ++ tail = chunk0078LeadChars00 ++ (fragment0271793Chars ++ (chunk0078SuffixChars00 ++ tail)) := by
    simp only [chunk0078Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 579) (SourceJson.white (chunk0078Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 579)
          (SourceJson.white (chunk0078LeadChars00 ++ (fragment0271793Chars ++ (chunk0078SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 579) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 578) (fragment0271793Chars ++ (chunk0078SuffixChars00 ++ tail))).bind
        (chunk0078AfterValue00 (fuel + 578) acc) := array_chunk0078_head fuel (chunk0078SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0271793Value, chunk0078SuffixChars00 ++ tail)).bind
        (chunk0078AfterValue00 (fuel + 578) acc) :=
      congrArg (fun result => result.bind (chunk0078AfterValue00 (fuel + 578) acc))
        (value_fragment0271793 (fuel + 144) (chunk0078SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 578) (SourceJson.white tail) (chunk0078Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0078_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0079_before_reader"
  err.flush

noncomputable def chunk0079LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0079SuffixChars00 : List Char := [',']
noncomputable def chunk0079Chars00 : List Char := chunk0079LeadChars00 ++ fragment0273801Chars ++ chunk0079SuffixChars00
noncomputable def chunk0079Push00 (acc : List SourceJson) : List SourceJson := fragment0273801Value :: acc

noncomputable def chunk0079AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0079_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 578)
      (SourceJson.white (chunk0079LeadChars00 ++ (fragment0273801Chars ++ rest))) acc =
      (SourceJson.value (fuel + 577) (fragment0273801Chars ++ rest)).bind
        (chunk0079AfterValue00 (fuel + 577) acc) := by rfl

theorem array_chunk0079 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 578) (SourceJson.white (chunk0079Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 577) (SourceJson.white tail) (chunk0079Push00 acc) := by
  have hinput : chunk0079Chars00 ++ tail = chunk0079LeadChars00 ++ (fragment0273801Chars ++ (chunk0079SuffixChars00 ++ tail)) := by
    simp only [chunk0079Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 578) (SourceJson.white (chunk0079Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 578)
          (SourceJson.white (chunk0079LeadChars00 ++ (fragment0273801Chars ++ (chunk0079SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 578) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 577) (fragment0273801Chars ++ (chunk0079SuffixChars00 ++ tail))).bind
        (chunk0079AfterValue00 (fuel + 577) acc) := array_chunk0079_head fuel (chunk0079SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0273801Value, chunk0079SuffixChars00 ++ tail)).bind
        (chunk0079AfterValue00 (fuel + 577) acc) :=
      congrArg (fun result => result.bind (chunk0079AfterValue00 (fuel + 577) acc))
        (value_fragment0273801 (fuel + 327) (chunk0079SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 577) (SourceJson.white tail) (chunk0079Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0079_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0072Chars00 ++ chunk0073Chars00 ++ chunk0074Chars00 ++ chunk0075Chars00 ++ chunk0076Chars00 ++ chunk0077Chars00 ++ chunk0078Chars00 ++ chunk0079Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0079Push00 (chunk0078Push00 (chunk0077Push00 (chunk0076Push00 (chunk0075Push00 (chunk0074Push00 (chunk0073Push00 (chunk0072Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 585) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 577) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0072Chars00 ++ (chunk0073Chars00 ++ (chunk0074Chars00 ++ (chunk0075Chars00 ++ (chunk0076Chars00 ++ (chunk0077Chars00 ++ (chunk0078Chars00 ++ (chunk0079Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 585) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 585) (SourceJson.white (chunk0072Chars00 ++ (chunk0073Chars00 ++ (chunk0074Chars00 ++ (chunk0075Chars00 ++ (chunk0076Chars00 ++ (chunk0077Chars00 ++ (chunk0078Chars00 ++ (chunk0079Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 585) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 584) (SourceJson.white (chunk0073Chars00 ++ (chunk0074Chars00 ++ (chunk0075Chars00 ++ (chunk0076Chars00 ++ (chunk0077Chars00 ++ (chunk0078Chars00 ++ (chunk0079Chars00 ++ (tail))))))))) (chunk0072Push00 (acc)) := array_chunk0072 fuel (chunk0073Chars00 ++ (chunk0074Chars00 ++ (chunk0075Chars00 ++ (chunk0076Chars00 ++ (chunk0077Chars00 ++ (chunk0078Chars00 ++ (chunk0079Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 583) (SourceJson.white (chunk0074Chars00 ++ (chunk0075Chars00 ++ (chunk0076Chars00 ++ (chunk0077Chars00 ++ (chunk0078Chars00 ++ (chunk0079Chars00 ++ (tail)))))))) (chunk0073Push00 (chunk0072Push00 (acc))) := array_chunk0073 fuel (chunk0074Chars00 ++ (chunk0075Chars00 ++ (chunk0076Chars00 ++ (chunk0077Chars00 ++ (chunk0078Chars00 ++ (chunk0079Chars00 ++ (tail))))))) (chunk0072Push00 (acc))
    _ = SourceJson.array (fuel + 582) (SourceJson.white (chunk0075Chars00 ++ (chunk0076Chars00 ++ (chunk0077Chars00 ++ (chunk0078Chars00 ++ (chunk0079Chars00 ++ (tail))))))) (chunk0074Push00 (chunk0073Push00 (chunk0072Push00 (acc)))) := array_chunk0074 fuel (chunk0075Chars00 ++ (chunk0076Chars00 ++ (chunk0077Chars00 ++ (chunk0078Chars00 ++ (chunk0079Chars00 ++ (tail)))))) (chunk0073Push00 (chunk0072Push00 (acc)))
    _ = SourceJson.array (fuel + 581) (SourceJson.white (chunk0076Chars00 ++ (chunk0077Chars00 ++ (chunk0078Chars00 ++ (chunk0079Chars00 ++ (tail)))))) (chunk0075Push00 (chunk0074Push00 (chunk0073Push00 (chunk0072Push00 (acc))))) := array_chunk0075 fuel (chunk0076Chars00 ++ (chunk0077Chars00 ++ (chunk0078Chars00 ++ (chunk0079Chars00 ++ (tail))))) (chunk0074Push00 (chunk0073Push00 (chunk0072Push00 (acc))))
    _ = SourceJson.array (fuel + 580) (SourceJson.white (chunk0077Chars00 ++ (chunk0078Chars00 ++ (chunk0079Chars00 ++ (tail))))) (chunk0076Push00 (chunk0075Push00 (chunk0074Push00 (chunk0073Push00 (chunk0072Push00 (acc)))))) := array_chunk0076 fuel (chunk0077Chars00 ++ (chunk0078Chars00 ++ (chunk0079Chars00 ++ (tail)))) (chunk0075Push00 (chunk0074Push00 (chunk0073Push00 (chunk0072Push00 (acc)))))
    _ = SourceJson.array (fuel + 579) (SourceJson.white (chunk0078Chars00 ++ (chunk0079Chars00 ++ (tail)))) (chunk0077Push00 (chunk0076Push00 (chunk0075Push00 (chunk0074Push00 (chunk0073Push00 (chunk0072Push00 (acc))))))) := array_chunk0077 fuel (chunk0078Chars00 ++ (chunk0079Chars00 ++ (tail))) (chunk0076Push00 (chunk0075Push00 (chunk0074Push00 (chunk0073Push00 (chunk0072Push00 (acc))))))
    _ = SourceJson.array (fuel + 578) (SourceJson.white (chunk0079Chars00 ++ (tail))) (chunk0078Push00 (chunk0077Push00 (chunk0076Push00 (chunk0075Push00 (chunk0074Push00 (chunk0073Push00 (chunk0072Push00 (acc)))))))) := array_chunk0078 fuel (chunk0079Chars00 ++ (tail)) (chunk0077Push00 (chunk0076Push00 (chunk0075Push00 (chunk0074Push00 (chunk0073Push00 (chunk0072Push00 (acc)))))))
    _ = SourceJson.array (fuel + 577) (SourceJson.white tail) (blockPush acc) := array_chunk0079 fuel (tail) (chunk0078Push00 (chunk0077Push00 (chunk0076Push00 (chunk0075Push00 (chunk0074Push00 (chunk0073Push00 (chunk0072Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 261421).take 14020 = blockChars := by rfl

theorem block_original_split : sourceRest 261421 = blockChars ++ sourceRest 275441 := by
  calc
    sourceRest 261421 = (sourceRest 261421).take 14020 ++ (sourceRest 261421).drop 14020 :=
      (List.take_append_drop 14020 (sourceRest 261421)).symm
    _ = blockChars ++ (sourceRest 261421).drop 14020 :=
      congrArg (fun part => part ++ (sourceRest 261421).drop 14020) block_original_prefix
    _ = blockChars ++ sourceRest 275441 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 261421 14020)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 585) (SourceJson.white (sourceRest 261421)) acc =
      SourceJson.array (fuel + 577) (SourceJson.white (sourceRest 275441)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 585) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 275441) acc)

#print axioms object_fragment0261427_field_000
#print axioms object_fragment0261427_field_001
#print axioms object_fragment0261427_field_002
#print axioms object_fragment0261427_field_003
#print axioms object_fragment0261427_field_004
#print axioms object_fragment0261427_field_005
#print axioms object_fragment0261427_field_006
#print axioms object_fragment0261427_field_007
#print axioms object_fragment0261427_field_008
#print axioms object_fragment0261427_field_009
#print axioms value_fragment0261427
#print axioms object_fragment0263305_field_000
#print axioms object_fragment0263305_field_001
#print axioms object_fragment0263305_field_002
#print axioms object_fragment0263305_field_003
#print axioms object_fragment0263305_field_004
#print axioms object_fragment0263305_field_005
#print axioms object_fragment0263305_field_006
#print axioms object_fragment0263305_field_007
#print axioms object_fragment0263305_field_008
#print axioms object_fragment0263305_field_009
#print axioms value_fragment0263305
#print axioms object_fragment0264837_field_000
#print axioms object_fragment0264837_field_001
#print axioms object_fragment0264837_field_002
#print axioms object_fragment0264837_field_003
#print axioms object_fragment0264837_field_004
#print axioms object_fragment0264837_field_005
#print axioms object_fragment0264837_field_006
#print axioms object_fragment0264837_field_007
#print axioms object_fragment0264837_field_008
#print axioms object_fragment0264837_field_009
#print axioms value_fragment0264837
#print axioms object_fragment0266682_field_000
#print axioms object_fragment0266682_field_001
#print axioms object_fragment0266682_field_002
#print axioms object_fragment0266682_field_003
#print axioms object_fragment0266682_field_004
#print axioms object_fragment0266682_field_005
#print axioms object_fragment0266682_field_006
#print axioms object_fragment0266682_field_007
#print axioms object_fragment0266682_field_008
#print axioms object_fragment0266682_field_009
#print axioms value_fragment0266682
#print axioms object_fragment0268202_field_000
#print axioms object_fragment0268202_field_001
#print axioms object_fragment0268202_field_002
#print axioms object_fragment0268202_field_003
#print axioms object_fragment0268202_field_004
#print axioms object_fragment0268202_field_005
#print axioms object_fragment0268202_field_006
#print axioms object_fragment0268202_field_007
#print axioms object_fragment0268202_field_008
#print axioms object_fragment0268202_field_009
#print axioms value_fragment0268202
#print axioms object_fragment0269747_field_000
#print axioms object_fragment0269747_field_001
#print axioms object_fragment0269747_field_002
#print axioms object_fragment0269747_field_003
#print axioms object_fragment0269747_field_004
#print axioms object_fragment0269747_field_005
#print axioms object_fragment0269747_field_006
#print axioms object_fragment0269747_field_007
#print axioms object_fragment0269747_field_008
#print axioms object_fragment0269747_field_009
#print axioms value_fragment0269747
#print axioms object_fragment0271793_field_000
#print axioms object_fragment0271793_field_001
#print axioms object_fragment0271793_field_002
#print axioms object_fragment0271793_field_003
#print axioms object_fragment0271793_field_004
#print axioms object_fragment0271793_field_005
#print axioms object_fragment0271793_field_006
#print axioms object_fragment0271793_field_007
#print axioms object_fragment0271793_field_008
#print axioms object_fragment0271793_field_009
#print axioms value_fragment0271793
#print axioms object_fragment0273801_field_000
#print axioms object_fragment0273801_field_001
#print axioms object_fragment0273801_field_002
#print axioms object_fragment0273801_field_003
#print axioms object_fragment0273801_field_004
#print axioms object_fragment0273801_field_005
#print axioms object_fragment0273801_field_006
#print axioms object_fragment0273801_field_007
#print axioms object_fragment0273801_field_008
#print axioms object_fragment0273801_field_009
#print axioms value_fragment0273801
#print axioms array_chunk0072_head
#print axioms array_chunk0072
#print axioms array_chunk0073_head
#print axioms array_chunk0073
#print axioms array_chunk0074_head
#print axioms array_chunk0074
#print axioms array_chunk0075_head
#print axioms array_chunk0075
#print axioms array_chunk0076_head
#print axioms array_chunk0076
#print axioms array_chunk0077_head
#print axioms array_chunk0077
#print axioms array_chunk0078_head
#print axioms array_chunk0078
#print axioms array_chunk0079_head
#print axioms array_chunk0079
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock009

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
