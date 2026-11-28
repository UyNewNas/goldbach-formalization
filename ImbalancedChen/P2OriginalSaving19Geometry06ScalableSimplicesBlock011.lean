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

namespace SimplicesBlock011

noncomputable def fragment0289765Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0289765Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0289765Field000Value00 : SourceJson := .number (String.ofList ['8', '8'])
noncomputable def fragment0289765Acc00100 : List (String × SourceJson) := (fragment0289765Field000Key00, fragment0289765Field000Value00) :: fragment0289765Acc00000
noncomputable def fragment0289765Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '8', ',']

theorem object_fragment0289765_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0289765Field000Chars00 ++ tail)) fragment0289765Acc00000 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0289765Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289765_object_field_000"
  err.flush

noncomputable def fragment0289765Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0289765Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['4'])]
noncomputable def fragment0289765Acc00200 : List (String × SourceJson) := (fragment0289765Field001Key00, fragment0289765Field001Value00) :: fragment0289765Acc00100
noncomputable def fragment0289765Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0289765_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0289765Field001Chars00 ++ tail)) fragment0289765Acc00100 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0289765Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289765_object_field_001"
  err.flush

noncomputable def fragment0289765Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0289765Field002Value00 : SourceJson := .str (String.ofList ['6', '2', '2', '7', '6', '4', '3', '9', '4', '0', '7', '4', '3', '2', '1', '7', '3', '8', '8', '6', '5', '2', '6', '5', '6', '6', '5', '4', '2', '8', '5', '6', '9', '8', '8', '2', '0', '8', '7', '9', '/', '3', '1', '2', '6', '6', '6', '0', '3', '0', '1', '6', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0289765Acc00300 : List (String × SourceJson) := (fragment0289765Field002Key00, fragment0289765Field002Value00) :: fragment0289765Acc00200
noncomputable def fragment0289765Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '2', '2', '7', '6', '4', '3', '9', '4', '0', '7', '4', '3', '2', '1', '7', '3', '8', '8', '6', '5', '2', '6', '5', '6', '6', '5', '4', '2', '8', '5', '6', '9', '8', '8', '2', '0', '8', '7', '9', '/', '3', '1', '2', '6', '6', '6', '0', '3', '0', '1', '6', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0289765_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0289765Field002Chars00 ++ tail)) fragment0289765Acc00200 =
      SourceJson.object (fuel + 240) (SourceJson.white tail) fragment0289765Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289765_object_field_002"
  err.flush

noncomputable def fragment0289765Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0289765Field003Value00 : SourceJson := .str (String.ofList ['9', '8', '4', '2', '0', '3', '/', '1', '3', '5', '4', '5', '0', '0', '0', '0', '0'])
noncomputable def fragment0289765Acc00400 : List (String × SourceJson) := (fragment0289765Field003Key00, fragment0289765Field003Value00) :: fragment0289765Acc00300
noncomputable def fragment0289765Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '8', '4', '2', '0', '3', '/', '1', '3', '5', '4', '5', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0289765_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 240) (SourceJson.white (fragment0289765Field003Chars00 ++ tail)) fragment0289765Acc00300 =
      SourceJson.object (fuel + 239) (SourceJson.white tail) fragment0289765Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289765_object_field_003"
  err.flush

noncomputable def fragment0289765Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0289765Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0289765Acc00500 : List (String × SourceJson) := (fragment0289765Field004Key00, fragment0289765Field004Value00) :: fragment0289765Acc00400
noncomputable def fragment0289765Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0289765_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0289765Field004Chars00 ++ tail)) fragment0289765Acc00400 =
      SourceJson.object (fuel + 238) (SourceJson.white tail) fragment0289765Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289765_object_field_004"
  err.flush

noncomputable def fragment0289765Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0289765Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '8', '9', '6', '5', '6', '6', '1', '8', '8', '6', '1', '4', '3', '/', '3', '3', '3', '9', '6', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '3', '7', '7', '8', '1', '1', '7', '4', '6', '9', '/', '7', '7', '6', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '8', '4', '0', '6', '5', '7', '5', '3', '6', '1', '/', '3', '6', '3', '0', '0', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '6', '3', '8', '8', '2', '9', '7', '7', '9', '0', '3', '/', '3', '7', '1', '0', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '3', '1', '1', '5', '5', '0', '3', '2', '4', '9', '3', '/', '1', '1', '1', '3', '2', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '8', '2', '6', '6', '0', '4', '3', '0', '7', '2', '9', '/', '1', '6', '6', '9', '8', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '9', '8', '4', '1', '8', '8', '9', '2', '3', '3', '/', '9', '5', '4', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '2', '4', '6', '7', '2', '3', '1', '7', '8', '8', '1', '/', '4', '7', '7', '0', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '9', '9', '4', '3', '0', '5', '7', '6', '4', '2', '1', '/', '3', '3', '3', '9', '6', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '3', '3', '1', '9', '0', '7', '8', '9', '1', '1', '/', '7', '7', '6', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0289765Acc00600 : List (String × SourceJson) := (fragment0289765Field005Key00, fragment0289765Field005Value00) :: fragment0289765Acc00500
noncomputable def fragment0289765Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '9', '6', '5', '6', '6', '1', '8', '8', '6', '1', '4', '3', '/', '3', '3', '3', '9', '6', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '3', '7', '7', '8', '1', '1', '7', '4', '6', '9', '/', '7', '7', '6', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '8', '4', '0', '6', '5', '7', '5', '3', '6', '1', '/', '3', '6', '3', '0', '0', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '6', '3', '8', '8', '2', '9', '7', '7', '9', '0', '3', '/', '3', '7', '1', '0', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '3', '1', '1', '5', '5', '0', '3', '2', '4', '9', '3', '/', '1', '1', '1', '3', '2', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '8', '2', '6', '6', '0', '4', '3', '0', '7', '2', '9', '/', '1', '6', '6', '9', '8', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '9', '8', '4', '1', '8', '8', '9', '2', '3', '3', '/', '9', '5', '4', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '2', '4', '6', '7', '2', '3', '1', '7', '8', '8', '1', '/', '4', '7', '7', '0', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '9', '9', '4', '3', '0', '5', '7', '6', '4', '2', '1', '/', '3', '3', '3', '9', '6', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '3', '3', '1', '9', '0', '7', '8', '9', '1', '1', '/', '7', '7', '6', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0289765_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0289765Field005Chars00 ++ tail)) fragment0289765Acc00500 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment0289765Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289765_object_field_005"
  err.flush

noncomputable def fragment0289765Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0289765Field006Value00 : SourceJson := .str (String.ofList ['7', '0', '1', '7', '7', '0', '3', '2', '8', '2', '5', '3', '7', '2', '0', '5', '6', '9', '6', '1', '6', '5', '4', '0', '9', '3', '5', '8', '2', '9', '2', '6', '6', '2', '1', '6', '4', '5', '9', '6', '7', '5', '9', '0', '7', '6', '9', '5', '9', '8', '7', '9', '3', '7', '5', '/', '2', '3', '5', '0', '6', '5', '3', '9', '2', '5', '8', '2', '6', '6', '3', '1', '6', '1', '1', '3', '1', '8', '1', '9', '9', '2', '7', '6', '7', '6', '0', '4', '1', '4', '5', '4', '5', '2', '7', '5', '0', '7', '6', '7', '3', '2', '5', '9', '6', '0', '1', '3', '1', '3', '0', '6', '4', '7', '7', '9', '8', '4', '8', '7', '6', '2', '2', '4'])
noncomputable def fragment0289765Acc00700 : List (String × SourceJson) := (fragment0289765Field006Key00, fragment0289765Field006Value00) :: fragment0289765Acc00600
noncomputable def fragment0289765Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '0', '1', '7', '7', '0', '3', '2', '8', '2', '5', '3', '7', '2', '0', '5', '6', '9', '6', '1', '6', '5', '4', '0', '9', '3', '5', '8', '2', '9', '2', '6', '6', '2', '1', '6', '4', '5', '9', '6', '7', '5', '9', '0', '7', '6', '9', '5', '9', '8', '7', '9', '3', '7', '5', '/', '2', '3', '5', '0', '6', '5', '3', '9', '2', '5', '8', '2', '6', '6', '3', '1', '6', '1', '1', '3', '1', '8', '1', '9', '9', '2', '7', '6', '7', '6', '0', '4', '1', '4', '5', '4', '5', '2', '7', '5', '0', '7', '6', '7', '3', '2', '5', '9', '6', '0', '1', '3', '1', '3', '0', '6', '4', '7', '7', '9', '8', '4', '8', '7', '6', '2', '2', '4', '"', ',']

theorem object_fragment0289765_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0289765Field006Chars00 ++ tail)) fragment0289765Acc00600 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0289765Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289765_object_field_006"
  err.flush

noncomputable def fragment0289765Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0289765Field007Value00 : SourceJson := .str (String.ofList ['1', '9', '2', '1', '8', '8', '9', '8', '1', '8', '3', '3', '2', '6', '4', '3', '4', '1', '0', '2', '6', '8', '5', '9', '1', '2', '0', '0', '6', '0', '9', '8', '4', '6', '1', '8', '6', '4', '7', '2', '9', '5', '5', '9', '5', '2', '9', '9', '3', '3', '4', '5', '1', '4', '1', '5', '9', '0', '2', '8', '0', '2', '0', '8', '1', '8', '6', '2', '7', '7', '6', '2', '6', '6', '8', '8', '9', '4', '7', '3', '8', '8', '6', '3', '3', '6', '9', '7', '7', '9', '9', '3', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '1', '6', '4', '1', '8', '6', '4', '0', '5', '4', '2', '9', '2', '0', '0', '4', '0', '3', '9', '4', '9', '9', '6', '3', '2', '4', '6', '3', '3', '4', '3', '4', '0', '1', '5', '1', '8', '2', '4', '1', '9', '4', '6', '8', '1', '1', '1', '8', '7', '5', '8', '5', '8', '2', '8', '8', '8', '2', '3', '0', '8', '9', '4', '4', '9', '1', '5', '8', '2', '6', '3', '3', '4', '5', '1', '2', '5', '4', '5', '0', '5', '7', '2', '0', '8', '0', '7', '3', '5', '7', '7', '1', '0', '3', '1', '8', '1', '3', '0', '4', '3', '9', '9', '1', '3', '2', '1', '2', '3', '8', '9', '0', '1', '3', '5', '8', '2', '2', '3', '4', '1'])
noncomputable def fragment0289765Acc00800 : List (String × SourceJson) := (fragment0289765Field007Key00, fragment0289765Field007Value00) :: fragment0289765Acc00700
noncomputable def fragment0289765Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '2', '1', '8', '8', '9', '8', '1', '8', '3', '3', '2', '6', '4', '3', '4', '1', '0', '2', '6', '8', '5', '9', '1', '2', '0', '0', '6', '0', '9', '8', '4', '6', '1', '8', '6', '4', '7', '2', '9', '5', '5', '9', '5', '2', '9', '9', '3', '3', '4', '5', '1', '4', '1', '5', '9', '0', '2', '8', '0', '2', '0', '8', '1', '8', '6', '2', '7', '7', '6', '2', '6', '6', '8', '8', '9', '4', '7', '3', '8', '8', '6', '3', '3', '6', '9', '7', '7', '9', '9', '3', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '1', '6', '4', '1', '8', '6', '4', '0', '5', '4', '2', '9', '2', '0', '0', '4', '0', '3', '9', '4', '9', '9', '6', '3', '2', '4', '6', '3', '3', '4', '3', '4', '0', '1', '5', '1', '8', '2', '4', '1', '9', '4', '6', '8', '1', '1', '1', '8', '7', '5', '8', '5', '8', '2', '8', '8', '8', '2', '3', '0', '8', '9', '4', '4', '9', '1', '5', '8', '2', '6', '3', '3', '4', '5', '1', '2', '5', '4', '5', '0', '5', '7', '2', '0', '8', '0', '7', '3', '5', '7', '7', '1', '0', '3', '1', '8', '1', '3', '0', '4', '3', '9', '9', '1', '3', '2', '1', '2', '3', '8', '9', '0', '1', '3', '5', '8', '2', '2', '3', '4', '1', '"', ',']

theorem object_fragment0289765_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0289765Field007Chars00 ++ tail)) fragment0289765Acc00700 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0289765Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289765_object_field_007"
  err.flush

noncomputable def fragment0289765Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0289765Field008Value00 : SourceJson := .str (String.ofList ['2', '3', '6', '5', '2', '9', '8', '1', '4', '1', '2', '4', '0', '5', '1', '0', '3'])
noncomputable def fragment0289765Acc00900 : List (String × SourceJson) := (fragment0289765Field008Key00, fragment0289765Field008Value00) :: fragment0289765Acc00800
noncomputable def fragment0289765Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '6', '5', '2', '9', '8', '1', '4', '1', '2', '4', '0', '5', '1', '0', '3', '"', ',']

theorem object_fragment0289765_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0289765Field008Chars00 ++ tail)) fragment0289765Acc00800 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0289765Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289765_object_field_008"
  err.flush

noncomputable def fragment0289765Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0289765Field009Value00 : SourceJson := .str (String.ofList ['7', '0', '3', '5', '7', '9', '8', '6', '9', '4', '5', '7', '5', '5', '2', '3', '8'])
noncomputable def fragment0289765Acc01000 : List (String × SourceJson) := (fragment0289765Field009Key00, fragment0289765Field009Value00) :: fragment0289765Acc00900
noncomputable def fragment0289765Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '0', '3', '5', '7', '9', '8', '6', '9', '4', '5', '7', '5', '5', '2', '3', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0289765_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0289765Field009Chars00 ++ tail)) fragment0289765Acc00900 =
      .ok (.obj (fragment0289765Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289765_object_field_009"
  err.flush

noncomputable def fragment0289765Chars : List Char := '{' :: (fragment0289765Field000Chars00 ++ fragment0289765Field001Chars00 ++ fragment0289765Field002Chars00 ++ fragment0289765Field003Chars00 ++ fragment0289765Field004Chars00 ++ fragment0289765Field005Chars00 ++ fragment0289765Field006Chars00 ++ fragment0289765Field007Chars00 ++ fragment0289765Field008Chars00 ++ fragment0289765Field009Chars00)
noncomputable def fragment0289765Value : SourceJson := .obj (fragment0289765Acc01000.reverse)

theorem value_fragment0289765 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 244) (fragment0289765Chars ++ tail) =
      .ok (fragment0289765Value, tail) := by
  have hinput : fragment0289765Chars ++ tail = '{' :: (fragment0289765Field000Chars00 ++ (fragment0289765Field001Chars00 ++ (fragment0289765Field002Chars00 ++ (fragment0289765Field003Chars00 ++ (fragment0289765Field004Chars00 ++ (fragment0289765Field005Chars00 ++ (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0289765Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 244) (fragment0289765Chars ++ tail) =
        SourceJson.value (fuel + 244) ('{' :: (fragment0289765Field000Chars00 ++ (fragment0289765Field001Chars00 ++ (fragment0289765Field002Chars00 ++ (fragment0289765Field003Chars00 ++ (fragment0289765Field004Chars00 ++ (fragment0289765Field005Chars00 ++ (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 244)) hinput
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0289765Field000Chars00 ++ (fragment0289765Field001Chars00 ++ (fragment0289765Field002Chars00 ++ (fragment0289765Field003Chars00 ++ (fragment0289765Field004Chars00 ++ (fragment0289765Field005Chars00 ++ (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail)))))))))))) fragment0289765Acc00000 := by rfl
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0289765Field001Chars00 ++ (fragment0289765Field002Chars00 ++ (fragment0289765Field003Chars00 ++ (fragment0289765Field004Chars00 ++ (fragment0289765Field005Chars00 ++ (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail))))))))))) fragment0289765Acc00100 := object_fragment0289765_field_000 fuel (fragment0289765Field001Chars00 ++ (fragment0289765Field002Chars00 ++ (fragment0289765Field003Chars00 ++ (fragment0289765Field004Chars00 ++ (fragment0289765Field005Chars00 ++ (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0289765Field002Chars00 ++ (fragment0289765Field003Chars00 ++ (fragment0289765Field004Chars00 ++ (fragment0289765Field005Chars00 ++ (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail)))))))))) fragment0289765Acc00200 := object_fragment0289765_field_001 fuel (fragment0289765Field002Chars00 ++ (fragment0289765Field003Chars00 ++ (fragment0289765Field004Chars00 ++ (fragment0289765Field005Chars00 ++ (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 240) (SourceJson.white (fragment0289765Field003Chars00 ++ (fragment0289765Field004Chars00 ++ (fragment0289765Field005Chars00 ++ (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail))))))))) fragment0289765Acc00300 := object_fragment0289765_field_002 fuel (fragment0289765Field003Chars00 ++ (fragment0289765Field004Chars00 ++ (fragment0289765Field005Chars00 ++ (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0289765Field004Chars00 ++ (fragment0289765Field005Chars00 ++ (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail)))))))) fragment0289765Acc00400 := object_fragment0289765_field_003 fuel (fragment0289765Field004Chars00 ++ (fragment0289765Field005Chars00 ++ (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0289765Field005Chars00 ++ (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail))))))) fragment0289765Acc00500 := object_fragment0289765_field_004 fuel (fragment0289765Field005Chars00 ++ (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail)))))) fragment0289765Acc00600 := object_fragment0289765_field_005 fuel (fragment0289765Field006Chars00 ++ (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail))))) fragment0289765Acc00700 := object_fragment0289765_field_006 fuel (fragment0289765Field007Chars00 ++ (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail)))) fragment0289765Acc00800 := object_fragment0289765_field_007 fuel (fragment0289765Field008Chars00 ++ (fragment0289765Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0289765Field009Chars00 ++ (tail))) fragment0289765Acc00900 := object_fragment0289765_field_008 fuel (fragment0289765Field009Chars00 ++ (tail))
    _ = .ok (fragment0289765Value, tail) := object_fragment0289765_field_009 fuel (tail)

noncomputable def fragment0291390Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0291390Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0291390Field000Value00 : SourceJson := .number (String.ofList ['8', '9'])
noncomputable def fragment0291390Acc00100 : List (String × SourceJson) := (fragment0291390Field000Key00, fragment0291390Field000Value00) :: fragment0291390Acc00000
noncomputable def fragment0291390Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '9', ',']

theorem object_fragment0291390_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 446) (SourceJson.white (fragment0291390Field000Chars00 ++ tail)) fragment0291390Acc00000 =
      SourceJson.object (fuel + 445) (SourceJson.white tail) fragment0291390Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291390_object_field_000"
  err.flush

noncomputable def fragment0291390Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0291390Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['3'])]
noncomputable def fragment0291390Acc00200 : List (String × SourceJson) := (fragment0291390Field001Key00, fragment0291390Field001Value00) :: fragment0291390Acc00100
noncomputable def fragment0291390Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0291390_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 445) (SourceJson.white (fragment0291390Field001Chars00 ++ tail)) fragment0291390Acc00100 =
      SourceJson.object (fuel + 444) (SourceJson.white tail) fragment0291390Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291390_object_field_001"
  err.flush

noncomputable def fragment0291390Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0291390Field002Value00 : SourceJson := .str (String.ofList ['6', '3', '2', '7', '3', '1', '4', '1', '2', '6', '1', '9', '9', '8', '2', '1', '2', '7', '1', '0', '4', '5', '9', '7', '5', '0', '3', '7', '1', '9', '0', '0', '2', '0', '0', '4', '1', '7', '5', '1', '/', '7', '0', '6', '5', '1', '6', '1', '6', '0', '0', '7', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0291390Acc00300 : List (String × SourceJson) := (fragment0291390Field002Key00, fragment0291390Field002Value00) :: fragment0291390Acc00200
noncomputable def fragment0291390Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '3', '2', '7', '3', '1', '4', '1', '2', '6', '1', '9', '9', '8', '2', '1', '2', '7', '1', '0', '4', '5', '9', '7', '5', '0', '3', '7', '1', '9', '0', '0', '2', '0', '0', '4', '1', '7', '5', '1', '/', '7', '0', '6', '5', '1', '6', '1', '6', '0', '0', '7', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0291390_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 444) (SourceJson.white (fragment0291390Field002Chars00 ++ tail)) fragment0291390Acc00200 =
      SourceJson.object (fuel + 443) (SourceJson.white tail) fragment0291390Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291390_object_field_002"
  err.flush

noncomputable def fragment0291390Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0291390Field003Value00 : SourceJson := .str (String.ofList ['2', '2', '3', '7', '4', '1', '1', '9', '2', '9', '/', '1', '0', '5', '5', '7', '3', '6', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0291390Acc00400 : List (String × SourceJson) := (fragment0291390Field003Key00, fragment0291390Field003Value00) :: fragment0291390Acc00300
noncomputable def fragment0291390Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '2', '3', '7', '4', '1', '1', '9', '2', '9', '/', '1', '0', '5', '5', '7', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0291390_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 443) (SourceJson.white (fragment0291390Field003Chars00 ++ tail)) fragment0291390Acc00300 =
      SourceJson.object (fuel + 442) (SourceJson.white tail) fragment0291390Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291390_object_field_003"
  err.flush

noncomputable def fragment0291390Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0291390Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '0', '1', '5', '6', '2', '9', '/', '8', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '4', '0', '6', '0', '9', '/', '2', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '9', '3', '7', '1', '/', '2', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '9', '3', '7', '1', '/', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '2', '1', '7', '0', '3', '/', '1', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0291390Acc00500 : List (String × SourceJson) := (fragment0291390Field004Key00, fragment0291390Field004Value00) :: fragment0291390Acc00400
noncomputable def fragment0291390Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '1', '5', '6', '2', '9', '/', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '4', '0', '6', '0', '9', '/', '2', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '9', '3', '7', '1', '/', '2', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '9', '3', '7', '1', '/', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '2', '1', '7', '0', '3', '/', '1', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0291390_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 442) (SourceJson.white (fragment0291390Field004Chars00 ++ tail)) fragment0291390Acc00400 =
      SourceJson.object (fuel + 441) (SourceJson.white tail) fragment0291390Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291390_object_field_004"
  err.flush

noncomputable def fragment0291390Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0291390Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '4', '7', '3', '1', '0', '8', '0', '3', '7', '8', '5', '4', '4', '5', '3', '7', '8', '5', '9', '/', '8', '6', '9', '2', '5', '8', '8', '0', '5', '8', '6', '1', '1', '0', '5', '7', '9', '2', '0', '0', '0']), .str (String.ofList ['4', '8', '0', '8', '9', '5', '0', '5', '8', '6', '2', '8', '3', '9', '3', '4', '1', '3', '7', '9', '0', '2', '9', '/', '5', '4', '3', '2', '8', '6', '7', '5', '3', '6', '6', '3', '1', '9', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '1', '8', '0', '7', '7', '0', '2', '5', '1', '5', '7', '4', '2', '3', '1', '2', '7', '0', '4', '7', '3', '/', '9', '5', '0', '7', '5', '1', '8', '1', '8', '9', '1', '0', '5', '8', '4', '4', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '1', '3', '7', '4', '6', '8', '5', '4', '0', '4', '0', '9', '4', '4', '1', '6', '5', '3', '9', '1', '1', '/', '4', '2', '2', '5', '5', '6', '3', '6', '3', '9', '6', '0', '2', '5', '9', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '9', '7', '2', '3', '5', '3', '5', '8', '6', '4', '6', '8', '4', '4', '8', '5', '1', '4', '1', '8', '6', '1', '/', '1', '2', '6', '7', '6', '6', '9', '0', '9', '1', '8', '8', '0', '7', '7', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '5', '4', '1', '4', '8', '6', '3', '8', '1', '0', '5', '1', '8', '9', '7', '9', '7', '6', '7', '3', '3', '/', '3', '8', '0', '3', '0', '0', '7', '2', '7', '5', '6', '4', '2', '3', '3', '7', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '3', '9', '8', '0', '6', '1', '0', '8', '3', '0', '3', '0', '0', '3', '3', '6', '6', '9', '3', '6', '0', '7', '/', '3', '8', '0', '3', '0', '0', '7', '2', '7', '5', '6', '4', '2', '3', '3', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '0', '3', '9', '1', '0', '9', '1', '8', '0', '1', '0', '9', '7', '1', '8', '2', '4', '7', '2', '1', '1', '/', '3', '8', '0', '3', '0', '0', '7', '2', '7', '5', '6', '4', '2', '3', '3', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '2', '0', '2', '5', '8', '4', '3', '8', '9', '6', '6', '5', '9', '4', '8', '9', '3', '6', '6', '1', '/', '1', '0', '8', '6', '5', '7', '3', '5', '0', '7', '3', '2', '6', '3', '8', '2', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '7', '0', '8', '5', '5', '6', '0', '6', '6', '4', '1', '8', '6', '8', '4', '4', '6', '4', '7', '/', '5', '4', '3', '2', '8', '6', '7', '5', '3', '6', '6', '3', '1', '9', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0291390Acc00600 : List (String × SourceJson) := (fragment0291390Field005Key00, fragment0291390Field005Value00) :: fragment0291390Acc00500
noncomputable def fragment0291390Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '7', '3', '1', '0', '8', '0', '3', '7', '8', '5', '4', '4', '5', '3', '7', '8', '5', '9', '/', '8', '6', '9', '2', '5', '8', '8', '0', '5', '8', '6', '1', '1', '0', '5', '7', '9', '2', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '0', '8', '9', '5', '0', '5', '8', '6', '2', '8', '3', '9', '3', '4', '1', '3', '7', '9', '0', '2', '9', '/', '5', '4', '3', '2', '8', '6', '7', '5', '3', '6', '6', '3', '1', '9', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '1', '8', '0', '7', '7', '0', '2', '5', '1', '5', '7', '4', '2', '3', '1', '2', '7', '0', '4', '7', '3', '/', '9', '5', '0', '7', '5', '1', '8', '1', '8', '9', '1', '0', '5', '8', '4', '4', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '1', '3', '7', '4', '6', '8', '5', '4', '0', '4', '0', '9', '4', '4', '1', '6', '5', '3', '9', '1', '1', '/', '4', '2', '2', '5', '5', '6', '3', '6', '3', '9', '6', '0', '2', '5', '9', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '7', '2', '3', '5', '3', '5', '8', '6', '4', '6', '8', '4', '4', '8', '5', '1', '4', '1', '8', '6', '1', '/', '1', '2', '6', '7', '6', '6', '9', '0', '9', '1', '8', '8', '0', '7', '7', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '5', '4', '1', '4', '8', '6', '3', '8', '1', '0', '5', '1', '8', '9', '7', '9', '7', '6', '7', '3', '3', '/', '3', '8', '0', '3', '0', '0', '7', '2', '7', '5', '6', '4', '2', '3', '3', '7', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '9', '8', '0', '6', '1', '0', '8', '3', '0', '3', '0', '0', '3', '3', '6', '6', '9', '3', '6', '0', '7', '/', '3', '8', '0', '3', '0', '0', '7', '2', '7', '5', '6', '4', '2', '3', '3', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '0', '3', '9', '1', '0', '9', '1', '8', '0', '1', '0', '9', '7', '1', '8', '2', '4', '7', '2', '1', '1', '/', '3', '8', '0', '3', '0', '0', '7', '2', '7', '5', '6', '4', '2', '3', '3', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '0', '2', '5', '8', '4', '3', '8', '9', '6', '6', '5', '9', '4', '8', '9', '3', '6', '6', '1', '/', '1', '0', '8', '6', '5', '7', '3', '5', '0', '7', '3', '2', '6', '3', '8', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '7', '0', '8', '5', '5', '6', '0', '6', '6', '4', '1', '8', '6', '8', '4', '4', '6', '4', '7', '/', '5', '4', '3', '2', '8', '6', '7', '5', '3', '6', '6', '3', '1', '9', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0291390_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 441) (SourceJson.white (fragment0291390Field005Chars00 ++ tail)) fragment0291390Acc00500 =
      SourceJson.object (fuel + 440) (SourceJson.white tail) fragment0291390Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291390_object_field_005"
  err.flush

noncomputable def fragment0291390Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0291390Field006Value00 : SourceJson := .str (String.ofList ['1', '0', '9', '6', '3', '0', '3', '2', '1', '9', '6', '1', '1', '6', '8', '1', '7', '1', '3', '5', '9', '3', '7', '6', '0', '6', '5', '8', '9', '0', '1', '1', '6', '1', '9', '2', '4', '6', '2', '1', '2', '4', '4', '5', '5', '6', '2', '6', '8', '2', '6', '1', '7', '6', '0', '0', '0', '0', '0', '/', '2', '1', '0', '4', '5', '9', '6', '3', '1', '8', '1', '6', '9', '1', '9', '9', '8', '3', '7', '5', '2', '3', '0', '8', '8', '3', '2', '7', '7', '4', '4', '4', '8', '6', '4', '0', '7', '8', '9', '7', '8', '3', '2', '3', '9', '6', '8', '3', '9', '4', '3', '2', '8', '1', '6', '9', '0', '6', '0', '1', '1', '8', '3', '8', '2', '2', '1', '9', '6', '1', '9', '3'])
noncomputable def fragment0291390Acc00700 : List (String × SourceJson) := (fragment0291390Field006Key00, fragment0291390Field006Value00) :: fragment0291390Acc00600
noncomputable def fragment0291390Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '9', '6', '3', '0', '3', '2', '1', '9', '6', '1', '1', '6', '8', '1', '7', '1', '3', '5', '9', '3', '7', '6', '0', '6', '5', '8', '9', '0', '1', '1', '6', '1', '9', '2', '4', '6', '2', '1', '2', '4', '4', '5', '5', '6', '2', '6', '8', '2', '6', '1', '7', '6', '0', '0', '0', '0', '0', '/', '2', '1', '0', '4', '5', '9', '6', '3', '1', '8', '1', '6', '9', '1', '9', '9', '8', '3', '7', '5', '2', '3', '0', '8', '8', '3', '2', '7', '7', '4', '4', '4', '8', '6', '4', '0', '7', '8', '9', '7', '8', '3', '2', '3', '9', '6', '8', '3', '9', '4', '3', '2', '8', '1', '6', '9', '0', '6', '0', '1', '1', '8', '3', '8', '2', '2', '1', '9', '6', '1', '9', '3', '"', ',']

theorem object_fragment0291390_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 440) (SourceJson.white (fragment0291390Field006Chars00 ++ tail)) fragment0291390Acc00600 =
      SourceJson.object (fuel + 439) (SourceJson.white tail) fragment0291390Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291390_object_field_006"
  err.flush

noncomputable def fragment0291390Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0291390Field007Value00 : SourceJson := .str (String.ofList ['5', '9', '2', '8', '6', '1', '8', '8', '5', '9', '4', '2', '3', '3', '8', '1', '7', '3', '9', '8', '4', '0', '1', '2', '3', '5', '8', '4', '0', '8', '9', '6', '7', '7', '9', '6', '7', '6', '4', '2', '3', '6', '3', '7', '8', '6', '0', '5', '9', '7', '3', '1', '8', '1', '4', '3', '2', '3', '5', '3', '5', '0', '3', '6', '8', '7', '7', '5', '8', '5', '8', '2', '5', '3', '3', '8', '3', '6', '8', '1', '6', '1', '1', '2', '7', '1', '6', '0', '1', '4', '7', '9', '0', '1', '0', '1', '8', '1', '5', '7', '9', '8', '5', '4', '8', '3', '3', '5', '9', '7', '9', '6', '3', '0', '1', '1', '3', '2', '1', '4', '6', '8', '4', '3', '1', '8', '9', '9', '9', '2', '8', '3', '5', '6', '2', '0', '4', '4', '9', '6', '5', '2', '5', '2', '2', '6', '8', '7', '6', '6', '4', '3', '9', '9', '1', '6', '7', '4', '1', '6', '0', '3', '0', '3', '3', '8', '9', '4', '0', '2', '4', '7', '3', '7', '7', '3', '0', '9', '4', '5', '2', '9', '7', '6', '4', '0', '3', '3', '6', '9', '3', '4', '2', '5', '0', '0', '0', '7', '7', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '8', '9', '0', '8', '8', '2', '4', '7', '0', '4', '2', '7', '0', '5', '1', '6', '0', '6', '3', '9', '4', '7', '5', '2', '6', '4', '9', '1', '4', '5', '3', '1', '7', '3', '2', '1', '2', '1', '5', '6', '8', '5', '5', '5', '0', '3', '8', '5', '5', '3', '1', '0', '0', '6', '2', '9', '6', '9', '3', '6', '3', '0', '3', '0', '4', '8', '8', '8', '9', '6', '9', '6', '6', '6', '8', '7', '8', '0', '1', '7', '1', '4', '4', '5', '7', '4', '1', '0', '4', '6', '6', '8', '5', '2', '8', '1', '8', '5', '2', '8', '8', '3', '5', '2', '3', '4', '3', '2', '0', '7', '2', '2', '9', '1', '5', '2', '6', '3', '8', '1', '0', '3', '1', '1', '0', '9', '2', '3', '0', '6', '4', '1', '3', '8', '3', '5', '0', '9', '0', '3', '2', '3', '9', '8', '5', '9', '9', '8', '6', '5', '7', '6', '0', '9', '8', '8', '1', '0', '9', '9', '4', '5', '4', '1', '6', '2', '8', '4', '0', '3', '0', '0', '0', '8', '3', '8', '5', '6', '6', '8', '1', '2', '1', '7', '0', '8', '5', '3', '0', '6', '3', '2', '3', '8', '5', '1', '3', '5', '9', '1', '1', '2', '0', '5', '8', '4', '5', '5', '9', '7', '3', '8', '1', '9', '9', '8', '1', '5', '2', '8', '9', '1', '1'])
noncomputable def fragment0291390Acc00800 : List (String × SourceJson) := (fragment0291390Field007Key00, fragment0291390Field007Value00) :: fragment0291390Acc00700
noncomputable def fragment0291390Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '9', '2', '8', '6', '1', '8', '8', '5', '9', '4', '2', '3', '3', '8', '1', '7', '3', '9', '8', '4', '0', '1', '2', '3', '5', '8', '4', '0', '8', '9', '6', '7', '7', '9', '6', '7', '6', '4', '2', '3', '6', '3', '7', '8', '6', '0', '5', '9', '7', '3', '1', '8', '1', '4', '3', '2', '3', '5', '3', '5', '0', '3', '6', '8', '7', '7', '5', '8', '5', '8', '2', '5', '3', '3', '8', '3', '6', '8', '1', '6', '1', '1', '2', '7', '1', '6', '0', '1', '4', '7', '9', '0', '1', '0', '1', '8', '1', '5', '7', '9', '8', '5', '4', '8', '3', '3', '5', '9', '7', '9', '6', '3', '0', '1', '1', '3', '2', '1', '4', '6', '8', '4', '3', '1', '8', '9', '9', '9', '2', '8', '3', '5', '6', '2', '0', '4', '4', '9', '6', '5', '2', '5', '2', '2', '6', '8', '7', '6', '6', '4', '3', '9', '9', '1', '6', '7', '4', '1', '6', '0', '3', '0', '3', '3', '8', '9', '4', '0', '2', '4', '7', '3', '7', '7', '3', '0', '9', '4', '5', '2', '9', '7', '6', '4', '0', '3', '3', '6', '9', '3', '4', '2', '5', '0', '0', '0', '7', '7', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '8', '9', '0', '8', '8', '2', '4', '7', '0', '4', '2', '7', '0', '5', '1', '6', '0', '6', '3', '9', '4', '7', '5', '2', '6', '4', '9', '1', '4', '5', '3', '1', '7', '3', '2', '1', '2', '1', '5', '6', '8', '5', '5', '5', '0', '3', '8', '5', '5', '3', '1', '0', '0', '6', '2', '9', '6', '9', '3', '6', '3', '0', '3', '0', '4', '8', '8', '8', '9', '6', '9', '6', '6', '6', '8', '7', '8', '0', '1', '7', '1', '4', '4', '5', '7', '4', '1', '0', '4', '6', '6', '8', '5', '2', '8', '1', '8', '5', '2', '8', '8', '3', '5', '2', '3', '4', '3', '2', '0', '7', '2', '2', '9', '1', '5', '2', '6', '3', '8', '1', '0', '3', '1', '1', '0', '9', '2', '3', '0', '6', '4', '1', '3', '8', '3', '5', '0', '9', '0', '3', '2', '3', '9', '8', '5', '9', '9', '8', '6', '5', '7', '6', '0', '9', '8', '8', '1', '0', '9', '9', '4', '5', '4', '1', '6', '2', '8', '4', '0', '3', '0', '0', '0', '8', '3', '8', '5', '6', '6', '8', '1', '2', '1', '7', '0', '8', '5', '3', '0', '6', '3', '2', '3', '8', '5', '1', '3', '5', '9', '1', '1', '2', '0', '5', '8', '4', '5', '5', '9', '7', '3', '8', '1', '9', '9', '8', '1', '5', '2', '8', '9', '1', '1', '"', ',']

theorem object_fragment0291390_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 439) (SourceJson.white (fragment0291390Field007Chars00 ++ tail)) fragment0291390Acc00700 =
      SourceJson.object (fuel + 438) (SourceJson.white tail) fragment0291390Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291390_object_field_007"
  err.flush

noncomputable def fragment0291390Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0291390Field008Value00 : SourceJson := .str (String.ofList ['4', '1', '2', '7', '0', '6', '6', '5', '0', '1', '9', '4', '3', '8', '9', '2'])
noncomputable def fragment0291390Acc00900 : List (String × SourceJson) := (fragment0291390Field008Key00, fragment0291390Field008Value00) :: fragment0291390Acc00800
noncomputable def fragment0291390Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '1', '2', '7', '0', '6', '6', '5', '0', '1', '9', '4', '3', '8', '9', '2', '"', ',']

theorem object_fragment0291390_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 438) (SourceJson.white (fragment0291390Field008Chars00 ++ tail)) fragment0291390Acc00800 =
      SourceJson.object (fuel + 437) (SourceJson.white tail) fragment0291390Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291390_object_field_008"
  err.flush

noncomputable def fragment0291390Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0291390Field009Value00 : SourceJson := .str (String.ofList ['9', '6', '0', '3', '8', '6', '1', '4', '9', '7', '7', '9', '0', '4', '9', '4'])
noncomputable def fragment0291390Acc01000 : List (String × SourceJson) := (fragment0291390Field009Key00, fragment0291390Field009Value00) :: fragment0291390Acc00900
noncomputable def fragment0291390Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '6', '0', '3', '8', '6', '1', '4', '9', '7', '7', '9', '0', '4', '9', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0291390_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 437) (SourceJson.white (fragment0291390Field009Chars00 ++ tail)) fragment0291390Acc00900 =
      .ok (.obj (fragment0291390Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291390_object_field_009"
  err.flush

noncomputable def fragment0291390Chars : List Char := '{' :: (fragment0291390Field000Chars00 ++ fragment0291390Field001Chars00 ++ fragment0291390Field002Chars00 ++ fragment0291390Field003Chars00 ++ fragment0291390Field004Chars00 ++ fragment0291390Field005Chars00 ++ fragment0291390Field006Chars00 ++ fragment0291390Field007Chars00 ++ fragment0291390Field008Chars00 ++ fragment0291390Field009Chars00)
noncomputable def fragment0291390Value : SourceJson := .obj (fragment0291390Acc01000.reverse)

theorem value_fragment0291390 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 447) (fragment0291390Chars ++ tail) =
      .ok (fragment0291390Value, tail) := by
  have hinput : fragment0291390Chars ++ tail = '{' :: (fragment0291390Field000Chars00 ++ (fragment0291390Field001Chars00 ++ (fragment0291390Field002Chars00 ++ (fragment0291390Field003Chars00 ++ (fragment0291390Field004Chars00 ++ (fragment0291390Field005Chars00 ++ (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0291390Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 447) (fragment0291390Chars ++ tail) =
        SourceJson.value (fuel + 447) ('{' :: (fragment0291390Field000Chars00 ++ (fragment0291390Field001Chars00 ++ (fragment0291390Field002Chars00 ++ (fragment0291390Field003Chars00 ++ (fragment0291390Field004Chars00 ++ (fragment0291390Field005Chars00 ++ (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 447)) hinput
    _ = SourceJson.object (fuel + 446) (SourceJson.white (fragment0291390Field000Chars00 ++ (fragment0291390Field001Chars00 ++ (fragment0291390Field002Chars00 ++ (fragment0291390Field003Chars00 ++ (fragment0291390Field004Chars00 ++ (fragment0291390Field005Chars00 ++ (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail)))))))))))) fragment0291390Acc00000 := by rfl
    _ = SourceJson.object (fuel + 445) (SourceJson.white (fragment0291390Field001Chars00 ++ (fragment0291390Field002Chars00 ++ (fragment0291390Field003Chars00 ++ (fragment0291390Field004Chars00 ++ (fragment0291390Field005Chars00 ++ (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail))))))))))) fragment0291390Acc00100 := object_fragment0291390_field_000 fuel (fragment0291390Field001Chars00 ++ (fragment0291390Field002Chars00 ++ (fragment0291390Field003Chars00 ++ (fragment0291390Field004Chars00 ++ (fragment0291390Field005Chars00 ++ (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 444) (SourceJson.white (fragment0291390Field002Chars00 ++ (fragment0291390Field003Chars00 ++ (fragment0291390Field004Chars00 ++ (fragment0291390Field005Chars00 ++ (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail)))))))))) fragment0291390Acc00200 := object_fragment0291390_field_001 fuel (fragment0291390Field002Chars00 ++ (fragment0291390Field003Chars00 ++ (fragment0291390Field004Chars00 ++ (fragment0291390Field005Chars00 ++ (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 443) (SourceJson.white (fragment0291390Field003Chars00 ++ (fragment0291390Field004Chars00 ++ (fragment0291390Field005Chars00 ++ (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail))))))))) fragment0291390Acc00300 := object_fragment0291390_field_002 fuel (fragment0291390Field003Chars00 ++ (fragment0291390Field004Chars00 ++ (fragment0291390Field005Chars00 ++ (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 442) (SourceJson.white (fragment0291390Field004Chars00 ++ (fragment0291390Field005Chars00 ++ (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail)))))))) fragment0291390Acc00400 := object_fragment0291390_field_003 fuel (fragment0291390Field004Chars00 ++ (fragment0291390Field005Chars00 ++ (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 441) (SourceJson.white (fragment0291390Field005Chars00 ++ (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail))))))) fragment0291390Acc00500 := object_fragment0291390_field_004 fuel (fragment0291390Field005Chars00 ++ (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 440) (SourceJson.white (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail)))))) fragment0291390Acc00600 := object_fragment0291390_field_005 fuel (fragment0291390Field006Chars00 ++ (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 439) (SourceJson.white (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail))))) fragment0291390Acc00700 := object_fragment0291390_field_006 fuel (fragment0291390Field007Chars00 ++ (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 438) (SourceJson.white (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail)))) fragment0291390Acc00800 := object_fragment0291390_field_007 fuel (fragment0291390Field008Chars00 ++ (fragment0291390Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 437) (SourceJson.white (fragment0291390Field009Chars00 ++ (tail))) fragment0291390Acc00900 := object_fragment0291390_field_008 fuel (fragment0291390Field009Chars00 ++ (tail))
    _ = .ok (fragment0291390Value, tail) := object_fragment0291390_field_009 fuel (tail)

noncomputable def fragment0293440Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0293440Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0293440Field000Value00 : SourceJson := .number (String.ofList ['9', '0'])
noncomputable def fragment0293440Acc00100 : List (String × SourceJson) := (fragment0293440Field000Key00, fragment0293440Field000Value00) :: fragment0293440Acc00000
noncomputable def fragment0293440Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '0', ',']

theorem object_fragment0293440_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0293440Field000Chars00 ++ tail)) fragment0293440Acc00000 =
      SourceJson.object (fuel + 203) (SourceJson.white tail) fragment0293440Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0293440_object_field_000"
  err.flush

noncomputable def fragment0293440Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0293440Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['4'])]
noncomputable def fragment0293440Acc00200 : List (String × SourceJson) := (fragment0293440Field001Key00, fragment0293440Field001Value00) :: fragment0293440Acc00100
noncomputable def fragment0293440Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0293440_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0293440Field001Chars00 ++ tail)) fragment0293440Acc00100 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0293440Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0293440_object_field_001"
  err.flush

noncomputable def fragment0293440Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0293440Field002Value00 : SourceJson := .str (String.ofList ['3', '3', '1', '9', '7', '4', '5', '8', '1', '5', '2', '2', '4', '7', '9', '2', '7', '3', '5', '0', '9', '9', '1', '8', '3', '7', '4', '1', '7', '8', '6', '4', '4', '3', '9', '9', '3', '0', '5', '3', '/', '2', '2', '2', '9', '6', '2', '5', '0', '9', '0', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0293440Acc00300 : List (String × SourceJson) := (fragment0293440Field002Key00, fragment0293440Field002Value00) :: fragment0293440Acc00200
noncomputable def fragment0293440Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '3', '1', '9', '7', '4', '5', '8', '1', '5', '2', '2', '4', '7', '9', '2', '7', '3', '5', '0', '9', '9', '1', '8', '3', '7', '4', '1', '7', '8', '6', '4', '4', '3', '9', '9', '3', '0', '5', '3', '/', '2', '2', '2', '9', '6', '2', '5', '0', '9', '0', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0293440_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0293440Field002Chars00 ++ tail)) fragment0293440Acc00200 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0293440Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0293440_object_field_002"
  err.flush

noncomputable def fragment0293440Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0293440Field003Value00 : SourceJson := .str (String.ofList ['9', '8', '4', '2', '0', '3', '/', '1', '3', '5', '4', '5', '0', '0', '0', '0', '0'])
noncomputable def fragment0293440Acc00400 : List (String × SourceJson) := (fragment0293440Field003Key00, fragment0293440Field003Value00) :: fragment0293440Acc00300
noncomputable def fragment0293440Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '8', '4', '2', '0', '3', '/', '1', '3', '5', '4', '5', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0293440_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0293440Field003Chars00 ++ tail)) fragment0293440Acc00300 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0293440Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0293440_object_field_003"
  err.flush

noncomputable def fragment0293440Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0293440Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0293440Acc00500 : List (String × SourceJson) := (fragment0293440Field004Key00, fragment0293440Field004Value00) :: fragment0293440Acc00400
noncomputable def fragment0293440Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0293440_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0293440Field004Chars00 ++ tail)) fragment0293440Acc00400 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0293440Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0293440_object_field_004"
  err.flush

noncomputable def fragment0293440Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0293440Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '2', '5', '2', '2', '0', '0', '3', '2', '8', '8', '7', '/', '4', '9', '8', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '4', '0', '4', '5', '1', '0', '1', '3', '/', '1', '1', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '9', '1', '2', '7', '1', '9', '0', '9', '/', '5', '4', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '7', '3', '5', '7', '1', '2', '3', '4', '2', '9', '/', '1', '6', '6', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '6', '4', '5', '4', '2', '2', '9', '3', '8', '1', '/', '1', '6', '6', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '3', '6', '1', '2', '7', '0', '6', '3', '7', '7', '/', '2', '4', '9', '2', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '0', '8', '0', '4', '1', '3', '7', '3', '/', '1', '4', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '2', '7', '7', '1', '2', '4', '1', '3', '/', '7', '1', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '8', '6', '6', '4', '9', '2', '3', '7', '4', '1', '/', '4', '9', '8', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '5', '4', '6', '2', '0', '2', '7', '/', '2', '3', '1', '8', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0293440Acc00600 : List (String × SourceJson) := (fragment0293440Field005Key00, fragment0293440Field005Value00) :: fragment0293440Acc00500
noncomputable def fragment0293440Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '5', '2', '2', '0', '0', '3', '2', '8', '8', '7', '/', '4', '9', '8', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '4', '0', '4', '5', '1', '0', '1', '3', '/', '1', '1', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '9', '1', '2', '7', '1', '9', '0', '9', '/', '5', '4', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '7', '3', '5', '7', '1', '2', '3', '4', '2', '9', '/', '1', '6', '6', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '4', '5', '4', '2', '2', '9', '3', '8', '1', '/', '1', '6', '6', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '3', '6', '1', '2', '7', '0', '6', '3', '7', '7', '/', '2', '4', '9', '2', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '0', '8', '0', '4', '1', '3', '7', '3', '/', '1', '4', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '2', '7', '7', '1', '2', '4', '1', '3', '/', '7', '1', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '6', '6', '4', '9', '2', '3', '7', '4', '1', '/', '4', '9', '8', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '5', '4', '6', '2', '0', '2', '7', '/', '2', '3', '1', '8', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0293440_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0293440Field005Chars00 ++ tail)) fragment0293440Acc00500 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0293440Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0293440_object_field_005"
  err.flush

noncomputable def fragment0293440Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0293440Field006Value00 : SourceJson := .str (String.ofList ['4', '9', '1', '0', '2', '3', '7', '7', '9', '8', '9', '1', '3', '9', '5', '5', '2', '7', '2', '6', '5', '6', '3', '4', '3', '1', '9', '3', '9', '1', '7', '6', '9', '2', '1', '3', '4', '1', '7', '3', '0', '6', '3', '6', '0', '9', '4', '0', '6', '2', '5', '/', '1', '9', '6', '0', '2', '8', '9', '3', '3', '7', '1', '2', '0', '1', '1', '1', '0', '7', '3', '0', '6', '1', '7', '0', '6', '4', '9', '0', '7', '6', '7', '8', '9', '0', '9', '8', '3', '7', '3', '2', '8', '6', '4', '5', '0', '1', '1', '4', '3', '6', '4', '3', '3', '0', '5', '2', '2', '1', '2', '9', '5', '1', '7', '4'])
noncomputable def fragment0293440Acc00700 : List (String × SourceJson) := (fragment0293440Field006Key00, fragment0293440Field006Value00) :: fragment0293440Acc00600
noncomputable def fragment0293440Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '9', '1', '0', '2', '3', '7', '7', '9', '8', '9', '1', '3', '9', '5', '5', '2', '7', '2', '6', '5', '6', '3', '4', '3', '1', '9', '3', '9', '1', '7', '6', '9', '2', '1', '3', '4', '1', '7', '3', '0', '6', '3', '6', '0', '9', '4', '0', '6', '2', '5', '/', '1', '9', '6', '0', '2', '8', '9', '3', '3', '7', '1', '2', '0', '1', '1', '1', '0', '7', '3', '0', '6', '1', '7', '0', '6', '4', '9', '0', '7', '6', '7', '8', '9', '0', '9', '8', '3', '7', '3', '2', '8', '6', '4', '5', '0', '1', '1', '4', '3', '6', '4', '3', '3', '0', '5', '2', '2', '1', '2', '9', '5', '1', '7', '4', '"', ',']

theorem object_fragment0293440_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0293440Field006Chars00 ++ tail)) fragment0293440Acc00600 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0293440Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0293440_object_field_006"
  err.flush

noncomputable def fragment0293440Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0293440Field007Value00 : SourceJson := .str (String.ofList ['8', '2', '0', '7', '2', '1', '0', '0', '4', '2', '4', '8', '2', '3', '7', '4', '2', '7', '7', '9', '4', '1', '3', '1', '1', '3', '0', '6', '3', '7', '0', '1', '8', '0', '5', '6', '7', '0', '5', '8', '0', '2', '9', '0', '6', '7', '6', '9', '7', '6', '3', '2', '6', '3', '5', '4', '0', '3', '9', '9', '5', '7', '0', '5', '6', '1', '5', '0', '3', '6', '3', '4', '3', '9', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '7', '7', '7', '3', '2', '7', '4', '5', '0', '6', '5', '5', '1', '3', '9', '1', '3', '2', '7', '0', '5', '9', '0', '5', '8', '0', '6', '6', '4', '9', '6', '9', '5', '6', '7', '4', '6', '8', '6', '7', '8', '2', '2', '8', '2', '1', '1', '6', '2', '9', '5', '7', '4', '2', '0', '4', '0', '5', '6', '9', '8', '9', '3', '7', '1', '2', '4', '5', '2', '4', '2', '0', '2', '5', '9', '0', '3', '6', '0', '5', '9', '8', '4', '1', '5', '4', '7', '7', '3', '3', '0', '1', '9', '6', '0', '7', '6', '4', '0', '5', '1'])
noncomputable def fragment0293440Acc00800 : List (String × SourceJson) := (fragment0293440Field007Key00, fragment0293440Field007Value00) :: fragment0293440Acc00700
noncomputable def fragment0293440Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '2', '0', '7', '2', '1', '0', '0', '4', '2', '4', '8', '2', '3', '7', '4', '2', '7', '7', '9', '4', '1', '3', '1', '1', '3', '0', '6', '3', '7', '0', '1', '8', '0', '5', '6', '7', '0', '5', '8', '0', '2', '9', '0', '6', '7', '6', '9', '7', '6', '3', '2', '6', '3', '5', '4', '0', '3', '9', '9', '5', '7', '0', '5', '6', '1', '5', '0', '3', '6', '3', '4', '3', '9', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '7', '7', '7', '3', '2', '7', '4', '5', '0', '6', '5', '5', '1', '3', '9', '1', '3', '2', '7', '0', '5', '9', '0', '5', '8', '0', '6', '6', '4', '9', '6', '9', '5', '6', '7', '4', '6', '8', '6', '7', '8', '2', '2', '8', '2', '1', '1', '6', '2', '9', '5', '7', '4', '2', '0', '4', '0', '5', '6', '9', '8', '9', '3', '7', '1', '2', '4', '5', '2', '4', '2', '0', '2', '5', '9', '0', '3', '6', '0', '5', '9', '8', '4', '1', '5', '4', '7', '7', '3', '3', '0', '1', '9', '6', '0', '7', '6', '4', '0', '5', '1', '"', ',']

theorem object_fragment0293440_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0293440Field007Chars00 ++ tail)) fragment0293440Acc00700 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0293440Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0293440_object_field_007"
  err.flush

noncomputable def fragment0293440Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0293440Field008Value00 : SourceJson := .str (String.ofList ['1', '9', '8', '4', '5', '4', '9', '4', '7', '9', '2', '4', '9', '6', '6', '3', '5'])
noncomputable def fragment0293440Acc00900 : List (String × SourceJson) := (fragment0293440Field008Key00, fragment0293440Field008Value00) :: fragment0293440Acc00800
noncomputable def fragment0293440Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '8', '4', '5', '4', '9', '4', '7', '9', '2', '4', '9', '6', '6', '3', '5', '"', ',']

theorem object_fragment0293440_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0293440Field008Chars00 ++ tail)) fragment0293440Acc00800 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0293440Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0293440_object_field_008"
  err.flush

noncomputable def fragment0293440Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0293440Field009Value00 : SourceJson := .str (String.ofList ['5', '5', '2', '1', '1', '3', '5', '1', '9', '6', '0', '6', '9', '6', '7', '1', '5'])
noncomputable def fragment0293440Acc01000 : List (String × SourceJson) := (fragment0293440Field009Key00, fragment0293440Field009Value00) :: fragment0293440Acc00900
noncomputable def fragment0293440Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '5', '2', '1', '1', '3', '5', '1', '9', '6', '0', '6', '9', '6', '7', '1', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0293440_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0293440Field009Chars00 ++ tail)) fragment0293440Acc00900 =
      .ok (.obj (fragment0293440Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0293440_object_field_009"
  err.flush

noncomputable def fragment0293440Chars : List Char := '{' :: (fragment0293440Field000Chars00 ++ fragment0293440Field001Chars00 ++ fragment0293440Field002Chars00 ++ fragment0293440Field003Chars00 ++ fragment0293440Field004Chars00 ++ fragment0293440Field005Chars00 ++ fragment0293440Field006Chars00 ++ fragment0293440Field007Chars00 ++ fragment0293440Field008Chars00 ++ fragment0293440Field009Chars00)
noncomputable def fragment0293440Value : SourceJson := .obj (fragment0293440Acc01000.reverse)

theorem value_fragment0293440 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 205) (fragment0293440Chars ++ tail) =
      .ok (fragment0293440Value, tail) := by
  have hinput : fragment0293440Chars ++ tail = '{' :: (fragment0293440Field000Chars00 ++ (fragment0293440Field001Chars00 ++ (fragment0293440Field002Chars00 ++ (fragment0293440Field003Chars00 ++ (fragment0293440Field004Chars00 ++ (fragment0293440Field005Chars00 ++ (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0293440Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 205) (fragment0293440Chars ++ tail) =
        SourceJson.value (fuel + 205) ('{' :: (fragment0293440Field000Chars00 ++ (fragment0293440Field001Chars00 ++ (fragment0293440Field002Chars00 ++ (fragment0293440Field003Chars00 ++ (fragment0293440Field004Chars00 ++ (fragment0293440Field005Chars00 ++ (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 205)) hinput
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0293440Field000Chars00 ++ (fragment0293440Field001Chars00 ++ (fragment0293440Field002Chars00 ++ (fragment0293440Field003Chars00 ++ (fragment0293440Field004Chars00 ++ (fragment0293440Field005Chars00 ++ (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail)))))))))))) fragment0293440Acc00000 := by rfl
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0293440Field001Chars00 ++ (fragment0293440Field002Chars00 ++ (fragment0293440Field003Chars00 ++ (fragment0293440Field004Chars00 ++ (fragment0293440Field005Chars00 ++ (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail))))))))))) fragment0293440Acc00100 := object_fragment0293440_field_000 fuel (fragment0293440Field001Chars00 ++ (fragment0293440Field002Chars00 ++ (fragment0293440Field003Chars00 ++ (fragment0293440Field004Chars00 ++ (fragment0293440Field005Chars00 ++ (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0293440Field002Chars00 ++ (fragment0293440Field003Chars00 ++ (fragment0293440Field004Chars00 ++ (fragment0293440Field005Chars00 ++ (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail)))))))))) fragment0293440Acc00200 := object_fragment0293440_field_001 fuel (fragment0293440Field002Chars00 ++ (fragment0293440Field003Chars00 ++ (fragment0293440Field004Chars00 ++ (fragment0293440Field005Chars00 ++ (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0293440Field003Chars00 ++ (fragment0293440Field004Chars00 ++ (fragment0293440Field005Chars00 ++ (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail))))))))) fragment0293440Acc00300 := object_fragment0293440_field_002 fuel (fragment0293440Field003Chars00 ++ (fragment0293440Field004Chars00 ++ (fragment0293440Field005Chars00 ++ (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0293440Field004Chars00 ++ (fragment0293440Field005Chars00 ++ (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail)))))))) fragment0293440Acc00400 := object_fragment0293440_field_003 fuel (fragment0293440Field004Chars00 ++ (fragment0293440Field005Chars00 ++ (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0293440Field005Chars00 ++ (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail))))))) fragment0293440Acc00500 := object_fragment0293440_field_004 fuel (fragment0293440Field005Chars00 ++ (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail)))))) fragment0293440Acc00600 := object_fragment0293440_field_005 fuel (fragment0293440Field006Chars00 ++ (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail))))) fragment0293440Acc00700 := object_fragment0293440_field_006 fuel (fragment0293440Field007Chars00 ++ (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail)))) fragment0293440Acc00800 := object_fragment0293440_field_007 fuel (fragment0293440Field008Chars00 ++ (fragment0293440Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0293440Field009Chars00 ++ (tail))) fragment0293440Acc00900 := object_fragment0293440_field_008 fuel (fragment0293440Field009Chars00 ++ (tail))
    _ = .ok (fragment0293440Value, tail) := object_fragment0293440_field_009 fuel (tail)

noncomputable def fragment0294984Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0294984Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0294984Field000Value00 : SourceJson := .number (String.ofList ['9', '1'])
noncomputable def fragment0294984Acc00100 : List (String × SourceJson) := (fragment0294984Field000Key00, fragment0294984Field000Value00) :: fragment0294984Acc00000
noncomputable def fragment0294984Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '1', ',']

theorem object_fragment0294984_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 564) (SourceJson.white (fragment0294984Field000Chars00 ++ tail)) fragment0294984Acc00000 =
      SourceJson.object (fuel + 563) (SourceJson.white tail) fragment0294984Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294984_object_field_000"
  err.flush

noncomputable def fragment0294984Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0294984Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0294984Acc00200 : List (String × SourceJson) := (fragment0294984Field001Key00, fragment0294984Field001Value00) :: fragment0294984Acc00100
noncomputable def fragment0294984Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0294984_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 563) (SourceJson.white (fragment0294984Field001Chars00 ++ tail)) fragment0294984Acc00100 =
      SourceJson.object (fuel + 562) (SourceJson.white tail) fragment0294984Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294984_object_field_001"
  err.flush

noncomputable def fragment0294984Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0294984Field002Value00 : SourceJson := .str (String.ofList ['2', '6', '9', '6', '0', '0', '7', '8', '3', '2', '0', '0', '7', '2', '3', '6', '0', '1', '9', '4', '1', '7', '9', '7', '9', '1', '0', '6', '8', '1', '5', '2', '6', '8', '8', '9', '6', '5', '4', '9', '6', '8', '8', '0', '9', '/', '3', '3', '6', '0', '1', '2', '4', '0', '0', '4', '1', '5', '8', '8', '8', '1', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0294984Acc00300 : List (String × SourceJson) := (fragment0294984Field002Key00, fragment0294984Field002Value00) :: fragment0294984Acc00200
noncomputable def fragment0294984Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '6', '9', '6', '0', '0', '7', '8', '3', '2', '0', '0', '7', '2', '3', '6', '0', '1', '9', '4', '1', '7', '9', '7', '9', '1', '0', '6', '8', '1', '5', '2', '6', '8', '8', '9', '6', '5', '4', '9', '6', '8', '8', '0', '9', '/', '3', '3', '6', '0', '1', '2', '4', '0', '0', '4', '1', '5', '8', '8', '8', '1', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0294984_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 562) (SourceJson.white (fragment0294984Field002Chars00 ++ tail)) fragment0294984Acc00200 =
      SourceJson.object (fuel + 561) (SourceJson.white tail) fragment0294984Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294984_object_field_002"
  err.flush

noncomputable def fragment0294984Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0294984Field003Value00 : SourceJson := .str (String.ofList ['1', '5', '9', '1', '7', '2', '6', '2', '4', '3', '0', '6', '6', '1', '/', '4', '3', '0', '7', '2', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0294984Acc00400 : List (String × SourceJson) := (fragment0294984Field003Key00, fragment0294984Field003Value00) :: fragment0294984Acc00300
noncomputable def fragment0294984Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '5', '9', '1', '7', '2', '6', '2', '4', '3', '0', '6', '6', '1', '/', '4', '3', '0', '7', '2', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0294984_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 561) (SourceJson.white (fragment0294984Field003Chars00 ++ tail)) fragment0294984Acc00300 =
      SourceJson.object (fuel + 560) (SourceJson.white tail) fragment0294984Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294984_object_field_003"
  err.flush

noncomputable def fragment0294984Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0294984Field004Value00 : SourceJson := .arr [.str (String.ofList ['5', '3', '9', '0', '5', '9', '7', '/', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '3', '9', '0', '5', '4', '1', '/', '1', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0294984Acc00500 : List (String × SourceJson) := (fragment0294984Field004Key00, fragment0294984Field004Value00) :: fragment0294984Acc00400
noncomputable def fragment0294984Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '0', '5', '9', '7', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '3', '9', '0', '5', '4', '1', '/', '1', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0294984_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 560) (SourceJson.white (fragment0294984Field004Chars00 ++ tail)) fragment0294984Acc00400 =
      SourceJson.object (fuel + 559) (SourceJson.white tail) fragment0294984Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294984_object_field_004"
  err.flush

noncomputable def fragment0294984Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0294984Field005Value00 : SourceJson := .arr [.str (String.ofList ['9', '9', '2', '5', '0', '2', '0', '4', '6', '2', '1', '8', '0', '1', '4', '1', '2', '3', '5', '8', '6', '0', '3', '4', '6', '5', '6', '0', '7', '/', '1', '1', '6', '5', '5', '0', '3', '8', '5', '8', '3', '2', '1', '3', '8', '2', '8', '8', '0', '9', '2', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '6', '6', '7', '5', '8', '8', '6', '4', '5', '2', '0', '3', '4', '6', '1', '7', '5', '1', '8', '1', '1', '9', '6', '1', '5', '1', '/', '8', '7', '1', '2', '2', '3', '8', '1', '4', '3', '5', '9', '8', '3', '7', '7', '0', '1', '6', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '8', '1', '8', '7', '6', '1', '7', '7', '6', '9', '8', '6', '9', '5', '2', '1', '8', '3', '6', '2', '9', '3', '6', '8', '6', '9', '9', '/', '8', '1', '9', '4', '9', '4', '9', '0', '0', '3', '8', '2', '2', '2', '2', '3', '3', '8', '1', '4', '8', '3', '9', '3', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '7', '6', '8', '4', '7', '0', '0', '5', '2', '3', '7', '8', '7', '1', '9', '9', '1', '4', '1', '2', '1', '5', '2', '0', '4', '2', '0', '3', '/', '4', '3', '7', '0', '6', '3', '9', '4', '6', '8', '7', '0', '5', '1', '8', '5', '8', '0', '3', '4', '5', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '9', '3', '0', '5', '9', '6', '3', '7', '3', '6', '4', '3', '5', '8', '5', '9', '9', '7', '2', '8', '1', '3', '6', '7', '3', '4', '3', '2', '3', '/', '1', '3', '1', '1', '1', '9', '1', '8', '4', '0', '6', '1', '1', '5', '5', '5', '7', '4', '1', '0', '3', '7', '4', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '1', '9', '0', '7', '9', '6', '9', '5', '3', '5', '0', '7', '5', '3', '5', '4', '2', '3', '4', '6', '4', '4', '7', '7', '1', '7', '/', '4', '7', '6', '7', '9', '7', '0', '3', '2', '9', '4', '9', '6', '5', '6', '6', '3', '3', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '4', '0', '9', '6', '2', '8', '1', '1', '6', '7', '4', '0', '3', '7', '8', '5', '6', '9', '0', '8', '3', '5', '6', '3', '2', '7', '/', '2', '3', '8', '3', '9', '8', '5', '1', '6', '4', '7', '4', '8', '2', '8', '3', '1', '6', '5', '5', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '9', '7', '1', '9', '7', '1', '7', '5', '0', '8', '3', '6', '2', '7', '9', '6', '7', '3', '4', '7', '5', '0', '1', '4', '6', '1', '/', '9', '5', '3', '5', '9', '4', '0', '6', '5', '8', '9', '9', '3', '1', '3', '2', '6', '6', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '7', '2', '6', '8', '5', '5', '6', '7', '1', '1', '4', '2', '5', '0', '6', '3', '0', '5', '2', '4', '8', '4', '3', '3', '0', '8', '9', '/', '4', '7', '6', '7', '9', '7', '0', '3', '2', '9', '4', '9', '6', '5', '6', '6', '3', '3', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '4', '3', '7', '9', '5', '6', '8', '0', '5', '2', '6', '6', '4', '6', '6', '5', '4', '0', '4', '3', '6', '1', '0', '9', '3', '/', '9', '6', '8', '0', '2', '6', '4', '6', '0', '3', '9', '9', '8', '1', '9', '6', '6', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0294984Acc00600 : List (String × SourceJson) := (fragment0294984Field005Key00, fragment0294984Field005Value00) :: fragment0294984Acc00500
noncomputable def fragment0294984Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '2', '5', '0', '2', '0', '4', '6', '2', '1', '8', '0', '1', '4', '1', '2', '3', '5', '8', '6', '0', '3', '4', '6', '5', '6', '0', '7', '/', '1', '1', '6', '5', '5', '0', '3', '8', '5', '8', '3', '2', '1', '3', '8', '2', '8', '8', '0', '9', '2', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '6', '6', '7', '5', '8', '8', '6', '4', '5', '2', '0', '3', '4', '6', '1', '7', '5', '1', '8', '1', '1', '9', '6', '1', '5', '1', '/', '8', '7', '1', '2', '2', '3', '8', '1', '4', '3', '5', '9', '8', '3', '7', '7', '0', '1', '6', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '8', '1', '8', '7', '6', '1', '7', '7', '6', '9', '8', '6', '9', '5', '2', '1', '8', '3', '6', '2', '9', '3', '6', '8', '6', '9', '9', '/', '8', '1', '9', '4', '9', '4', '9', '0', '0', '3', '8', '2', '2', '2', '2', '3', '3', '8', '1', '4', '8', '3', '9', '3', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '7', '6', '8', '4', '7', '0', '0', '5', '2', '3', '7', '8', '7', '1', '9', '9', '1', '4', '1', '2', '1', '5', '2', '0', '4', '2', '0', '3', '/', '4', '3', '7', '0', '6', '3', '9', '4', '6', '8', '7', '0', '5', '1', '8', '5', '8', '0', '3', '4', '5', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '3', '0', '5', '9', '6', '3', '7', '3', '6', '4', '3', '5', '8', '5', '9', '9', '7', '2', '8', '1', '3', '6', '7', '3', '4', '3', '2', '3', '/', '1', '3', '1', '1', '1', '9', '1', '8', '4', '0', '6', '1', '1', '5', '5', '5', '7', '4', '1', '0', '3', '7', '4', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '1', '9', '0', '7', '9', '6', '9', '5', '3', '5', '0', '7', '5', '3', '5', '4', '2', '3', '4', '6', '4', '4', '7', '7', '1', '7', '/', '4', '7', '6', '7', '9', '7', '0', '3', '2', '9', '4', '9', '6', '5', '6', '6', '3', '3', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '5', '4', '0', '9', '6', '2', '8', '1', '1', '6', '7', '4', '0', '3', '7', '8', '5', '6', '9', '0', '8', '3', '5', '6', '3', '2', '7', '/', '2', '3', '8', '3', '9', '8', '5', '1', '6', '4', '7', '4', '8', '2', '8', '3', '1', '6', '5', '5', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '9', '7', '1', '9', '7', '1', '7', '5', '0', '8', '3', '6', '2', '7', '9', '6', '7', '3', '4', '7', '5', '0', '1', '4', '6', '1', '/', '9', '5', '3', '5', '9', '4', '0', '6', '5', '8', '9', '9', '3', '1', '3', '2', '6', '6', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '2', '6', '8', '5', '5', '6', '7', '1', '1', '4', '2', '5', '0', '6', '3', '0', '5', '2', '4', '8', '4', '3', '3', '0', '8', '9', '/', '4', '7', '6', '7', '9', '7', '0', '3', '2', '9', '4', '9', '6', '5', '6', '6', '3', '3', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '4', '3', '7', '9', '5', '6', '8', '0', '5', '2', '6', '6', '4', '6', '6', '5', '4', '0', '4', '3', '6', '1', '0', '9', '3', '/', '9', '6', '8', '0', '2', '6', '4', '6', '0', '3', '9', '9', '8', '1', '9', '6', '6', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0294984_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 559) (SourceJson.white (fragment0294984Field005Chars00 ++ tail)) fragment0294984Acc00500 =
      SourceJson.object (fuel + 558) (SourceJson.white tail) fragment0294984Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294984_object_field_005"
  err.flush

noncomputable def fragment0294984Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0294984Field006Value00 : SourceJson := .str (String.ofList ['6', '7', '0', '5', '1', '6', '6', '2', '7', '7', '6', '8', '3', '8', '4', '2', '2', '7', '4', '5', '2', '8', '3', '3', '3', '1', '7', '3', '7', '9', '2', '3', '3', '1', '3', '6', '6', '7', '1', '9', '1', '8', '7', '4', '3', '8', '0', '9', '2', '9', '3', '7', '8', '9', '4', '9', '2', '0', '3', '1', '2', '5', '0', '/', '9', '3', '7', '5', '4', '1', '2', '0', '7', '7', '9', '4', '0', '0', '3', '7', '8', '0', '1', '1', '3', '0', '1', '9', '7', '2', '2', '4', '0', '5', '8', '9', '5', '1', '8', '2', '5', '3', '7', '1', '8', '8', '5', '7', '6', '9', '5', '7', '1', '3', '7', '9', '7', '1', '9', '7', '3', '4', '1', '6', '5', '0', '8', '4', '4', '2', '4', '3', '5', '0', '0', '7', '2', '0', '2', '8', '5', '1'])
noncomputable def fragment0294984Acc00700 : List (String × SourceJson) := (fragment0294984Field006Key00, fragment0294984Field006Value00) :: fragment0294984Acc00600
noncomputable def fragment0294984Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '7', '0', '5', '1', '6', '6', '2', '7', '7', '6', '8', '3', '8', '4', '2', '2', '7', '4', '5', '2', '8', '3', '3', '3', '1', '7', '3', '7', '9', '2', '3', '3', '1', '3', '6', '6', '7', '1', '9', '1', '8', '7', '4', '3', '8', '0', '9', '2', '9', '3', '7', '8', '9', '4', '9', '2', '0', '3', '1', '2', '5', '0', '/', '9', '3', '7', '5', '4', '1', '2', '0', '7', '7', '9', '4', '0', '0', '3', '7', '8', '0', '1', '1', '3', '0', '1', '9', '7', '2', '2', '4', '0', '5', '8', '9', '5', '1', '8', '2', '5', '3', '7', '1', '8', '8', '5', '7', '6', '9', '5', '7', '1', '3', '7', '9', '7', '1', '9', '7', '3', '4', '1', '6', '5', '0', '8', '4', '4', '2', '4', '3', '5', '0', '0', '7', '2', '0', '2', '8', '5', '1', '"', ',']

theorem object_fragment0294984_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 558) (SourceJson.white (fragment0294984Field006Chars00 ++ tail)) fragment0294984Acc00600 =
      SourceJson.object (fuel + 557) (SourceJson.white tail) fragment0294984Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294984_object_field_006"
  err.flush

noncomputable def fragment0294984Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0294984Field007Value00 : SourceJson := .str (String.ofList ['9', '4', '3', '1', '8', '9', '3', '2', '2', '5', '7', '3', '0', '6', '0', '5', '4', '7', '5', '7', '2', '7', '6', '2', '2', '9', '8', '3', '9', '9', '5', '7', '4', '2', '8', '4', '0', '0', '3', '4', '6', '0', '9', '2', '7', '9', '3', '2', '7', '3', '6', '8', '0', '9', '5', '1', '9', '1', '3', '1', '7', '3', '1', '7', '3', '9', '9', '8', '2', '9', '1', '2', '7', '6', '0', '6', '4', '5', '5', '1', '5', '5', '5', '1', '3', '5', '3', '8', '2', '2', '5', '4', '0', '4', '2', '2', '1', '8', '9', '3', '4', '9', '0', '7', '7', '7', '9', '0', '4', '1', '0', '2', '2', '9', '8', '0', '4', '0', '0', '3', '9', '1', '2', '5', '6', '9', '4', '3', '1', '2', '2', '0', '9', '7', '5', '4', '7', '2', '5', '6', '9', '3', '5', '1', '1', '1', '8', '2', '4', '2', '6', '4', '3', '9', '8', '8', '7', '2', '0', '4', '8', '9', '5', '3', '4', '1', '7', '5', '9', '0', '3', '9', '9', '9', '0', '6', '4', '2', '9', '2', '1', '2', '6', '8', '8', '9', '8', '0', '2', '7', '0', '7', '9', '2', '2', '0', '5', '2', '4', '1', '2', '2', '8', '1', '3', '5', '4', '9', '3', '6', '3', '0', '5', '0', '7', '9', '4', '4', '8', '6', '1', '7', '6', '5', '8', '5', '0', '3', '4', '6', '1', '5', '1', '9', '8', '2', '0', '6', '0', '3', '1', '4', '1', '2', '2', '8', '1', '8', '9', '7', '6', '4', '5', '0', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '7', '7', '6', '6', '7', '1', '7', '6', '3', '7', '9', '5', '1', '0', '2', '5', '3', '0', '4', '5', '1', '5', '9', '8', '3', '3', '4', '6', '2', '4', '6', '2', '0', '8', '8', '8', '9', '6', '0', '9', '3', '1', '8', '3', '3', '0', '2', '2', '6', '6', '4', '0', '9', '0', '2', '5', '0', '1', '0', '4', '4', '2', '3', '6', '0', '5', '9', '9', '3', '4', '6', '5', '2', '3', '7', '1', '2', '7', '6', '1', '5', '6', '5', '3', '4', '6', '8', '5', '6', '5', '1', '0', '9', '2', '2', '7', '2', '1', '3', '3', '6', '1', '3', '3', '7', '9', '5', '0', '5', '4', '5', '5', '0', '1', '9', '3', '9', '5', '5', '2', '8', '8', '3', '7', '7', '1', '5', '1', '3', '9', '9', '4', '9', '2', '8', '2', '0', '4', '5', '3', '4', '5', '2', '9', '7', '4', '9', '2', '8', '6', '2', '4', '7', '7', '3', '1', '4', '5', '2', '6', '4', '7', '1', '2', '9', '0', '0', '2', '1', '4', '1', '9', '6', '6', '1', '6', '3', '1', '3', '3', '0', '0', '2', '7', '3', '3', '2', '1', '6', '5', '5', '7', '4', '6', '1', '5', '5', '6', '4', '2', '3', '7', '7', '5', '2', '6', '5', '5', '9', '2', '6', '5', '2', '1', '8', '0', '1', '0', '4', '1', '1', '8', '4', '9', '5', '2', '1', '0', '0', '7', '2', '8', '4', '1', '5', '5', '7', '7', '5', '7', '2', '3', '8', '0', '9', '7', '7', '4', '2', '2', '9', '6', '3', '3', '2', '2', '2', '8', '0', '6', '8', '7', '9', '3', '0', '8', '8', '8', '3', '9', '6', '5', '3', '0', '6', '4', '3', '8', '8', '6', '1', '4', '7'])
noncomputable def fragment0294984Acc00800 : List (String × SourceJson) := (fragment0294984Field007Key00, fragment0294984Field007Value00) :: fragment0294984Acc00700
noncomputable def fragment0294984Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '4', '3', '1', '8', '9', '3', '2', '2', '5', '7', '3', '0', '6', '0', '5', '4', '7', '5', '7', '2', '7', '6', '2', '2', '9', '8', '3', '9', '9', '5', '7', '4', '2', '8', '4', '0', '0', '3', '4', '6', '0', '9', '2', '7', '9', '3', '2', '7', '3', '6', '8', '0', '9', '5', '1', '9', '1', '3', '1', '7', '3', '1', '7', '3', '9', '9', '8', '2', '9', '1', '2', '7', '6', '0', '6', '4', '5', '5', '1', '5', '5', '5', '1', '3', '5', '3', '8', '2', '2', '5', '4', '0', '4', '2', '2', '1', '8', '9', '3', '4', '9', '0', '7', '7', '7', '9', '0', '4', '1', '0', '2', '2', '9', '8', '0', '4', '0', '0', '3', '9', '1', '2', '5', '6', '9', '4', '3', '1', '2', '2', '0', '9', '7', '5', '4', '7', '2', '5', '6', '9', '3', '5', '1', '1', '1', '8', '2', '4', '2', '6', '4', '3', '9', '8', '8', '7', '2', '0', '4', '8', '9', '5', '3', '4', '1', '7', '5', '9', '0', '3', '9', '9', '9', '0', '6', '4', '2', '9', '2', '1', '2', '6', '8', '8', '9', '8', '0', '2', '7', '0', '7', '9', '2', '2', '0', '5', '2', '4', '1', '2', '2', '8', '1', '3', '5', '4', '9', '3', '6', '3', '0', '5', '0', '7', '9', '4', '4', '8', '6', '1', '7', '6', '5', '8', '5', '0', '3', '4', '6', '1', '5', '1', '9', '8', '2', '0', '6', '0', '3', '1', '4', '1', '2', '2', '8', '1', '8', '9', '7', '6', '4', '5', '0', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '7', '7', '6', '6', '7', '1', '7', '6', '3', '7', '9', '5', '1', '0', '2', '5', '3', '0', '4', '5', '1', '5', '9', '8', '3', '3', '4', '6', '2', '4', '6', '2', '0', '8', '8', '8', '9', '6', '0', '9', '3', '1', '8', '3', '3', '0', '2', '2', '6', '6', '4', '0', '9', '0', '2', '5', '0', '1', '0', '4', '4', '2', '3', '6', '0', '5', '9', '9', '3', '4', '6', '5', '2', '3', '7', '1', '2', '7', '6', '1', '5', '6', '5', '3', '4', '6', '8', '5', '6', '5', '1', '0', '9', '2', '2', '7', '2', '1', '3', '3', '6', '1', '3', '3', '7', '9', '5', '0', '5', '4', '5', '5', '0', '1', '9', '3', '9', '5', '5', '2', '8', '8', '3', '7', '7', '1', '5', '1', '3', '9', '9', '4', '9', '2', '8', '2', '0', '4', '5', '3', '4', '5', '2', '9', '7', '4', '9', '2', '8', '6', '2', '4', '7', '7', '3', '1', '4', '5', '2', '6', '4', '7', '1', '2', '9', '0', '0', '2', '1', '4', '1', '9', '6', '6', '1', '6', '3', '1', '3', '3', '0', '0', '2', '7', '3', '3', '2', '1', '6', '5', '5', '7', '4', '6', '1', '5', '5', '6', '4', '2', '3', '7', '7', '5', '2', '6', '5', '5', '9', '2', '6', '5', '2', '1', '8', '0', '1', '0', '4', '1', '1', '8', '4', '9', '5', '2', '1', '0', '0', '7', '2', '8', '4', '1', '5', '5', '7', '7', '5', '7', '2', '3', '8', '0', '9', '7', '7', '4', '2', '2', '9', '6', '3', '3', '2', '2', '2', '8', '0', '6', '8', '7', '9', '3', '0', '8', '8', '8', '3', '9', '6', '5', '3', '0', '6', '4', '3', '8', '8', '6', '1', '4', '7', '"', ',']

theorem object_fragment0294984_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 557) (SourceJson.white (fragment0294984Field007Chars00 ++ tail)) fragment0294984Acc00700 =
      SourceJson.object (fuel + 556) (SourceJson.white tail) fragment0294984Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294984_object_field_007"
  err.flush

noncomputable def fragment0294984Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0294984Field008Value00 : SourceJson := .str (String.ofList ['5', '6', '6', '6', '2', '8', '9', '6', '4', '2', '7', '0', '7', '8'])
noncomputable def fragment0294984Acc00900 : List (String × SourceJson) := (fragment0294984Field008Key00, fragment0294984Field008Value00) :: fragment0294984Acc00800
noncomputable def fragment0294984Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '6', '6', '6', '2', '8', '9', '6', '4', '2', '7', '0', '7', '8', '"', ',']

theorem object_fragment0294984_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 556) (SourceJson.white (fragment0294984Field008Chars00 ++ tail)) fragment0294984Acc00800 =
      SourceJson.object (fuel + 555) (SourceJson.white tail) fragment0294984Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294984_object_field_008"
  err.flush

noncomputable def fragment0294984Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0294984Field009Value00 : SourceJson := .str (String.ofList ['1', '2', '9', '3', '6', '0', '2', '2', '6', '7', '6', '3', '9', '3', '8'])
noncomputable def fragment0294984Acc01000 : List (String × SourceJson) := (fragment0294984Field009Key00, fragment0294984Field009Value00) :: fragment0294984Acc00900
noncomputable def fragment0294984Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '9', '3', '6', '0', '2', '2', '6', '7', '6', '3', '9', '3', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0294984_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 555) (SourceJson.white (fragment0294984Field009Chars00 ++ tail)) fragment0294984Acc00900 =
      .ok (.obj (fragment0294984Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294984_object_field_009"
  err.flush

noncomputable def fragment0294984Chars : List Char := '{' :: (fragment0294984Field000Chars00 ++ fragment0294984Field001Chars00 ++ fragment0294984Field002Chars00 ++ fragment0294984Field003Chars00 ++ fragment0294984Field004Chars00 ++ fragment0294984Field005Chars00 ++ fragment0294984Field006Chars00 ++ fragment0294984Field007Chars00 ++ fragment0294984Field008Chars00 ++ fragment0294984Field009Chars00)
noncomputable def fragment0294984Value : SourceJson := .obj (fragment0294984Acc01000.reverse)

theorem value_fragment0294984 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 565) (fragment0294984Chars ++ tail) =
      .ok (fragment0294984Value, tail) := by
  have hinput : fragment0294984Chars ++ tail = '{' :: (fragment0294984Field000Chars00 ++ (fragment0294984Field001Chars00 ++ (fragment0294984Field002Chars00 ++ (fragment0294984Field003Chars00 ++ (fragment0294984Field004Chars00 ++ (fragment0294984Field005Chars00 ++ (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0294984Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 565) (fragment0294984Chars ++ tail) =
        SourceJson.value (fuel + 565) ('{' :: (fragment0294984Field000Chars00 ++ (fragment0294984Field001Chars00 ++ (fragment0294984Field002Chars00 ++ (fragment0294984Field003Chars00 ++ (fragment0294984Field004Chars00 ++ (fragment0294984Field005Chars00 ++ (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 565)) hinput
    _ = SourceJson.object (fuel + 564) (SourceJson.white (fragment0294984Field000Chars00 ++ (fragment0294984Field001Chars00 ++ (fragment0294984Field002Chars00 ++ (fragment0294984Field003Chars00 ++ (fragment0294984Field004Chars00 ++ (fragment0294984Field005Chars00 ++ (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail)))))))))))) fragment0294984Acc00000 := by rfl
    _ = SourceJson.object (fuel + 563) (SourceJson.white (fragment0294984Field001Chars00 ++ (fragment0294984Field002Chars00 ++ (fragment0294984Field003Chars00 ++ (fragment0294984Field004Chars00 ++ (fragment0294984Field005Chars00 ++ (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail))))))))))) fragment0294984Acc00100 := object_fragment0294984_field_000 fuel (fragment0294984Field001Chars00 ++ (fragment0294984Field002Chars00 ++ (fragment0294984Field003Chars00 ++ (fragment0294984Field004Chars00 ++ (fragment0294984Field005Chars00 ++ (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 562) (SourceJson.white (fragment0294984Field002Chars00 ++ (fragment0294984Field003Chars00 ++ (fragment0294984Field004Chars00 ++ (fragment0294984Field005Chars00 ++ (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail)))))))))) fragment0294984Acc00200 := object_fragment0294984_field_001 fuel (fragment0294984Field002Chars00 ++ (fragment0294984Field003Chars00 ++ (fragment0294984Field004Chars00 ++ (fragment0294984Field005Chars00 ++ (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 561) (SourceJson.white (fragment0294984Field003Chars00 ++ (fragment0294984Field004Chars00 ++ (fragment0294984Field005Chars00 ++ (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail))))))))) fragment0294984Acc00300 := object_fragment0294984_field_002 fuel (fragment0294984Field003Chars00 ++ (fragment0294984Field004Chars00 ++ (fragment0294984Field005Chars00 ++ (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 560) (SourceJson.white (fragment0294984Field004Chars00 ++ (fragment0294984Field005Chars00 ++ (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail)))))))) fragment0294984Acc00400 := object_fragment0294984_field_003 fuel (fragment0294984Field004Chars00 ++ (fragment0294984Field005Chars00 ++ (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 559) (SourceJson.white (fragment0294984Field005Chars00 ++ (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail))))))) fragment0294984Acc00500 := object_fragment0294984_field_004 fuel (fragment0294984Field005Chars00 ++ (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 558) (SourceJson.white (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail)))))) fragment0294984Acc00600 := object_fragment0294984_field_005 fuel (fragment0294984Field006Chars00 ++ (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 557) (SourceJson.white (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail))))) fragment0294984Acc00700 := object_fragment0294984_field_006 fuel (fragment0294984Field007Chars00 ++ (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 556) (SourceJson.white (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail)))) fragment0294984Acc00800 := object_fragment0294984_field_007 fuel (fragment0294984Field008Chars00 ++ (fragment0294984Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 555) (SourceJson.white (fragment0294984Field009Chars00 ++ (tail))) fragment0294984Acc00900 := object_fragment0294984_field_008 fuel (fragment0294984Field009Chars00 ++ (tail))
    _ = .ok (fragment0294984Value, tail) := object_fragment0294984_field_009 fuel (tail)

noncomputable def fragment0297291Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0297291Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0297291Field000Value00 : SourceJson := .number (String.ofList ['9', '2'])
noncomputable def fragment0297291Acc00100 : List (String × SourceJson) := (fragment0297291Field000Key00, fragment0297291Field000Value00) :: fragment0297291Acc00000
noncomputable def fragment0297291Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '2', ',']

theorem object_fragment0297291_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 513) (SourceJson.white (fragment0297291Field000Chars00 ++ tail)) fragment0297291Acc00000 =
      SourceJson.object (fuel + 512) (SourceJson.white tail) fragment0297291Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0297291_object_field_000"
  err.flush

noncomputable def fragment0297291Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0297291Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0297291Acc00200 : List (String × SourceJson) := (fragment0297291Field001Key00, fragment0297291Field001Value00) :: fragment0297291Acc00100
noncomputable def fragment0297291Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0297291_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 512) (SourceJson.white (fragment0297291Field001Chars00 ++ tail)) fragment0297291Acc00100 =
      SourceJson.object (fuel + 511) (SourceJson.white tail) fragment0297291Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0297291_object_field_001"
  err.flush

noncomputable def fragment0297291Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0297291Field002Value00 : SourceJson := .str (String.ofList ['1', '2', '4', '1', '7', '4', '2', '8', '6', '4', '7', '0', '1', '6', '7', '8', '4', '8', '8', '1', '0', '5', '3', '8', '3', '7', '4', '8', '5', '1', '4', '4', '5', '8', '0', '4', '9', '4', '8', '0', '0', '5', '5', '1', '9', '/', '1', '1', '9', '7', '6', '6', '7', '9', '6', '1', '8', '7', '8', '4', '1', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0297291Acc00300 : List (String × SourceJson) := (fragment0297291Field002Key00, fragment0297291Field002Value00) :: fragment0297291Acc00200
noncomputable def fragment0297291Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '2', '4', '1', '7', '4', '2', '8', '6', '4', '7', '0', '1', '6', '7', '8', '4', '8', '8', '1', '0', '5', '3', '8', '3', '7', '4', '8', '5', '1', '4', '4', '5', '8', '0', '4', '9', '4', '8', '0', '0', '5', '5', '1', '9', '/', '1', '1', '9', '7', '6', '6', '7', '9', '6', '1', '8', '7', '8', '4', '1', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0297291_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 511) (SourceJson.white (fragment0297291Field002Chars00 ++ tail)) fragment0297291Acc00200 =
      SourceJson.object (fuel + 510) (SourceJson.white tail) fragment0297291Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0297291_object_field_002"
  err.flush

noncomputable def fragment0297291Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0297291Field003Value00 : SourceJson := .str (String.ofList ['1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9', '/', '3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0297291Acc00400 : List (String × SourceJson) := (fragment0297291Field003Key00, fragment0297291Field003Value00) :: fragment0297291Acc00300
noncomputable def fragment0297291Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9', '/', '3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0297291_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 510) (SourceJson.white (fragment0297291Field003Chars00 ++ tail)) fragment0297291Acc00300 =
      SourceJson.object (fuel + 509) (SourceJson.white tail) fragment0297291Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0297291_object_field_003"
  err.flush

noncomputable def fragment0297291Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0297291Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0297291Acc00500 : List (String × SourceJson) := (fragment0297291Field004Key00, fragment0297291Field004Value00) :: fragment0297291Acc00400
noncomputable def fragment0297291Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0297291_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 509) (SourceJson.white (fragment0297291Field004Chars00 ++ tail)) fragment0297291Acc00400 =
      SourceJson.object (fuel + 508) (SourceJson.white tail) fragment0297291Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0297291_object_field_004"
  err.flush

noncomputable def fragment0297291Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0297291Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '2', '1', '2', '4', '0', '8', '6', '3', '3', '1', '1', '1', '7', '4', '7', '7', '5', '9', '0', '3', '6', '7', '5', '5', '5', '1', '/', '3', '6', '9', '9', '2', '3', '6', '5', '8', '6', '3', '7', '6', '4', '3', '2', '0', '2', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '8', '0', '9', '3', '2', '3', '8', '4', '6', '3', '2', '0', '7', '9', '6', '2', '4', '7', '8', '9', '7', '0', '3', '/', '1', '2', '2', '8', '9', '8', '2', '2', '5', '4', '6', '1', '0', '1', '1', '0', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '6', '7', '3', '9', '8', '4', '4', '2', '1', '5', '7', '4', '9', '3', '3', '2', '2', '9', '1', '3', '8', '3', '2', '8', '3', '1', '/', '2', '4', '6', '6', '1', '5', '7', '7', '2', '4', '2', '5', '0', '9', '5', '4', '6', '8', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '1', '9', '2', '0', '3', '6', '8', '7', '7', '6', '1', '6', '3', '4', '3', '2', '5', '8', '4', '6', '7', '7', '8', '9', '4', '3', '/', '7', '3', '9', '8', '4', '7', '3', '1', '7', '2', '7', '5', '2', '8', '6', '4', '0', '5', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '5', '7', '1', '7', '6', '1', '5', '7', '0', '0', '1', '3', '3', '0', '4', '8', '7', '3', '0', '8', '6', '0', '3', '2', '9', '1', '/', '7', '3', '9', '8', '4', '7', '3', '1', '7', '2', '7', '5', '2', '8', '6', '4', '0', '5', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '8', '6', '0', '1', '7', '5', '8', '7', '7', '8', '6', '6', '9', '9', '3', '7', '1', '4', '8', '8', '1', '4', '3', '/', '8', '9', '6', '7', '8', '4', '6', '2', '7', '0', '0', '0', '3', '4', '7', '1', '5', '8', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '7', '2', '3', '5', '2', '0', '3', '4', '2', '8', '6', '2', '4', '5', '7', '8', '4', '0', '4', '7', '4', '4', '7', '/', '6', '7', '2', '5', '8', '8', '4', '7', '0', '2', '5', '0', '2', '6', '0', '3', '6', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '0', '6', '5', '0', '6', '0', '9', '1', '5', '4', '9', '9', '8', '6', '2', '7', '8', '5', '0', '3', '0', '1', '/', '5', '3', '8', '0', '7', '0', '7', '7', '6', '2', '0', '0', '2', '0', '8', '2', '9', '4', '8', '4', '8', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '6', '5', '7', '8', '6', '9', '8', '2', '7', '5', '0', '4', '9', '7', '8', '4', '5', '4', '4', '5', '9', '7', '7', '/', '6', '7', '2', '5', '8', '8', '4', '7', '0', '2', '5', '0', '2', '6', '0', '3', '6', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '7', '8', '9', '8', '2', '8', '3', '5', '2', '5', '6', '3', '6', '7', '9', '9', '3', '8', '1', '3', '2', '6', '1', '/', '1', '2', '2', '8', '9', '8', '2', '2', '5', '4', '6', '1', '0', '1', '1', '0', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0297291Acc00600 : List (String × SourceJson) := (fragment0297291Field005Key00, fragment0297291Field005Value00) :: fragment0297291Acc00500
noncomputable def fragment0297291Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '1', '2', '4', '0', '8', '6', '3', '3', '1', '1', '1', '7', '4', '7', '7', '5', '9', '0', '3', '6', '7', '5', '5', '5', '1', '/', '3', '6', '9', '9', '2', '3', '6', '5', '8', '6', '3', '7', '6', '4', '3', '2', '0', '2', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '8', '0', '9', '3', '2', '3', '8', '4', '6', '3', '2', '0', '7', '9', '6', '2', '4', '7', '8', '9', '7', '0', '3', '/', '1', '2', '2', '8', '9', '8', '2', '2', '5', '4', '6', '1', '0', '1', '1', '0', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '6', '7', '3', '9', '8', '4', '4', '2', '1', '5', '7', '4', '9', '3', '3', '2', '2', '9', '1', '3', '8', '3', '2', '8', '3', '1', '/', '2', '4', '6', '6', '1', '5', '7', '7', '2', '4', '2', '5', '0', '9', '5', '4', '6', '8', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '1', '9', '2', '0', '3', '6', '8', '7', '7', '6', '1', '6', '3', '4', '3', '2', '5', '8', '4', '6', '7', '7', '8', '9', '4', '3', '/', '7', '3', '9', '8', '4', '7', '3', '1', '7', '2', '7', '5', '2', '8', '6', '4', '0', '5', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '5', '7', '1', '7', '6', '1', '5', '7', '0', '0', '1', '3', '3', '0', '4', '8', '7', '3', '0', '8', '6', '0', '3', '2', '9', '1', '/', '7', '3', '9', '8', '4', '7', '3', '1', '7', '2', '7', '5', '2', '8', '6', '4', '0', '5', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '8', '6', '0', '1', '7', '5', '8', '7', '7', '8', '6', '6', '9', '9', '3', '7', '1', '4', '8', '8', '1', '4', '3', '/', '8', '9', '6', '7', '8', '4', '6', '2', '7', '0', '0', '0', '3', '4', '7', '1', '5', '8', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '7', '2', '3', '5', '2', '0', '3', '4', '2', '8', '6', '2', '4', '5', '7', '8', '4', '0', '4', '7', '4', '4', '7', '/', '6', '7', '2', '5', '8', '8', '4', '7', '0', '2', '5', '0', '2', '6', '0', '3', '6', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '6', '5', '0', '6', '0', '9', '1', '5', '4', '9', '9', '8', '6', '2', '7', '8', '5', '0', '3', '0', '1', '/', '5', '3', '8', '0', '7', '0', '7', '7', '6', '2', '0', '0', '2', '0', '8', '2', '9', '4', '8', '4', '8', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '6', '5', '7', '8', '6', '9', '8', '2', '7', '5', '0', '4', '9', '7', '8', '4', '5', '4', '4', '5', '9', '7', '7', '/', '6', '7', '2', '5', '8', '8', '4', '7', '0', '2', '5', '0', '2', '6', '0', '3', '6', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '7', '8', '9', '8', '2', '8', '3', '5', '2', '5', '6', '3', '6', '7', '9', '9', '3', '8', '1', '3', '2', '6', '1', '/', '1', '2', '2', '8', '9', '8', '2', '2', '5', '4', '6', '1', '0', '1', '1', '0', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0297291_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 508) (SourceJson.white (fragment0297291Field005Chars00 ++ tail)) fragment0297291Acc00500 =
      SourceJson.object (fuel + 507) (SourceJson.white tail) fragment0297291Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0297291_object_field_005"
  err.flush

noncomputable def fragment0297291Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0297291Field006Value00 : SourceJson := .str (String.ofList ['1', '4', '0', '8', '0', '1', '5', '0', '6', '6', '1', '7', '7', '9', '3', '3', '8', '7', '6', '1', '5', '1', '9', '1', '9', '3', '5', '7', '3', '2', '8', '5', '0', '7', '7', '8', '5', '6', '5', '9', '6', '5', '8', '6', '0', '5', '1', '1', '5', '7', '8', '5', '1', '5', '5', '0', '1', '0', '0', '0', '0', '0', '0', '/', '2', '6', '2', '3', '4', '4', '7', '7', '2', '2', '9', '1', '4', '8', '8', '9', '9', '9', '5', '0', '8', '9', '2', '1', '2', '7', '7', '7', '6', '1', '3', '8', '7', '0', '1', '4', '9', '4', '1', '3', '6', '4', '5', '0', '7', '5', '2', '2', '8', '2', '7', '2', '1', '2', '3', '9', '4', '7', '8', '3', '7', '3', '0', '8', '8', '7', '5', '5', '6', '6', '4', '9', '2', '1', '1', '1', '9'])
noncomputable def fragment0297291Acc00700 : List (String × SourceJson) := (fragment0297291Field006Key00, fragment0297291Field006Value00) :: fragment0297291Acc00600
noncomputable def fragment0297291Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '0', '8', '0', '1', '5', '0', '6', '6', '1', '7', '7', '9', '3', '3', '8', '7', '6', '1', '5', '1', '9', '1', '9', '3', '5', '7', '3', '2', '8', '5', '0', '7', '7', '8', '5', '6', '5', '9', '6', '5', '8', '6', '0', '5', '1', '1', '5', '7', '8', '5', '1', '5', '5', '0', '1', '0', '0', '0', '0', '0', '0', '/', '2', '6', '2', '3', '4', '4', '7', '7', '2', '2', '9', '1', '4', '8', '8', '9', '9', '9', '5', '0', '8', '9', '2', '1', '2', '7', '7', '7', '6', '1', '3', '8', '7', '0', '1', '4', '9', '4', '1', '3', '6', '4', '5', '0', '7', '5', '2', '2', '8', '2', '7', '2', '1', '2', '3', '9', '4', '7', '8', '3', '7', '3', '0', '8', '8', '7', '5', '5', '6', '6', '4', '9', '2', '1', '1', '1', '9', '"', ',']

theorem object_fragment0297291_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 507) (SourceJson.white (fragment0297291Field006Chars00 ++ tail)) fragment0297291Acc00600 =
      SourceJson.object (fuel + 506) (SourceJson.white tail) fragment0297291Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0297291_object_field_006"
  err.flush

noncomputable def fragment0297291Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0297291Field007Value00 : SourceJson := .str (String.ofList ['1', '8', '3', '3', '8', '1', '4', '5', '1', '7', '3', '5', '6', '0', '9', '6', '3', '1', '6', '7', '9', '5', '1', '0', '9', '5', '0', '5', '9', '0', '3', '1', '4', '1', '6', '9', '9', '6', '9', '8', '7', '1', '0', '2', '3', '4', '5', '1', '4', '5', '3', '8', '5', '0', '8', '7', '1', '0', '2', '1', '3', '9', '8', '8', '2', '6', '9', '8', '9', '9', '0', '4', '8', '2', '6', '5', '6', '3', '8', '3', '8', '4', '8', '5', '7', '4', '5', '3', '9', '6', '7', '6', '4', '4', '4', '4', '8', '7', '7', '3', '0', '5', '5', '7', '7', '5', '0', '6', '0', '5', '8', '4', '1', '1', '5', '8', '2', '1', '9', '3', '4', '0', '8', '5', '7', '1', '2', '9', '3', '0', '1', '6', '6', '1', '8', '9', '0', '2', '7', '1', '8', '5', '3', '5', '6', '1', '6', '8', '8', '2', '0', '1', '5', '3', '0', '0', '6', '6', '1', '9', '8', '1', '8', '0', '1', '5', '9', '5', '7', '1', '3', '9', '9', '8', '5', '4', '2', '3', '4', '4', '5', '5', '3', '5', '0', '1', '9', '0', '3', '0', '6', '0', '0', '6', '8', '0', '1', '7', '1', '7', '5', '1', '6', '7', '7', '5', '8', '4', '4', '9', '6', '7', '2', '9', '0', '1', '7', '0', '9', '7', '6', '3', '4', '1', '0', '9', '8', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '0', '7', '2', '9', '4', '5', '6', '9', '7', '3', '3', '5', '9', '7', '3', '9', '3', '4', '9', '5', '6', '2', '4', '5', '3', '0', '4', '6', '9', '8', '5', '1', '9', '0', '3', '7', '8', '6', '9', '3', '6', '0', '8', '8', '7', '3', '9', '6', '7', '9', '3', '1', '0', '7', '0', '3', '6', '7', '8', '4', '0', '6', '9', '0', '6', '4', '6', '4', '3', '2', '4', '6', '7', '6', '0', '5', '7', '1', '6', '2', '0', '9', '5', '9', '7', '1', '4', '6', '1', '9', '2', '6', '8', '3', '5', '7', '2', '8', '7', '6', '0', '7', '6', '6', '8', '9', '6', '3', '0', '6', '5', '2', '2', '7', '1', '8', '3', '6', '0', '1', '7', '1', '4', '0', '5', '9', '5', '2', '1', '0', '6', '8', '2', '9', '6', '4', '5', '5', '0', '2', '3', '4', '7', '9', '4', '1', '7', '8', '9', '2', '2', '0', '6', '8', '8', '6', '6', '6', '2', '8', '6', '2', '3', '3', '2', '7', '5', '9', '1', '2', '4', '2', '2', '6', '2', '3', '3', '8', '7', '5', '0', '9', '7', '6', '6', '8', '9', '0', '1', '6', '6', '3', '4', '6', '7', '2', '1', '5', '9', '7', '1', '7', '6', '0', '8', '9', '7', '2', '3', '1', '3', '7', '4', '7', '3', '7', '7', '1', '5', '7', '6', '3', '5', '1', '8', '8', '8', '9', '0', '3', '8', '8', '2', '0', '7', '4', '4', '6', '6', '4', '0', '7', '9', '2', '7', '0', '1', '8', '3', '7', '5', '0', '5', '5', '5', '3'])
noncomputable def fragment0297291Acc00800 : List (String × SourceJson) := (fragment0297291Field007Key00, fragment0297291Field007Value00) :: fragment0297291Acc00700
noncomputable def fragment0297291Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '3', '3', '8', '1', '4', '5', '1', '7', '3', '5', '6', '0', '9', '6', '3', '1', '6', '7', '9', '5', '1', '0', '9', '5', '0', '5', '9', '0', '3', '1', '4', '1', '6', '9', '9', '6', '9', '8', '7', '1', '0', '2', '3', '4', '5', '1', '4', '5', '3', '8', '5', '0', '8', '7', '1', '0', '2', '1', '3', '9', '8', '8', '2', '6', '9', '8', '9', '9', '0', '4', '8', '2', '6', '5', '6', '3', '8', '3', '8', '4', '8', '5', '7', '4', '5', '3', '9', '6', '7', '6', '4', '4', '4', '4', '8', '7', '7', '3', '0', '5', '5', '7', '7', '5', '0', '6', '0', '5', '8', '4', '1', '1', '5', '8', '2', '1', '9', '3', '4', '0', '8', '5', '7', '1', '2', '9', '3', '0', '1', '6', '6', '1', '8', '9', '0', '2', '7', '1', '8', '5', '3', '5', '6', '1', '6', '8', '8', '2', '0', '1', '5', '3', '0', '0', '6', '6', '1', '9', '8', '1', '8', '0', '1', '5', '9', '5', '7', '1', '3', '9', '9', '8', '5', '4', '2', '3', '4', '4', '5', '5', '3', '5', '0', '1', '9', '0', '3', '0', '6', '0', '0', '6', '8', '0', '1', '7', '1', '7', '5', '1', '6', '7', '7', '5', '8', '4', '4', '9', '6', '7', '2', '9', '0', '1', '7', '0', '9', '7', '6', '3', '4', '1', '0', '9', '8', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '0', '7', '2', '9', '4', '5', '6', '9', '7', '3', '3', '5', '9', '7', '3', '9', '3', '4', '9', '5', '6', '2', '4', '5', '3', '0', '4', '6', '9', '8', '5', '1', '9', '0', '3', '7', '8', '6', '9', '3', '6', '0', '8', '8', '7', '3', '9', '6', '7', '9', '3', '1', '0', '7', '0', '3', '6', '7', '8', '4', '0', '6', '9', '0', '6', '4', '6', '4', '3', '2', '4', '6', '7', '6', '0', '5', '7', '1', '6', '2', '0', '9', '5', '9', '7', '1', '4', '6', '1', '9', '2', '6', '8', '3', '5', '7', '2', '8', '7', '6', '0', '7', '6', '6', '8', '9', '6', '3', '0', '6', '5', '2', '2', '7', '1', '8', '3', '6', '0', '1', '7', '1', '4', '0', '5', '9', '5', '2', '1', '0', '6', '8', '2', '9', '6', '4', '5', '5', '0', '2', '3', '4', '7', '9', '4', '1', '7', '8', '9', '2', '2', '0', '6', '8', '8', '6', '6', '6', '2', '8', '6', '2', '3', '3', '2', '7', '5', '9', '1', '2', '4', '2', '2', '6', '2', '3', '3', '8', '7', '5', '0', '9', '7', '6', '6', '8', '9', '0', '1', '6', '6', '3', '4', '6', '7', '2', '1', '5', '9', '7', '1', '7', '6', '0', '8', '9', '7', '2', '3', '1', '3', '7', '4', '7', '3', '7', '7', '1', '5', '7', '6', '3', '5', '1', '8', '8', '8', '9', '0', '3', '8', '8', '2', '0', '7', '4', '4', '6', '6', '4', '0', '7', '9', '2', '7', '0', '1', '8', '3', '7', '5', '0', '5', '5', '5', '3', '"', ',']

theorem object_fragment0297291_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 506) (SourceJson.white (fragment0297291Field007Chars00 ++ tail)) fragment0297291Acc00700 =
      SourceJson.object (fuel + 505) (SourceJson.white tail) fragment0297291Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0297291_object_field_007"
  err.flush

noncomputable def fragment0297291Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0297291Field008Value00 : SourceJson := .str (String.ofList ['4', '2', '5', '2', '2', '0', '7', '7', '1', '5', '4', '9', '1', '6', '8'])
noncomputable def fragment0297291Acc00900 : List (String × SourceJson) := (fragment0297291Field008Key00, fragment0297291Field008Value00) :: fragment0297291Acc00800
noncomputable def fragment0297291Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '2', '5', '2', '2', '0', '7', '7', '1', '5', '4', '9', '1', '6', '8', '"', ',']

theorem object_fragment0297291_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 505) (SourceJson.white (fragment0297291Field008Chars00 ++ tail)) fragment0297291Acc00800 =
      SourceJson.object (fuel + 504) (SourceJson.white tail) fragment0297291Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0297291_object_field_008"
  err.flush

noncomputable def fragment0297291Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0297291Field009Value00 : SourceJson := .str (String.ofList ['1', '3', '1', '2', '1', '1', '4', '7', '5', '7', '6', '5', '7', '1', '3', '4'])
noncomputable def fragment0297291Acc01000 : List (String × SourceJson) := (fragment0297291Field009Key00, fragment0297291Field009Value00) :: fragment0297291Acc00900
noncomputable def fragment0297291Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '1', '2', '1', '1', '4', '7', '5', '7', '6', '5', '7', '1', '3', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0297291_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 504) (SourceJson.white (fragment0297291Field009Chars00 ++ tail)) fragment0297291Acc00900 =
      .ok (.obj (fragment0297291Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0297291_object_field_009"
  err.flush

noncomputable def fragment0297291Chars : List Char := '{' :: (fragment0297291Field000Chars00 ++ fragment0297291Field001Chars00 ++ fragment0297291Field002Chars00 ++ fragment0297291Field003Chars00 ++ fragment0297291Field004Chars00 ++ fragment0297291Field005Chars00 ++ fragment0297291Field006Chars00 ++ fragment0297291Field007Chars00 ++ fragment0297291Field008Chars00 ++ fragment0297291Field009Chars00)
noncomputable def fragment0297291Value : SourceJson := .obj (fragment0297291Acc01000.reverse)

theorem value_fragment0297291 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 514) (fragment0297291Chars ++ tail) =
      .ok (fragment0297291Value, tail) := by
  have hinput : fragment0297291Chars ++ tail = '{' :: (fragment0297291Field000Chars00 ++ (fragment0297291Field001Chars00 ++ (fragment0297291Field002Chars00 ++ (fragment0297291Field003Chars00 ++ (fragment0297291Field004Chars00 ++ (fragment0297291Field005Chars00 ++ (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0297291Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 514) (fragment0297291Chars ++ tail) =
        SourceJson.value (fuel + 514) ('{' :: (fragment0297291Field000Chars00 ++ (fragment0297291Field001Chars00 ++ (fragment0297291Field002Chars00 ++ (fragment0297291Field003Chars00 ++ (fragment0297291Field004Chars00 ++ (fragment0297291Field005Chars00 ++ (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 514)) hinput
    _ = SourceJson.object (fuel + 513) (SourceJson.white (fragment0297291Field000Chars00 ++ (fragment0297291Field001Chars00 ++ (fragment0297291Field002Chars00 ++ (fragment0297291Field003Chars00 ++ (fragment0297291Field004Chars00 ++ (fragment0297291Field005Chars00 ++ (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail)))))))))))) fragment0297291Acc00000 := by rfl
    _ = SourceJson.object (fuel + 512) (SourceJson.white (fragment0297291Field001Chars00 ++ (fragment0297291Field002Chars00 ++ (fragment0297291Field003Chars00 ++ (fragment0297291Field004Chars00 ++ (fragment0297291Field005Chars00 ++ (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail))))))))))) fragment0297291Acc00100 := object_fragment0297291_field_000 fuel (fragment0297291Field001Chars00 ++ (fragment0297291Field002Chars00 ++ (fragment0297291Field003Chars00 ++ (fragment0297291Field004Chars00 ++ (fragment0297291Field005Chars00 ++ (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 511) (SourceJson.white (fragment0297291Field002Chars00 ++ (fragment0297291Field003Chars00 ++ (fragment0297291Field004Chars00 ++ (fragment0297291Field005Chars00 ++ (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail)))))))))) fragment0297291Acc00200 := object_fragment0297291_field_001 fuel (fragment0297291Field002Chars00 ++ (fragment0297291Field003Chars00 ++ (fragment0297291Field004Chars00 ++ (fragment0297291Field005Chars00 ++ (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 510) (SourceJson.white (fragment0297291Field003Chars00 ++ (fragment0297291Field004Chars00 ++ (fragment0297291Field005Chars00 ++ (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail))))))))) fragment0297291Acc00300 := object_fragment0297291_field_002 fuel (fragment0297291Field003Chars00 ++ (fragment0297291Field004Chars00 ++ (fragment0297291Field005Chars00 ++ (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 509) (SourceJson.white (fragment0297291Field004Chars00 ++ (fragment0297291Field005Chars00 ++ (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail)))))))) fragment0297291Acc00400 := object_fragment0297291_field_003 fuel (fragment0297291Field004Chars00 ++ (fragment0297291Field005Chars00 ++ (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 508) (SourceJson.white (fragment0297291Field005Chars00 ++ (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail))))))) fragment0297291Acc00500 := object_fragment0297291_field_004 fuel (fragment0297291Field005Chars00 ++ (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 507) (SourceJson.white (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail)))))) fragment0297291Acc00600 := object_fragment0297291_field_005 fuel (fragment0297291Field006Chars00 ++ (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 506) (SourceJson.white (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail))))) fragment0297291Acc00700 := object_fragment0297291_field_006 fuel (fragment0297291Field007Chars00 ++ (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 505) (SourceJson.white (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail)))) fragment0297291Acc00800 := object_fragment0297291_field_007 fuel (fragment0297291Field008Chars00 ++ (fragment0297291Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 504) (SourceJson.white (fragment0297291Field009Chars00 ++ (tail))) fragment0297291Acc00900 := object_fragment0297291_field_008 fuel (fragment0297291Field009Chars00 ++ (tail))
    _ = .ok (fragment0297291Value, tail) := object_fragment0297291_field_009 fuel (tail)

noncomputable def fragment0299497Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0299497Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0299497Field000Value00 : SourceJson := .number (String.ofList ['9', '3'])
noncomputable def fragment0299497Acc00100 : List (String × SourceJson) := (fragment0299497Field000Key00, fragment0299497Field000Value00) :: fragment0299497Acc00000
noncomputable def fragment0299497Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '3', ',']

theorem object_fragment0299497_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 472) (SourceJson.white (fragment0299497Field000Chars00 ++ tail)) fragment0299497Acc00000 =
      SourceJson.object (fuel + 471) (SourceJson.white tail) fragment0299497Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0299497_object_field_000"
  err.flush

noncomputable def fragment0299497Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0299497Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0299497Acc00200 : List (String × SourceJson) := (fragment0299497Field001Key00, fragment0299497Field001Value00) :: fragment0299497Acc00100
noncomputable def fragment0299497Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0299497_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 471) (SourceJson.white (fragment0299497Field001Chars00 ++ tail)) fragment0299497Acc00100 =
      SourceJson.object (fuel + 470) (SourceJson.white tail) fragment0299497Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0299497_object_field_001"
  err.flush

noncomputable def fragment0299497Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0299497Field002Value00 : SourceJson := .str (String.ofList ['1', '2', '2', '9', '2', '3', '4', '2', '1', '6', '2', '5', '0', '2', '7', '7', '1', '4', '2', '9', '8', '0', '8', '4', '7', '4', '3', '2', '5', '2', '7', '5', '0', '6', '3', '2', '9', '7', '7', '7', '2', '9', '7', '9', '5', '9', '/', '1', '3', '0', '9', '9', '4', '9', '3', '3', '3', '3', '0', '4', '5', '1', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0299497Acc00300 : List (String × SourceJson) := (fragment0299497Field002Key00, fragment0299497Field002Value00) :: fragment0299497Acc00200
noncomputable def fragment0299497Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '2', '2', '9', '2', '3', '4', '2', '1', '6', '2', '5', '0', '2', '7', '7', '1', '4', '2', '9', '8', '0', '8', '4', '7', '4', '3', '2', '5', '2', '7', '5', '0', '6', '3', '2', '9', '7', '7', '7', '2', '9', '7', '9', '5', '9', '/', '1', '3', '0', '9', '9', '4', '9', '3', '3', '3', '3', '0', '4', '5', '1', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0299497_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 470) (SourceJson.white (fragment0299497Field002Chars00 ++ tail)) fragment0299497Acc00200 =
      SourceJson.object (fuel + 469) (SourceJson.white tail) fragment0299497Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0299497_object_field_002"
  err.flush

noncomputable def fragment0299497Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0299497Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0299497Acc00400 : List (String × SourceJson) := (fragment0299497Field003Key00, fragment0299497Field003Value00) :: fragment0299497Acc00300
noncomputable def fragment0299497Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0299497_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 469) (SourceJson.white (fragment0299497Field003Chars00 ++ tail)) fragment0299497Acc00300 =
      SourceJson.object (fuel + 468) (SourceJson.white tail) fragment0299497Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0299497_object_field_003"
  err.flush

noncomputable def fragment0299497Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0299497Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0299497Acc00500 : List (String × SourceJson) := (fragment0299497Field004Key00, fragment0299497Field004Value00) :: fragment0299497Acc00400
noncomputable def fragment0299497Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0299497_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 468) (SourceJson.white (fragment0299497Field004Chars00 ++ tail)) fragment0299497Acc00400 =
      SourceJson.object (fuel + 467) (SourceJson.white tail) fragment0299497Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0299497_object_field_004"
  err.flush

noncomputable def fragment0299497Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0299497Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '0', '9', '7', '9', '7', '6', '6', '7', '2', '6', '2', '4', '0', '4', '2', '6', '8', '9', '2', '6', '6', '0', '9', '/', '2', '4', '0', '0', '1', '1', '3', '9', '1', '8', '0', '3', '2', '2', '4', '3', '4', '5', '9', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '7', '6', '1', '8', '6', '6', '0', '5', '4', '7', '0', '2', '0', '3', '6', '4', '6', '4', '0', '2', '9', '/', '9', '9', '6', '7', '2', '5', '0', '4', '9', '0', '1', '6', '7', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '5', '6', '1', '4', '0', '2', '4', '0', '3', '0', '3', '7', '3', '6', '1', '6', '1', '3', '7', '8', '1', '1', '/', '8', '6', '9', '6', '0', '6', '4', '9', '2', '0', '4', '0', '6', '6', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '8', '2', '4', '1', '5', '5', '4', '7', '1', '8', '7', '7', '4', '4', '7', '8', '1', '9', '8', '2', '0', '3', '2', '9', '/', '6', '0', '0', '0', '2', '8', '4', '7', '9', '5', '0', '8', '0', '6', '0', '8', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '5', '1', '0', '0', '8', '5', '2', '4', '8', '8', '6', '7', '1', '4', '9', '2', '4', '4', '9', '3', '5', '5', '7', '3', '/', '6', '0', '0', '0', '2', '8', '4', '7', '9', '5', '0', '8', '0', '6', '0', '8', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '1', '8', '6', '9', '2', '5', '0', '8', '3', '9', '1', '9', '9', '2', '0', '8', '0', '8', '1', '5', '7', '/', '3', '6', '3', '6', '5', '3', '6', '2', '3', '9', '4', '4', '2', '7', '9', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '5', '6', '4', '4', '1', '2', '4', '1', '3', '6', '6', '3', '2', '7', '9', '2', '2', '0', '2', '8', '6', '1', '/', '5', '4', '5', '4', '8', '0', '4', '3', '5', '9', '1', '6', '4', '1', '8', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '8', '8', '4', '4', '2', '0', '2', '2', '3', '7', '0', '5', '1', '3', '3', '6', '6', '7', '6', '1', '9', '/', '1', '0', '9', '0', '9', '6', '0', '8', '7', '1', '8', '3', '2', '8', '3', '7', '9', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '1', '4', '5', '7', '5', '1', '7', '7', '2', '0', '9', '9', '6', '2', '6', '3', '3', '2', '5', '9', '5', '1', '/', '5', '4', '5', '4', '8', '0', '4', '3', '5', '9', '1', '6', '4', '1', '8', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '6', '1', '2', '7', '3', '3', '1', '2', '5', '9', '7', '4', '1', '9', '4', '7', '7', '5', '4', '2', '3', '/', '9', '9', '6', '7', '2', '5', '0', '4', '9', '0', '1', '6', '7', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0299497Acc00600 : List (String × SourceJson) := (fragment0299497Field005Key00, fragment0299497Field005Value00) :: fragment0299497Acc00500
noncomputable def fragment0299497Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '9', '7', '9', '7', '6', '6', '7', '2', '6', '2', '4', '0', '4', '2', '6', '8', '9', '2', '6', '6', '0', '9', '/', '2', '4', '0', '0', '1', '1', '3', '9', '1', '8', '0', '3', '2', '2', '4', '3', '4', '5', '9', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '7', '6', '1', '8', '6', '6', '0', '5', '4', '7', '0', '2', '0', '3', '6', '4', '6', '4', '0', '2', '9', '/', '9', '9', '6', '7', '2', '5', '0', '4', '9', '0', '1', '6', '7', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '5', '6', '1', '4', '0', '2', '4', '0', '3', '0', '3', '7', '3', '6', '1', '6', '1', '3', '7', '8', '1', '1', '/', '8', '6', '9', '6', '0', '6', '4', '9', '2', '0', '4', '0', '6', '6', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '8', '2', '4', '1', '5', '5', '4', '7', '1', '8', '7', '7', '4', '4', '7', '8', '1', '9', '8', '2', '0', '3', '2', '9', '/', '6', '0', '0', '0', '2', '8', '4', '7', '9', '5', '0', '8', '0', '6', '0', '8', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '5', '1', '0', '0', '8', '5', '2', '4', '8', '8', '6', '7', '1', '4', '9', '2', '4', '4', '9', '3', '5', '5', '7', '3', '/', '6', '0', '0', '0', '2', '8', '4', '7', '9', '5', '0', '8', '0', '6', '0', '8', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '1', '8', '6', '9', '2', '5', '0', '8', '3', '9', '1', '9', '9', '2', '0', '8', '0', '8', '1', '5', '7', '/', '3', '6', '3', '6', '5', '3', '6', '2', '3', '9', '4', '4', '2', '7', '9', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '5', '6', '4', '4', '1', '2', '4', '1', '3', '6', '6', '3', '2', '7', '9', '2', '2', '0', '2', '8', '6', '1', '/', '5', '4', '5', '4', '8', '0', '4', '3', '5', '9', '1', '6', '4', '1', '8', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '8', '8', '4', '4', '2', '0', '2', '2', '3', '7', '0', '5', '1', '3', '3', '6', '6', '7', '6', '1', '9', '/', '1', '0', '9', '0', '9', '6', '0', '8', '7', '1', '8', '3', '2', '8', '3', '7', '9', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '1', '4', '5', '7', '5', '1', '7', '7', '2', '0', '9', '9', '6', '2', '6', '3', '3', '2', '5', '9', '5', '1', '/', '5', '4', '5', '4', '8', '0', '4', '3', '5', '9', '1', '6', '4', '1', '8', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '6', '1', '2', '7', '3', '3', '1', '2', '5', '9', '7', '4', '1', '9', '4', '7', '7', '5', '4', '2', '3', '/', '9', '9', '6', '7', '2', '5', '0', '4', '9', '0', '1', '6', '7', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0299497_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 467) (SourceJson.white (fragment0299497Field005Chars00 ++ tail)) fragment0299497Acc00500 =
      SourceJson.object (fuel + 466) (SourceJson.white tail) fragment0299497Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0299497_object_field_005"
  err.flush

noncomputable def fragment0299497Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0299497Field006Value00 : SourceJson := .str (String.ofList ['2', '6', '3', '0', '7', '9', '6', '8', '3', '1', '5', '1', '9', '2', '6', '3', '5', '2', '4', '8', '4', '4', '7', '8', '3', '6', '6', '8', '1', '5', '5', '9', '2', '6', '9', '4', '2', '1', '1', '1', '6', '3', '5', '1', '8', '4', '6', '6', '5', '9', '1', '3', '3', '5', '1', '6', '8', '0', '0', '0', '0', '0', '/', '7', '2', '5', '8', '5', '5', '1', '0', '1', '2', '0', '1', '7', '4', '8', '2', '1', '9', '9', '8', '5', '1', '5', '7', '6', '8', '5', '5', '0', '5', '8', '1', '3', '8', '7', '5', '3', '3', '1', '8', '3', '8', '5', '5', '8', '3', '6', '3', '5', '5', '3', '5', '5', '2', '0', '8', '0', '4', '2', '9', '2', '9', '4', '9', '4', '5', '8', '0', '8', '9', '1', '0', '8', '6', '1'])
noncomputable def fragment0299497Acc00700 : List (String × SourceJson) := (fragment0299497Field006Key00, fragment0299497Field006Value00) :: fragment0299497Acc00600
noncomputable def fragment0299497Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '6', '3', '0', '7', '9', '6', '8', '3', '1', '5', '1', '9', '2', '6', '3', '5', '2', '4', '8', '4', '4', '7', '8', '3', '6', '6', '8', '1', '5', '5', '9', '2', '6', '9', '4', '2', '1', '1', '1', '6', '3', '5', '1', '8', '4', '6', '6', '5', '9', '1', '3', '3', '5', '1', '6', '8', '0', '0', '0', '0', '0', '/', '7', '2', '5', '8', '5', '5', '1', '0', '1', '2', '0', '1', '7', '4', '8', '2', '1', '9', '9', '8', '5', '1', '5', '7', '6', '8', '5', '5', '0', '5', '8', '1', '3', '8', '7', '5', '3', '3', '1', '8', '3', '8', '5', '5', '8', '3', '6', '3', '5', '5', '3', '5', '5', '2', '0', '8', '0', '4', '2', '9', '2', '9', '4', '9', '4', '5', '8', '0', '8', '9', '1', '0', '8', '6', '1', '"', ',']

theorem object_fragment0299497_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 466) (SourceJson.white (fragment0299497Field006Chars00 ++ tail)) fragment0299497Acc00600 =
      SourceJson.object (fuel + 465) (SourceJson.white tail) fragment0299497Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0299497_object_field_006"
  err.flush

noncomputable def fragment0299497Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0299497Field007Value00 : SourceJson := .str (String.ofList ['7', '2', '9', '1', '5', '5', '8', '2', '8', '7', '1', '9', '0', '7', '5', '0', '0', '6', '2', '8', '5', '5', '6', '5', '2', '0', '5', '7', '7', '8', '0', '6', '1', '5', '3', '3', '2', '4', '2', '9', '2', '6', '4', '0', '4', '6', '4', '1', '8', '9', '6', '5', '1', '0', '2', '5', '7', '4', '3', '7', '9', '1', '6', '1', '9', '7', '4', '6', '3', '5', '4', '4', '6', '1', '1', '1', '8', '3', '2', '3', '8', '8', '4', '2', '3', '1', '5', '3', '9', '9', '1', '2', '6', '2', '1', '9', '3', '7', '7', '4', '6', '8', '8', '3', '1', '3', '7', '7', '7', '0', '3', '3', '1', '6', '9', '3', '3', '3', '8', '2', '0', '9', '9', '4', '9', '9', '0', '4', '7', '3', '4', '3', '3', '3', '6', '2', '2', '8', '4', '1', '8', '7', '9', '6', '8', '6', '1', '3', '7', '2', '5', '0', '9', '9', '4', '9', '1', '4', '9', '6', '4', '6', '7', '6', '1', '0', '3', '2', '5', '0', '5', '8', '9', '1', '3', '5', '7', '7', '9', '7', '9', '4', '6', '5', '8', '5', '4', '5', '1', '3', '9', '9', '7', '8', '3', '2', '9', '9', '6', '7', '8', '8', '5', '3', '9', '2', '2', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '6', '0', '9', '3', '2', '4', '8', '2', '3', '4', '8', '7', '7', '2', '5', '4', '0', '2', '0', '9', '6', '1', '4', '7', '4', '2', '5', '5', '5', '9', '8', '9', '1', '8', '0', '5', '1', '4', '5', '8', '2', '1', '8', '0', '6', '0', '8', '7', '5', '5', '9', '2', '0', '8', '6', '0', '3', '4', '5', '7', '7', '1', '3', '8', '2', '4', '8', '3', '9', '8', '6', '2', '5', '6', '8', '4', '3', '4', '0', '0', '6', '1', '1', '9', '5', '4', '5', '0', '6', '5', '9', '9', '7', '2', '3', '4', '4', '0', '5', '7', '3', '8', '0', '1', '0', '1', '3', '3', '1', '5', '4', '7', '1', '8', '4', '7', '4', '8', '2', '6', '0', '0', '5', '8', '5', '5', '6', '1', '0', '8', '8', '7', '9', '5', '3', '9', '9', '4', '6', '5', '8', '9', '2', '4', '9', '2', '3', '8', '9', '3', '6', '8', '1', '5', '8', '4', '2', '3', '9', '1', '8', '1', '0', '3', '9', '9', '6', '9', '7', '7', '2', '1', '9', '8', '7', '5', '1', '8', '9', '8', '0', '0', '7', '2', '0', '3', '3', '4', '2', '7', '6', '5', '8', '8', '1', '3', '2', '5', '1', '0', '9', '8', '2', '6', '0', '5', '8', '6', '9', '2', '4', '0', '7', '5', '3', '4', '2', '4', '0', '8', '2', '8', '1', '9', '3', '0', '6', '8', '9', '1', '7', '4', '9', '1', '9', '3'])
noncomputable def fragment0299497Acc00800 : List (String × SourceJson) := (fragment0299497Field007Key00, fragment0299497Field007Value00) :: fragment0299497Acc00700
noncomputable def fragment0299497Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '2', '9', '1', '5', '5', '8', '2', '8', '7', '1', '9', '0', '7', '5', '0', '0', '6', '2', '8', '5', '5', '6', '5', '2', '0', '5', '7', '7', '8', '0', '6', '1', '5', '3', '3', '2', '4', '2', '9', '2', '6', '4', '0', '4', '6', '4', '1', '8', '9', '6', '5', '1', '0', '2', '5', '7', '4', '3', '7', '9', '1', '6', '1', '9', '7', '4', '6', '3', '5', '4', '4', '6', '1', '1', '1', '8', '3', '2', '3', '8', '8', '4', '2', '3', '1', '5', '3', '9', '9', '1', '2', '6', '2', '1', '9', '3', '7', '7', '4', '6', '8', '8', '3', '1', '3', '7', '7', '7', '0', '3', '3', '1', '6', '9', '3', '3', '3', '8', '2', '0', '9', '9', '4', '9', '9', '0', '4', '7', '3', '4', '3', '3', '3', '6', '2', '2', '8', '4', '1', '8', '7', '9', '6', '8', '6', '1', '3', '7', '2', '5', '0', '9', '9', '4', '9', '1', '4', '9', '6', '4', '6', '7', '6', '1', '0', '3', '2', '5', '0', '5', '8', '9', '1', '3', '5', '7', '7', '9', '7', '9', '4', '6', '5', '8', '5', '4', '5', '1', '3', '9', '9', '7', '8', '3', '2', '9', '9', '6', '7', '8', '8', '5', '3', '9', '2', '2', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '6', '0', '9', '3', '2', '4', '8', '2', '3', '4', '8', '7', '7', '2', '5', '4', '0', '2', '0', '9', '6', '1', '4', '7', '4', '2', '5', '5', '5', '9', '8', '9', '1', '8', '0', '5', '1', '4', '5', '8', '2', '1', '8', '0', '6', '0', '8', '7', '5', '5', '9', '2', '0', '8', '6', '0', '3', '4', '5', '7', '7', '1', '3', '8', '2', '4', '8', '3', '9', '8', '6', '2', '5', '6', '8', '4', '3', '4', '0', '0', '6', '1', '1', '9', '5', '4', '5', '0', '6', '5', '9', '9', '7', '2', '3', '4', '4', '0', '5', '7', '3', '8', '0', '1', '0', '1', '3', '3', '1', '5', '4', '7', '1', '8', '4', '7', '4', '8', '2', '6', '0', '0', '5', '8', '5', '5', '6', '1', '0', '8', '8', '7', '9', '5', '3', '9', '9', '4', '6', '5', '8', '9', '2', '4', '9', '2', '3', '8', '9', '3', '6', '8', '1', '5', '8', '4', '2', '3', '9', '1', '8', '1', '0', '3', '9', '9', '6', '9', '7', '7', '2', '1', '9', '8', '7', '5', '1', '8', '9', '8', '0', '0', '7', '2', '0', '3', '3', '4', '2', '7', '6', '5', '8', '8', '1', '3', '2', '5', '1', '0', '9', '8', '2', '6', '0', '5', '8', '6', '9', '2', '4', '0', '7', '5', '3', '4', '2', '4', '0', '8', '2', '8', '1', '9', '3', '0', '6', '8', '9', '1', '7', '4', '9', '1', '9', '3', '"', ',']

theorem object_fragment0299497_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 465) (SourceJson.white (fragment0299497Field007Chars00 ++ tail)) fragment0299497Acc00700 =
      SourceJson.object (fuel + 464) (SourceJson.white tail) fragment0299497Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0299497_object_field_007"
  err.flush

noncomputable def fragment0299497Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0299497Field008Value00 : SourceJson := .str (String.ofList ['2', '8', '7', '1', '5', '5', '3', '8', '2', '0', '6', '5', '2', '7', '9', '1'])
noncomputable def fragment0299497Acc00900 : List (String × SourceJson) := (fragment0299497Field008Key00, fragment0299497Field008Value00) :: fragment0299497Acc00800
noncomputable def fragment0299497Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '8', '7', '1', '5', '5', '3', '8', '2', '0', '6', '5', '2', '7', '9', '1', '"', ',']

theorem object_fragment0299497_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 464) (SourceJson.white (fragment0299497Field008Chars00 ++ tail)) fragment0299497Acc00800 =
      SourceJson.object (fuel + 463) (SourceJson.white tail) fragment0299497Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0299497_object_field_008"
  err.flush

noncomputable def fragment0299497Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0299497Field009Value00 : SourceJson := .str (String.ofList ['8', '7', '4', '0', '6', '3', '2', '0', '6', '7', '3', '9', '0', '6', '6', '6'])
noncomputable def fragment0299497Acc01000 : List (String × SourceJson) := (fragment0299497Field009Key00, fragment0299497Field009Value00) :: fragment0299497Acc00900
noncomputable def fragment0299497Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '7', '4', '0', '6', '3', '2', '0', '6', '7', '3', '9', '0', '6', '6', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0299497_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 463) (SourceJson.white (fragment0299497Field009Chars00 ++ tail)) fragment0299497Acc00900 =
      .ok (.obj (fragment0299497Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0299497_object_field_009"
  err.flush

noncomputable def fragment0299497Chars : List Char := '{' :: (fragment0299497Field000Chars00 ++ fragment0299497Field001Chars00 ++ fragment0299497Field002Chars00 ++ fragment0299497Field003Chars00 ++ fragment0299497Field004Chars00 ++ fragment0299497Field005Chars00 ++ fragment0299497Field006Chars00 ++ fragment0299497Field007Chars00 ++ fragment0299497Field008Chars00 ++ fragment0299497Field009Chars00)
noncomputable def fragment0299497Value : SourceJson := .obj (fragment0299497Acc01000.reverse)

theorem value_fragment0299497 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 473) (fragment0299497Chars ++ tail) =
      .ok (fragment0299497Value, tail) := by
  have hinput : fragment0299497Chars ++ tail = '{' :: (fragment0299497Field000Chars00 ++ (fragment0299497Field001Chars00 ++ (fragment0299497Field002Chars00 ++ (fragment0299497Field003Chars00 ++ (fragment0299497Field004Chars00 ++ (fragment0299497Field005Chars00 ++ (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0299497Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 473) (fragment0299497Chars ++ tail) =
        SourceJson.value (fuel + 473) ('{' :: (fragment0299497Field000Chars00 ++ (fragment0299497Field001Chars00 ++ (fragment0299497Field002Chars00 ++ (fragment0299497Field003Chars00 ++ (fragment0299497Field004Chars00 ++ (fragment0299497Field005Chars00 ++ (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 473)) hinput
    _ = SourceJson.object (fuel + 472) (SourceJson.white (fragment0299497Field000Chars00 ++ (fragment0299497Field001Chars00 ++ (fragment0299497Field002Chars00 ++ (fragment0299497Field003Chars00 ++ (fragment0299497Field004Chars00 ++ (fragment0299497Field005Chars00 ++ (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail)))))))))))) fragment0299497Acc00000 := by rfl
    _ = SourceJson.object (fuel + 471) (SourceJson.white (fragment0299497Field001Chars00 ++ (fragment0299497Field002Chars00 ++ (fragment0299497Field003Chars00 ++ (fragment0299497Field004Chars00 ++ (fragment0299497Field005Chars00 ++ (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail))))))))))) fragment0299497Acc00100 := object_fragment0299497_field_000 fuel (fragment0299497Field001Chars00 ++ (fragment0299497Field002Chars00 ++ (fragment0299497Field003Chars00 ++ (fragment0299497Field004Chars00 ++ (fragment0299497Field005Chars00 ++ (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 470) (SourceJson.white (fragment0299497Field002Chars00 ++ (fragment0299497Field003Chars00 ++ (fragment0299497Field004Chars00 ++ (fragment0299497Field005Chars00 ++ (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail)))))))))) fragment0299497Acc00200 := object_fragment0299497_field_001 fuel (fragment0299497Field002Chars00 ++ (fragment0299497Field003Chars00 ++ (fragment0299497Field004Chars00 ++ (fragment0299497Field005Chars00 ++ (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 469) (SourceJson.white (fragment0299497Field003Chars00 ++ (fragment0299497Field004Chars00 ++ (fragment0299497Field005Chars00 ++ (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail))))))))) fragment0299497Acc00300 := object_fragment0299497_field_002 fuel (fragment0299497Field003Chars00 ++ (fragment0299497Field004Chars00 ++ (fragment0299497Field005Chars00 ++ (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 468) (SourceJson.white (fragment0299497Field004Chars00 ++ (fragment0299497Field005Chars00 ++ (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail)))))))) fragment0299497Acc00400 := object_fragment0299497_field_003 fuel (fragment0299497Field004Chars00 ++ (fragment0299497Field005Chars00 ++ (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 467) (SourceJson.white (fragment0299497Field005Chars00 ++ (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail))))))) fragment0299497Acc00500 := object_fragment0299497_field_004 fuel (fragment0299497Field005Chars00 ++ (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 466) (SourceJson.white (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail)))))) fragment0299497Acc00600 := object_fragment0299497_field_005 fuel (fragment0299497Field006Chars00 ++ (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 465) (SourceJson.white (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail))))) fragment0299497Acc00700 := object_fragment0299497_field_006 fuel (fragment0299497Field007Chars00 ++ (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 464) (SourceJson.white (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail)))) fragment0299497Acc00800 := object_fragment0299497_field_007 fuel (fragment0299497Field008Chars00 ++ (fragment0299497Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 463) (SourceJson.white (fragment0299497Field009Chars00 ++ (tail))) fragment0299497Acc00900 := object_fragment0299497_field_008 fuel (fragment0299497Field009Chars00 ++ (tail))
    _ = .ok (fragment0299497Value, tail) := object_fragment0299497_field_009 fuel (tail)

noncomputable def fragment0301614Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0301614Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0301614Field000Value00 : SourceJson := .number (String.ofList ['9', '4'])
noncomputable def fragment0301614Acc00100 : List (String × SourceJson) := (fragment0301614Field000Key00, fragment0301614Field000Value00) :: fragment0301614Acc00000
noncomputable def fragment0301614Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '4', ',']

theorem object_fragment0301614_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 409) (SourceJson.white (fragment0301614Field000Chars00 ++ tail)) fragment0301614Acc00000 =
      SourceJson.object (fuel + 408) (SourceJson.white tail) fragment0301614Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0301614_object_field_000"
  err.flush

noncomputable def fragment0301614Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0301614Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0301614Acc00200 : List (String × SourceJson) := (fragment0301614Field001Key00, fragment0301614Field001Value00) :: fragment0301614Acc00100
noncomputable def fragment0301614Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0301614_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 408) (SourceJson.white (fragment0301614Field001Chars00 ++ tail)) fragment0301614Acc00100 =
      SourceJson.object (fuel + 407) (SourceJson.white tail) fragment0301614Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0301614_object_field_001"
  err.flush

noncomputable def fragment0301614Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0301614Field002Value00 : SourceJson := .str (String.ofList ['2', '0', '4', '7', '4', '7', '8', '9', '3', '2', '8', '5', '0', '9', '9', '1', '7', '4', '5', '1', '1', '5', '7', '5', '7', '5', '3', '6', '4', '0', '6', '9', '4', '1', '1', '2', '1', '9', '4', '2', '9', '5', '4', '0', '9', '7', '/', '1', '8', '2', '7', '8', '3', '6', '2', '7', '9', '0', '2', '9', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0301614Acc00300 : List (String × SourceJson) := (fragment0301614Field002Key00, fragment0301614Field002Value00) :: fragment0301614Acc00200
noncomputable def fragment0301614Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '0', '4', '7', '4', '7', '8', '9', '3', '2', '8', '5', '0', '9', '9', '1', '7', '4', '5', '1', '1', '5', '7', '5', '7', '5', '3', '6', '4', '0', '6', '9', '4', '1', '1', '2', '1', '9', '4', '2', '9', '5', '4', '0', '9', '7', '/', '1', '8', '2', '7', '8', '3', '6', '2', '7', '9', '0', '2', '9', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0301614_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 407) (SourceJson.white (fragment0301614Field002Chars00 ++ tail)) fragment0301614Acc00200 =
      SourceJson.object (fuel + 406) (SourceJson.white tail) fragment0301614Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0301614_object_field_002"
  err.flush

noncomputable def fragment0301614Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0301614Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0301614Acc00400 : List (String × SourceJson) := (fragment0301614Field003Key00, fragment0301614Field003Value00) :: fragment0301614Acc00300
noncomputable def fragment0301614Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0301614_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 406) (SourceJson.white (fragment0301614Field003Chars00 ++ tail)) fragment0301614Acc00300 =
      SourceJson.object (fuel + 405) (SourceJson.white tail) fragment0301614Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0301614_object_field_003"
  err.flush

noncomputable def fragment0301614Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0301614Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0301614Acc00500 : List (String × SourceJson) := (fragment0301614Field004Key00, fragment0301614Field004Value00) :: fragment0301614Acc00400
noncomputable def fragment0301614Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0301614_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 405) (SourceJson.white (fragment0301614Field004Chars00 ++ tail)) fragment0301614Acc00400 =
      SourceJson.object (fuel + 404) (SourceJson.white tail) fragment0301614Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0301614_object_field_004"
  err.flush

noncomputable def fragment0301614Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0301614Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '9', '1', '5', '2', '8', '1', '0', '0', '7', '9', '9', '4', '9', '0', '8', '0', '8', '0', '5', '5', '3', '/', '2', '1', '7', '5', '4', '4', '4', '0', '1', '0', '4', '0', '5', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '9', '9', '0', '5', '6', '9', '6', '3', '6', '2', '5', '9', '5', '5', '8', '3', '7', '6', '6', '3', '/', '1', '5', '5', '3', '8', '8', '8', '5', '7', '8', '8', '6', '1', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '3', '1', '7', '8', '5', '1', '4', '0', '5', '5', '1', '3', '2', '1', '8', '7', '1', '3', '3', '/', '1', '0', '5', '0', '9', '3', '9', '1', '3', '5', '4', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '6', '8', '6', '3', '7', '0', '2', '1', '3', '7', '1', '9', '3', '7', '5', '1', '0', '2', '3', '0', '1', '/', '2', '1', '7', '5', '4', '4', '4', '0', '1', '0', '4', '0', '5', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '2', '0', '9', '9', '4', '5', '1', '2', '8', '3', '2', '2', '8', '1', '0', '1', '1', '0', '5', '3', '7', '/', '2', '1', '7', '5', '4', '4', '4', '0', '1', '0', '4', '0', '5', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '3', '4', '7', '3', '7', '0', '4', '0', '6', '7', '6', '2', '7', '5', '9', '4', '9', '9', '/', '4', '3', '9', '4', '8', '3', '6', '3', '8', '4', '6', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '8', '3', '5', '2', '3', '3', '7', '8', '5', '4', '1', '5', '5', '5', '3', '8', '9', '1', '/', '1', '9', '7', '7', '6', '7', '6', '3', '7', '3', '0', '9', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '4', '7', '4', '9', '4', '6', '2', '6', '6', '7', '6', '3', '1', '7', '9', '1', '1', '9', '/', '1', '9', '7', '7', '6', '7', '6', '3', '7', '3', '0', '9', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '4', '0', '0', '1', '1', '6', '4', '1', '8', '5', '5', '4', '8', '9', '4', '7', '8', '3', '/', '1', '9', '7', '7', '6', '7', '6', '3', '7', '3', '0', '9', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '7', '1', '4', '2', '2', '9', '3', '2', '9', '4', '5', '4', '7', '8', '9', '8', '5', '8', '1', '/', '1', '5', '5', '3', '8', '8', '8', '5', '7', '8', '8', '6', '1', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0301614Acc00600 : List (String × SourceJson) := (fragment0301614Field005Key00, fragment0301614Field005Value00) :: fragment0301614Acc00500
noncomputable def fragment0301614Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '1', '5', '2', '8', '1', '0', '0', '7', '9', '9', '4', '9', '0', '8', '0', '8', '0', '5', '5', '3', '/', '2', '1', '7', '5', '4', '4', '4', '0', '1', '0', '4', '0', '5', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '9', '0', '5', '6', '9', '6', '3', '6', '2', '5', '9', '5', '5', '8', '3', '7', '6', '6', '3', '/', '1', '5', '5', '3', '8', '8', '8', '5', '7', '8', '8', '6', '1', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '3', '1', '7', '8', '5', '1', '4', '0', '5', '5', '1', '3', '2', '1', '8', '7', '1', '3', '3', '/', '1', '0', '5', '0', '9', '3', '9', '1', '3', '5', '4', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '6', '8', '6', '3', '7', '0', '2', '1', '3', '7', '1', '9', '3', '7', '5', '1', '0', '2', '3', '0', '1', '/', '2', '1', '7', '5', '4', '4', '4', '0', '1', '0', '4', '0', '5', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '0', '9', '9', '4', '5', '1', '2', '8', '3', '2', '2', '8', '1', '0', '1', '1', '0', '5', '3', '7', '/', '2', '1', '7', '5', '4', '4', '4', '0', '1', '0', '4', '0', '5', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '3', '4', '7', '3', '7', '0', '4', '0', '6', '7', '6', '2', '7', '5', '9', '4', '9', '9', '/', '4', '3', '9', '4', '8', '3', '6', '3', '8', '4', '6', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '8', '3', '5', '2', '3', '3', '7', '8', '5', '4', '1', '5', '5', '5', '3', '8', '9', '1', '/', '1', '9', '7', '7', '6', '7', '6', '3', '7', '3', '0', '9', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '4', '7', '4', '9', '4', '6', '2', '6', '6', '7', '6', '3', '1', '7', '9', '1', '1', '9', '/', '1', '9', '7', '7', '6', '7', '6', '3', '7', '3', '0', '9', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '4', '0', '0', '1', '1', '6', '4', '1', '8', '5', '5', '4', '8', '9', '4', '7', '8', '3', '/', '1', '9', '7', '7', '6', '7', '6', '3', '7', '3', '0', '9', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '7', '1', '4', '2', '2', '9', '3', '2', '9', '4', '5', '4', '7', '8', '9', '8', '5', '8', '1', '/', '1', '5', '5', '3', '8', '8', '8', '5', '7', '8', '8', '6', '1', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0301614_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 404) (SourceJson.white (fragment0301614Field005Chars00 ++ tail)) fragment0301614Acc00500 =
      SourceJson.object (fuel + 403) (SourceJson.white tail) fragment0301614Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0301614_object_field_005"
  err.flush

noncomputable def fragment0301614Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0301614Field006Value00 : SourceJson := .str (String.ofList ['2', '5', '5', '1', '6', '6', '7', '0', '1', '3', '4', '4', '3', '5', '7', '4', '9', '2', '8', '2', '9', '1', '1', '6', '5', '8', '1', '3', '6', '1', '6', '8', '2', '9', '1', '9', '6', '7', '7', '0', '5', '5', '2', '8', '2', '8', '1', '8', '4', '6', '6', '3', '0', '4', '0', '0', '/', '1', '1', '6', '6', '8', '3', '3', '4', '0', '7', '6', '1', '2', '2', '7', '9', '7', '8', '3', '8', '3', '1', '3', '2', '9', '8', '7', '7', '3', '5', '1', '2', '6', '2', '0', '1', '7', '2', '1', '3', '8', '5', '3', '2', '9', '9', '4', '1', '2', '4', '8', '7', '3', '3', '2', '1', '1', '0', '7', '8', '4', '7', '2', '9', '1', '1', '4', '5', '3'])
noncomputable def fragment0301614Acc00700 : List (String × SourceJson) := (fragment0301614Field006Key00, fragment0301614Field006Value00) :: fragment0301614Acc00600
noncomputable def fragment0301614Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '5', '5', '1', '6', '6', '7', '0', '1', '3', '4', '4', '3', '5', '7', '4', '9', '2', '8', '2', '9', '1', '1', '6', '5', '8', '1', '3', '6', '1', '6', '8', '2', '9', '1', '9', '6', '7', '7', '0', '5', '5', '2', '8', '2', '8', '1', '8', '4', '6', '6', '3', '0', '4', '0', '0', '/', '1', '1', '6', '6', '8', '3', '3', '4', '0', '7', '6', '1', '2', '2', '7', '9', '7', '8', '3', '8', '3', '1', '3', '2', '9', '8', '7', '7', '3', '5', '1', '2', '6', '2', '0', '1', '7', '2', '1', '3', '8', '5', '3', '2', '9', '9', '4', '1', '2', '4', '8', '7', '3', '3', '2', '1', '1', '0', '7', '8', '4', '7', '2', '9', '1', '1', '4', '5', '3', '"', ',']

theorem object_fragment0301614_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 403) (SourceJson.white (fragment0301614Field006Chars00 ++ tail)) fragment0301614Acc00600 =
      SourceJson.object (fuel + 402) (SourceJson.white tail) fragment0301614Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0301614_object_field_006"
  err.flush

noncomputable def fragment0301614Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0301614Field007Value00 : SourceJson := .str (String.ofList ['1', '7', '2', '4', '4', '3', '0', '9', '6', '9', '8', '9', '4', '2', '9', '0', '2', '7', '9', '2', '5', '9', '1', '8', '8', '1', '7', '4', '3', '3', '5', '5', '5', '4', '5', '6', '0', '5', '3', '6', '8', '7', '9', '0', '4', '1', '0', '9', '7', '9', '0', '1', '2', '1', '6', '5', '6', '3', '0', '5', '4', '8', '5', '1', '4', '2', '5', '4', '5', '5', '1', '7', '3', '4', '0', '5', '9', '7', '4', '7', '2', '1', '0', '7', '6', '3', '9', '9', '5', '8', '9', '9', '0', '5', '7', '7', '4', '9', '4', '2', '6', '6', '6', '4', '9', '9', '7', '4', '7', '1', '8', '7', '2', '2', '5', '3', '4', '1', '4', '5', '8', '6', '6', '2', '4', '8', '0', '7', '7', '5', '8', '0', '2', '6', '5', '1', '5', '4', '5', '2', '6', '2', '4', '1', '8', '6', '6', '5', '6', '8', '7', '1', '7', '2', '4', '3', '1', '7', '4', '8', '5', '3', '9', '6', '8', '4', '0', '5', '5', '7', '3', '1', '4', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '8', '2', '3', '2', '9', '5', '9', '0', '3', '9', '2', '0', '2', '7', '1', '9', '0', '1', '9', '5', '8', '8', '6', '7', '9', '2', '5', '5', '1', '8', '9', '9', '7', '3', '8', '2', '8', '8', '2', '2', '7', '6', '9', '2', '1', '8', '4', '0', '3', '9', '5', '2', '8', '7', '9', '5', '3', '2', '8', '2', '5', '3', '5', '4', '7', '3', '2', '7', '7', '7', '7', '6', '3', '4', '6', '3', '9', '3', '2', '3', '2', '8', '9', '9', '2', '7', '2', '2', '9', '8', '5', '2', '5', '8', '6', '2', '1', '6', '3', '0', '4', '5', '0', '8', '5', '7', '1', '3', '5', '4', '7', '5', '7', '8', '3', '3', '0', '1', '2', '0', '8', '7', '2', '7', '0', '4', '7', '3', '6', '6', '3', '5', '5', '6', '4', '0', '9', '6', '3', '6', '7', '4', '4', '7', '3', '1', '2', '9', '4', '2', '9', '4', '9', '2', '3', '3', '4', '1', '0', '6', '7', '5', '6', '1', '4', '3', '8', '5', '3', '4', '2', '7', '9', '1', '2', '9', '0', '9', '6', '2', '4', '4', '9', '3', '0', '9', '9', '7', '8', '9', '1', '1', '7', '4', '9', '0', '0', '2', '5', '3', '0', '4', '7'])
noncomputable def fragment0301614Acc00800 : List (String × SourceJson) := (fragment0301614Field007Key00, fragment0301614Field007Value00) :: fragment0301614Acc00700
noncomputable def fragment0301614Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '7', '2', '4', '4', '3', '0', '9', '6', '9', '8', '9', '4', '2', '9', '0', '2', '7', '9', '2', '5', '9', '1', '8', '8', '1', '7', '4', '3', '3', '5', '5', '5', '4', '5', '6', '0', '5', '3', '6', '8', '7', '9', '0', '4', '1', '0', '9', '7', '9', '0', '1', '2', '1', '6', '5', '6', '3', '0', '5', '4', '8', '5', '1', '4', '2', '5', '4', '5', '5', '1', '7', '3', '4', '0', '5', '9', '7', '4', '7', '2', '1', '0', '7', '6', '3', '9', '9', '5', '8', '9', '9', '0', '5', '7', '7', '4', '9', '4', '2', '6', '6', '6', '4', '9', '9', '7', '4', '7', '1', '8', '7', '2', '2', '5', '3', '4', '1', '4', '5', '8', '6', '6', '2', '4', '8', '0', '7', '7', '5', '8', '0', '2', '6', '5', '1', '5', '4', '5', '2', '6', '2', '4', '1', '8', '6', '6', '5', '6', '8', '7', '1', '7', '2', '4', '3', '1', '7', '4', '8', '5', '3', '9', '6', '8', '4', '0', '5', '5', '7', '3', '1', '4', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '8', '2', '3', '2', '9', '5', '9', '0', '3', '9', '2', '0', '2', '7', '1', '9', '0', '1', '9', '5', '8', '8', '6', '7', '9', '2', '5', '5', '1', '8', '9', '9', '7', '3', '8', '2', '8', '8', '2', '2', '7', '6', '9', '2', '1', '8', '4', '0', '3', '9', '5', '2', '8', '7', '9', '5', '3', '2', '8', '2', '5', '3', '5', '4', '7', '3', '2', '7', '7', '7', '7', '6', '3', '4', '6', '3', '9', '3', '2', '3', '2', '8', '9', '9', '2', '7', '2', '2', '9', '8', '5', '2', '5', '8', '6', '2', '1', '6', '3', '0', '4', '5', '0', '8', '5', '7', '1', '3', '5', '4', '7', '5', '7', '8', '3', '3', '0', '1', '2', '0', '8', '7', '2', '7', '0', '4', '7', '3', '6', '6', '3', '5', '5', '6', '4', '0', '9', '6', '3', '6', '7', '4', '4', '7', '3', '1', '2', '9', '4', '2', '9', '4', '9', '2', '3', '3', '4', '1', '0', '6', '7', '5', '6', '1', '4', '3', '8', '5', '3', '4', '2', '7', '9', '1', '2', '9', '0', '9', '6', '2', '4', '4', '9', '3', '0', '9', '9', '7', '8', '9', '1', '1', '7', '4', '9', '0', '0', '2', '5', '3', '0', '4', '7', '"', ',']

theorem object_fragment0301614_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 402) (SourceJson.white (fragment0301614Field007Chars00 ++ tail)) fragment0301614Acc00700 =
      SourceJson.object (fuel + 401) (SourceJson.white tail) fragment0301614Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0301614_object_field_007"
  err.flush

noncomputable def fragment0301614Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0301614Field008Value00 : SourceJson := .str (String.ofList ['1', '7', '3', '2', '5', '8', '5', '7', '1', '0', '2', '1', '7', '9', '4', '8', '5'])
noncomputable def fragment0301614Acc00900 : List (String × SourceJson) := (fragment0301614Field008Key00, fragment0301614Field008Value00) :: fragment0301614Acc00800
noncomputable def fragment0301614Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '3', '2', '5', '8', '5', '7', '1', '0', '2', '1', '7', '9', '4', '8', '5', '"', ',']

theorem object_fragment0301614_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 401) (SourceJson.white (fragment0301614Field008Chars00 ++ tail)) fragment0301614Acc00800 =
      SourceJson.object (fuel + 400) (SourceJson.white tail) fragment0301614Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0301614_object_field_008"
  err.flush

noncomputable def fragment0301614Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0301614Field009Value00 : SourceJson := .str (String.ofList ['6', '8', '9', '2', '0', '6', '7', '6', '8', '5', '8', '9', '8', '6', '1', '6', '0'])
noncomputable def fragment0301614Acc01000 : List (String × SourceJson) := (fragment0301614Field009Key00, fragment0301614Field009Value00) :: fragment0301614Acc00900
noncomputable def fragment0301614Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '8', '9', '2', '0', '6', '7', '6', '8', '5', '8', '9', '8', '6', '1', '6', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0301614_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0301614Field009Chars00 ++ tail)) fragment0301614Acc00900 =
      .ok (.obj (fragment0301614Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0301614_object_field_009"
  err.flush

noncomputable def fragment0301614Chars : List Char := '{' :: (fragment0301614Field000Chars00 ++ fragment0301614Field001Chars00 ++ fragment0301614Field002Chars00 ++ fragment0301614Field003Chars00 ++ fragment0301614Field004Chars00 ++ fragment0301614Field005Chars00 ++ fragment0301614Field006Chars00 ++ fragment0301614Field007Chars00 ++ fragment0301614Field008Chars00 ++ fragment0301614Field009Chars00)
noncomputable def fragment0301614Value : SourceJson := .obj (fragment0301614Acc01000.reverse)

theorem value_fragment0301614 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 410) (fragment0301614Chars ++ tail) =
      .ok (fragment0301614Value, tail) := by
  have hinput : fragment0301614Chars ++ tail = '{' :: (fragment0301614Field000Chars00 ++ (fragment0301614Field001Chars00 ++ (fragment0301614Field002Chars00 ++ (fragment0301614Field003Chars00 ++ (fragment0301614Field004Chars00 ++ (fragment0301614Field005Chars00 ++ (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0301614Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 410) (fragment0301614Chars ++ tail) =
        SourceJson.value (fuel + 410) ('{' :: (fragment0301614Field000Chars00 ++ (fragment0301614Field001Chars00 ++ (fragment0301614Field002Chars00 ++ (fragment0301614Field003Chars00 ++ (fragment0301614Field004Chars00 ++ (fragment0301614Field005Chars00 ++ (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 410)) hinput
    _ = SourceJson.object (fuel + 409) (SourceJson.white (fragment0301614Field000Chars00 ++ (fragment0301614Field001Chars00 ++ (fragment0301614Field002Chars00 ++ (fragment0301614Field003Chars00 ++ (fragment0301614Field004Chars00 ++ (fragment0301614Field005Chars00 ++ (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail)))))))))))) fragment0301614Acc00000 := by rfl
    _ = SourceJson.object (fuel + 408) (SourceJson.white (fragment0301614Field001Chars00 ++ (fragment0301614Field002Chars00 ++ (fragment0301614Field003Chars00 ++ (fragment0301614Field004Chars00 ++ (fragment0301614Field005Chars00 ++ (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail))))))))))) fragment0301614Acc00100 := object_fragment0301614_field_000 fuel (fragment0301614Field001Chars00 ++ (fragment0301614Field002Chars00 ++ (fragment0301614Field003Chars00 ++ (fragment0301614Field004Chars00 ++ (fragment0301614Field005Chars00 ++ (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 407) (SourceJson.white (fragment0301614Field002Chars00 ++ (fragment0301614Field003Chars00 ++ (fragment0301614Field004Chars00 ++ (fragment0301614Field005Chars00 ++ (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail)))))))))) fragment0301614Acc00200 := object_fragment0301614_field_001 fuel (fragment0301614Field002Chars00 ++ (fragment0301614Field003Chars00 ++ (fragment0301614Field004Chars00 ++ (fragment0301614Field005Chars00 ++ (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 406) (SourceJson.white (fragment0301614Field003Chars00 ++ (fragment0301614Field004Chars00 ++ (fragment0301614Field005Chars00 ++ (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail))))))))) fragment0301614Acc00300 := object_fragment0301614_field_002 fuel (fragment0301614Field003Chars00 ++ (fragment0301614Field004Chars00 ++ (fragment0301614Field005Chars00 ++ (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 405) (SourceJson.white (fragment0301614Field004Chars00 ++ (fragment0301614Field005Chars00 ++ (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail)))))))) fragment0301614Acc00400 := object_fragment0301614_field_003 fuel (fragment0301614Field004Chars00 ++ (fragment0301614Field005Chars00 ++ (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 404) (SourceJson.white (fragment0301614Field005Chars00 ++ (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail))))))) fragment0301614Acc00500 := object_fragment0301614_field_004 fuel (fragment0301614Field005Chars00 ++ (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 403) (SourceJson.white (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail)))))) fragment0301614Acc00600 := object_fragment0301614_field_005 fuel (fragment0301614Field006Chars00 ++ (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 402) (SourceJson.white (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail))))) fragment0301614Acc00700 := object_fragment0301614_field_006 fuel (fragment0301614Field007Chars00 ++ (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 401) (SourceJson.white (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail)))) fragment0301614Acc00800 := object_fragment0301614_field_007 fuel (fragment0301614Field008Chars00 ++ (fragment0301614Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0301614Field009Chars00 ++ (tail))) fragment0301614Acc00900 := object_fragment0301614_field_008 fuel (fragment0301614Field009Chars00 ++ (tail))
    _ = .ok (fragment0301614Value, tail) := object_fragment0301614_field_009 fuel (tail)

noncomputable def fragment0303596Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0303596Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0303596Field000Value00 : SourceJson := .number (String.ofList ['9', '5'])
noncomputable def fragment0303596Acc00100 : List (String × SourceJson) := (fragment0303596Field000Key00, fragment0303596Field000Value00) :: fragment0303596Acc00000
noncomputable def fragment0303596Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '5', ',']

theorem object_fragment0303596_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0303596Field000Chars00 ++ tail)) fragment0303596Acc00000 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0303596Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303596_object_field_000"
  err.flush

noncomputable def fragment0303596Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0303596Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0303596Acc00200 : List (String × SourceJson) := (fragment0303596Field001Key00, fragment0303596Field001Value00) :: fragment0303596Acc00100
noncomputable def fragment0303596Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0303596_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0303596Field001Chars00 ++ tail)) fragment0303596Acc00100 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0303596Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303596_object_field_001"
  err.flush

noncomputable def fragment0303596Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0303596Field002Value00 : SourceJson := .str (String.ofList ['4', '5', '3', '0', '8', '3', '2', '3', '4', '3', '8', '9', '1', '1', '2', '2', '1', '9', '8', '3', '4', '6', '5', '9', '1', '3', '9', '6', '9', '3', '8', '9', '1', '1', '4', '6', '1', '9', '6', '4', '1', '0', '5', '7', '1', '1', '7', '/', '4', '0', '2', '8', '7', '0', '0', '3', '7', '0', '1', '0', '5', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0303596Acc00300 : List (String × SourceJson) := (fragment0303596Field002Key00, fragment0303596Field002Value00) :: fragment0303596Acc00200
noncomputable def fragment0303596Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '5', '3', '0', '8', '3', '2', '3', '4', '3', '8', '9', '1', '1', '2', '2', '1', '9', '8', '3', '4', '6', '5', '9', '1', '3', '9', '6', '9', '3', '8', '9', '1', '1', '4', '6', '1', '9', '6', '4', '1', '0', '5', '7', '1', '1', '7', '/', '4', '0', '2', '8', '7', '0', '0', '3', '7', '0', '1', '0', '5', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0303596_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0303596Field002Chars00 ++ tail)) fragment0303596Acc00200 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0303596Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303596_object_field_002"
  err.flush

noncomputable def fragment0303596Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0303596Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0303596Acc00400 : List (String × SourceJson) := (fragment0303596Field003Key00, fragment0303596Field003Value00) :: fragment0303596Acc00300
noncomputable def fragment0303596Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0303596_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0303596Field003Chars00 ++ tail)) fragment0303596Acc00300 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0303596Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303596_object_field_003"
  err.flush

noncomputable def fragment0303596Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0303596Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0303596Acc00500 : List (String × SourceJson) := (fragment0303596Field004Key00, fragment0303596Field004Value00) :: fragment0303596Acc00400
noncomputable def fragment0303596Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0303596_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0303596Field004Chars00 ++ tail)) fragment0303596Acc00400 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0303596Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303596_object_field_004"
  err.flush

noncomputable def fragment0303596Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0303596Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '8', '9', '3', '4', '6', '1', '5', '6', '2', '5', '9', '9', '/', '2', '1', '6', '7', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '6', '1', '0', '4', '6', '3', '0', '8', '3', '6', '8', '7', '/', '1', '0', '8', '3', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '2', '0', '2', '5', '5', '3', '7', '5', '3', '7', '7', '/', '2', '8', '2', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '4', '1', '2', '5', '4', '4', '8', '7', '3', '9', '6', '1', '/', '6', '5', '0', '3', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '9', '8', '8', '3', '5', '4', '8', '3', '4', '9', '9', '7', '/', '6', '5', '0', '3', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '3', '5', '9', '2', '0', '2', '2', '5', '8', '3', '/', '1', '1', '8', '2', '3', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '9', '0', '0', '4', '7', '5', '9', '4', '1', '/', '8', '4', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '1', '7', '5', '7', '7', '6', '7', '0', '6', '9', '/', '5', '9', '1', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '8', '5', '4', '4', '7', '4', '9', '9', '3', '3', '/', '5', '9', '1', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '3', '6', '2', '4', '6', '3', '1', '5', '2', '0', '7', '/', '3', '2', '5', '1', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0303596Acc00600 : List (String × SourceJson) := (fragment0303596Field005Key00, fragment0303596Field005Value00) :: fragment0303596Acc00500
noncomputable def fragment0303596Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '3', '4', '6', '1', '5', '6', '2', '5', '9', '9', '/', '2', '1', '6', '7', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '1', '0', '4', '6', '3', '0', '8', '3', '6', '8', '7', '/', '1', '0', '8', '3', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '0', '2', '5', '5', '3', '7', '5', '3', '7', '7', '/', '2', '8', '2', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '4', '1', '2', '5', '4', '4', '8', '7', '3', '9', '6', '1', '/', '6', '5', '0', '3', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '9', '8', '8', '3', '5', '4', '8', '3', '4', '9', '9', '7', '/', '6', '5', '0', '3', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '3', '5', '9', '2', '0', '2', '2', '5', '8', '3', '/', '1', '1', '8', '2', '3', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '9', '0', '0', '4', '7', '5', '9', '4', '1', '/', '8', '4', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '1', '7', '5', '7', '7', '6', '7', '0', '6', '9', '/', '5', '9', '1', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '5', '4', '4', '7', '4', '9', '9', '3', '3', '/', '5', '9', '1', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '3', '6', '2', '4', '6', '3', '1', '5', '2', '0', '7', '/', '3', '2', '5', '1', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0303596_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0303596Field005Chars00 ++ tail)) fragment0303596Acc00500 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0303596Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303596_object_field_005"
  err.flush

noncomputable def fragment0303596Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0303596Field006Value00 : SourceJson := .str (String.ofList ['1', '6', '8', '5', '1', '8', '6', '6', '1', '8', '0', '1', '5', '9', '6', '8', '6', '4', '2', '7', '2', '7', '9', '3', '4', '4', '7', '8', '1', '7', '6', '2', '5', '6', '6', '7', '1', '6', '8', '5', '0', '8', '7', '1', '9', '8', '8', '5', '3', '2', '2', '4', '3', '7', '1', '2', '0', '0', '/', '1', '8', '4', '2', '9', '6', '6', '9', '3', '8', '7', '5', '8', '6', '4', '8', '8', '3', '2', '5', '5', '7', '1', '1', '5', '4', '9', '7', '2', '5', '2', '1', '7', '7', '9', '5', '4', '2', '2', '1', '2', '1', '9', '7', '8', '4', '3', '8', '8', '2', '0', '2', '2', '0', '9', '3', '8', '3', '4', '5', '2', '4', '2', '9', '9', '4', '8', '6', '4', '7'])
noncomputable def fragment0303596Acc00700 : List (String × SourceJson) := (fragment0303596Field006Key00, fragment0303596Field006Value00) :: fragment0303596Acc00600
noncomputable def fragment0303596Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '8', '5', '1', '8', '6', '6', '1', '8', '0', '1', '5', '9', '6', '8', '6', '4', '2', '7', '2', '7', '9', '3', '4', '4', '7', '8', '1', '7', '6', '2', '5', '6', '6', '7', '1', '6', '8', '5', '0', '8', '7', '1', '9', '8', '8', '5', '3', '2', '2', '4', '3', '7', '1', '2', '0', '0', '/', '1', '8', '4', '2', '9', '6', '6', '9', '3', '8', '7', '5', '8', '6', '4', '8', '8', '3', '2', '5', '5', '7', '1', '1', '5', '4', '9', '7', '2', '5', '2', '1', '7', '7', '9', '5', '4', '2', '2', '1', '2', '1', '9', '7', '8', '4', '3', '8', '8', '2', '0', '2', '2', '0', '9', '3', '8', '3', '4', '5', '2', '4', '2', '9', '9', '4', '8', '6', '4', '7', '"', ',']

theorem object_fragment0303596_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0303596Field006Chars00 ++ tail)) fragment0303596Acc00600 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0303596Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303596_object_field_006"
  err.flush

noncomputable def fragment0303596Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0303596Field007Value00 : SourceJson := .str (String.ofList ['1', '0', '5', '2', '4', '0', '0', '5', '9', '3', '8', '8', '6', '6', '1', '9', '8', '4', '2', '6', '0', '8', '8', '7', '5', '9', '2', '2', '0', '7', '5', '1', '8', '3', '3', '6', '1', '7', '4', '8', '2', '2', '9', '9', '1', '7', '5', '6', '2', '2', '2', '7', '3', '2', '3', '2', '8', '6', '6', '2', '9', '4', '7', '6', '7', '2', '5', '5', '4', '7', '6', '9', '2', '3', '9', '3', '8', '6', '3', '5', '0', '2', '0', '0', '2', '9', '0', '8', '5', '7', '5', '8', '2', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '4', '6', '2', '5', '2', '9', '8', '2', '0', '3', '0', '0', '6', '5', '4', '5', '2', '0', '5', '5', '5', '3', '4', '9', '2', '8', '1', '7', '1', '0', '9', '1', '3', '4', '7', '4', '5', '0', '6', '3', '5', '8', '3', '4', '6', '8', '6', '1', '1', '5', '9', '7', '5', '6', '6', '9', '7', '9', '9', '2', '8', '6', '2', '9', '2', '5', '0', '7', '5', '1', '7', '6', '7', '4', '3', '3', '1', '9', '0', '1', '4', '6', '1', '0', '6', '3', '0', '8', '5', '2', '5', '5', '5', '2', '1', '9', '6', '4', '1', '0', '1', '6', '6', '3', '3', '0', '6', '0', '0', '4', '4', '1', '8', '6', '0', '2', '7', '9', '8', '6', '0', '8', '9'])
noncomputable def fragment0303596Acc00800 : List (String × SourceJson) := (fragment0303596Field007Key00, fragment0303596Field007Value00) :: fragment0303596Acc00700
noncomputable def fragment0303596Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '5', '2', '4', '0', '0', '5', '9', '3', '8', '8', '6', '6', '1', '9', '8', '4', '2', '6', '0', '8', '8', '7', '5', '9', '2', '2', '0', '7', '5', '1', '8', '3', '3', '6', '1', '7', '4', '8', '2', '2', '9', '9', '1', '7', '5', '6', '2', '2', '2', '7', '3', '2', '3', '2', '8', '6', '6', '2', '9', '4', '7', '6', '7', '2', '5', '5', '4', '7', '6', '9', '2', '3', '9', '3', '8', '6', '3', '5', '0', '2', '0', '0', '2', '9', '0', '8', '5', '7', '5', '8', '2', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '4', '6', '2', '5', '2', '9', '8', '2', '0', '3', '0', '0', '6', '5', '4', '5', '2', '0', '5', '5', '5', '3', '4', '9', '2', '8', '1', '7', '1', '0', '9', '1', '3', '4', '7', '4', '5', '0', '6', '3', '5', '8', '3', '4', '6', '8', '6', '1', '1', '5', '9', '7', '5', '6', '6', '9', '7', '9', '9', '2', '8', '6', '2', '9', '2', '5', '0', '7', '5', '1', '7', '6', '7', '4', '3', '3', '1', '9', '0', '1', '4', '6', '1', '0', '6', '3', '0', '8', '5', '2', '5', '5', '5', '2', '1', '9', '6', '4', '1', '0', '1', '6', '6', '3', '3', '0', '6', '0', '0', '4', '4', '1', '8', '6', '0', '2', '7', '9', '8', '6', '0', '8', '9', '"', ',']

theorem object_fragment0303596_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0303596Field007Chars00 ++ tail)) fragment0303596Acc00700 =
      SourceJson.object (fuel + 240) (SourceJson.white tail) fragment0303596Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303596_object_field_007"
  err.flush

noncomputable def fragment0303596Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0303596Field008Value00 : SourceJson := .str (String.ofList ['7', '2', '4', '4', '5', '2', '7', '0', '9', '5', '4', '7', '5', '8', '7', '8', '8'])
noncomputable def fragment0303596Acc00900 : List (String × SourceJson) := (fragment0303596Field008Key00, fragment0303596Field008Value00) :: fragment0303596Acc00800
noncomputable def fragment0303596Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '2', '4', '4', '5', '2', '7', '0', '9', '5', '4', '7', '5', '8', '7', '8', '8', '"', ',']

theorem object_fragment0303596_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 240) (SourceJson.white (fragment0303596Field008Chars00 ++ tail)) fragment0303596Acc00800 =
      SourceJson.object (fuel + 239) (SourceJson.white tail) fragment0303596Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303596_object_field_008"
  err.flush

noncomputable def fragment0303596Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0303596Field009Value00 : SourceJson := .str (String.ofList ['3', '3', '8', '5', '9', '3', '9', '3', '1', '3', '1', '0', '7', '5', '8', '4', '6', '7'])
noncomputable def fragment0303596Acc01000 : List (String × SourceJson) := (fragment0303596Field009Key00, fragment0303596Field009Value00) :: fragment0303596Acc00900
noncomputable def fragment0303596Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '8', '5', '9', '3', '9', '3', '1', '3', '1', '0', '7', '5', '8', '4', '6', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0303596_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0303596Field009Chars00 ++ tail)) fragment0303596Acc00900 =
      .ok (.obj (fragment0303596Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303596_object_field_009"
  err.flush

noncomputable def fragment0303596Chars : List Char := '{' :: (fragment0303596Field000Chars00 ++ fragment0303596Field001Chars00 ++ fragment0303596Field002Chars00 ++ fragment0303596Field003Chars00 ++ fragment0303596Field004Chars00 ++ fragment0303596Field005Chars00 ++ fragment0303596Field006Chars00 ++ fragment0303596Field007Chars00 ++ fragment0303596Field008Chars00 ++ fragment0303596Field009Chars00)
noncomputable def fragment0303596Value : SourceJson := .obj (fragment0303596Acc01000.reverse)

theorem value_fragment0303596 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 249) (fragment0303596Chars ++ tail) =
      .ok (fragment0303596Value, tail) := by
  have hinput : fragment0303596Chars ++ tail = '{' :: (fragment0303596Field000Chars00 ++ (fragment0303596Field001Chars00 ++ (fragment0303596Field002Chars00 ++ (fragment0303596Field003Chars00 ++ (fragment0303596Field004Chars00 ++ (fragment0303596Field005Chars00 ++ (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0303596Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 249) (fragment0303596Chars ++ tail) =
        SourceJson.value (fuel + 249) ('{' :: (fragment0303596Field000Chars00 ++ (fragment0303596Field001Chars00 ++ (fragment0303596Field002Chars00 ++ (fragment0303596Field003Chars00 ++ (fragment0303596Field004Chars00 ++ (fragment0303596Field005Chars00 ++ (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 249)) hinput
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0303596Field000Chars00 ++ (fragment0303596Field001Chars00 ++ (fragment0303596Field002Chars00 ++ (fragment0303596Field003Chars00 ++ (fragment0303596Field004Chars00 ++ (fragment0303596Field005Chars00 ++ (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail)))))))))))) fragment0303596Acc00000 := by rfl
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0303596Field001Chars00 ++ (fragment0303596Field002Chars00 ++ (fragment0303596Field003Chars00 ++ (fragment0303596Field004Chars00 ++ (fragment0303596Field005Chars00 ++ (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail))))))))))) fragment0303596Acc00100 := object_fragment0303596_field_000 fuel (fragment0303596Field001Chars00 ++ (fragment0303596Field002Chars00 ++ (fragment0303596Field003Chars00 ++ (fragment0303596Field004Chars00 ++ (fragment0303596Field005Chars00 ++ (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0303596Field002Chars00 ++ (fragment0303596Field003Chars00 ++ (fragment0303596Field004Chars00 ++ (fragment0303596Field005Chars00 ++ (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail)))))))))) fragment0303596Acc00200 := object_fragment0303596_field_001 fuel (fragment0303596Field002Chars00 ++ (fragment0303596Field003Chars00 ++ (fragment0303596Field004Chars00 ++ (fragment0303596Field005Chars00 ++ (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0303596Field003Chars00 ++ (fragment0303596Field004Chars00 ++ (fragment0303596Field005Chars00 ++ (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail))))))))) fragment0303596Acc00300 := object_fragment0303596_field_002 fuel (fragment0303596Field003Chars00 ++ (fragment0303596Field004Chars00 ++ (fragment0303596Field005Chars00 ++ (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0303596Field004Chars00 ++ (fragment0303596Field005Chars00 ++ (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail)))))))) fragment0303596Acc00400 := object_fragment0303596_field_003 fuel (fragment0303596Field004Chars00 ++ (fragment0303596Field005Chars00 ++ (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0303596Field005Chars00 ++ (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail))))))) fragment0303596Acc00500 := object_fragment0303596_field_004 fuel (fragment0303596Field005Chars00 ++ (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail)))))) fragment0303596Acc00600 := object_fragment0303596_field_005 fuel (fragment0303596Field006Chars00 ++ (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail))))) fragment0303596Acc00700 := object_fragment0303596_field_006 fuel (fragment0303596Field007Chars00 ++ (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 240) (SourceJson.white (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail)))) fragment0303596Acc00800 := object_fragment0303596_field_007 fuel (fragment0303596Field008Chars00 ++ (fragment0303596Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0303596Field009Chars00 ++ (tail))) fragment0303596Acc00900 := object_fragment0303596_field_008 fuel (fragment0303596Field009Chars00 ++ (tail))
    _ = .ok (fragment0303596Value, tail) := object_fragment0303596_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0088_before_reader"
  err.flush

noncomputable def chunk0088LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0088SuffixChars00 : List Char := [',']
noncomputable def chunk0088Chars00 : List Char := chunk0088LeadChars00 ++ fragment0289765Chars ++ chunk0088SuffixChars00
noncomputable def chunk0088Push00 (acc : List SourceJson) : List SourceJson := fragment0289765Value :: acc

noncomputable def chunk0088AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0088_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 569)
      (SourceJson.white (chunk0088LeadChars00 ++ (fragment0289765Chars ++ rest))) acc =
      (SourceJson.value (fuel + 568) (fragment0289765Chars ++ rest)).bind
        (chunk0088AfterValue00 (fuel + 568) acc) := by rfl

theorem array_chunk0088 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 569) (SourceJson.white (chunk0088Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 568) (SourceJson.white tail) (chunk0088Push00 acc) := by
  have hinput : chunk0088Chars00 ++ tail = chunk0088LeadChars00 ++ (fragment0289765Chars ++ (chunk0088SuffixChars00 ++ tail)) := by
    simp only [chunk0088Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 569) (SourceJson.white (chunk0088Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 569)
          (SourceJson.white (chunk0088LeadChars00 ++ (fragment0289765Chars ++ (chunk0088SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 569) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 568) (fragment0289765Chars ++ (chunk0088SuffixChars00 ++ tail))).bind
        (chunk0088AfterValue00 (fuel + 568) acc) := array_chunk0088_head fuel (chunk0088SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0289765Value, chunk0088SuffixChars00 ++ tail)).bind
        (chunk0088AfterValue00 (fuel + 568) acc) :=
      congrArg (fun result => result.bind (chunk0088AfterValue00 (fuel + 568) acc))
        (value_fragment0289765 (fuel + 324) (chunk0088SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 568) (SourceJson.white tail) (chunk0088Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0088_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0089_before_reader"
  err.flush

noncomputable def chunk0089LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0089SuffixChars00 : List Char := [',']
noncomputable def chunk0089Chars00 : List Char := chunk0089LeadChars00 ++ fragment0291390Chars ++ chunk0089SuffixChars00
noncomputable def chunk0089Push00 (acc : List SourceJson) : List SourceJson := fragment0291390Value :: acc

noncomputable def chunk0089AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0089_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 568)
      (SourceJson.white (chunk0089LeadChars00 ++ (fragment0291390Chars ++ rest))) acc =
      (SourceJson.value (fuel + 567) (fragment0291390Chars ++ rest)).bind
        (chunk0089AfterValue00 (fuel + 567) acc) := by rfl

theorem array_chunk0089 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 568) (SourceJson.white (chunk0089Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 567) (SourceJson.white tail) (chunk0089Push00 acc) := by
  have hinput : chunk0089Chars00 ++ tail = chunk0089LeadChars00 ++ (fragment0291390Chars ++ (chunk0089SuffixChars00 ++ tail)) := by
    simp only [chunk0089Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 568) (SourceJson.white (chunk0089Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 568)
          (SourceJson.white (chunk0089LeadChars00 ++ (fragment0291390Chars ++ (chunk0089SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 568) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 567) (fragment0291390Chars ++ (chunk0089SuffixChars00 ++ tail))).bind
        (chunk0089AfterValue00 (fuel + 567) acc) := array_chunk0089_head fuel (chunk0089SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0291390Value, chunk0089SuffixChars00 ++ tail)).bind
        (chunk0089AfterValue00 (fuel + 567) acc) :=
      congrArg (fun result => result.bind (chunk0089AfterValue00 (fuel + 567) acc))
        (value_fragment0291390 (fuel + 120) (chunk0089SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 567) (SourceJson.white tail) (chunk0089Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0089_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0090_before_reader"
  err.flush

noncomputable def chunk0090LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0090SuffixChars00 : List Char := [',']
noncomputable def chunk0090Chars00 : List Char := chunk0090LeadChars00 ++ fragment0293440Chars ++ chunk0090SuffixChars00
noncomputable def chunk0090Push00 (acc : List SourceJson) : List SourceJson := fragment0293440Value :: acc

noncomputable def chunk0090AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0090_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 567)
      (SourceJson.white (chunk0090LeadChars00 ++ (fragment0293440Chars ++ rest))) acc =
      (SourceJson.value (fuel + 566) (fragment0293440Chars ++ rest)).bind
        (chunk0090AfterValue00 (fuel + 566) acc) := by rfl

theorem array_chunk0090 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 567) (SourceJson.white (chunk0090Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 566) (SourceJson.white tail) (chunk0090Push00 acc) := by
  have hinput : chunk0090Chars00 ++ tail = chunk0090LeadChars00 ++ (fragment0293440Chars ++ (chunk0090SuffixChars00 ++ tail)) := by
    simp only [chunk0090Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 567) (SourceJson.white (chunk0090Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 567)
          (SourceJson.white (chunk0090LeadChars00 ++ (fragment0293440Chars ++ (chunk0090SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 567) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 566) (fragment0293440Chars ++ (chunk0090SuffixChars00 ++ tail))).bind
        (chunk0090AfterValue00 (fuel + 566) acc) := array_chunk0090_head fuel (chunk0090SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0293440Value, chunk0090SuffixChars00 ++ tail)).bind
        (chunk0090AfterValue00 (fuel + 566) acc) :=
      congrArg (fun result => result.bind (chunk0090AfterValue00 (fuel + 566) acc))
        (value_fragment0293440 (fuel + 361) (chunk0090SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 566) (SourceJson.white tail) (chunk0090Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0090_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0091_before_reader"
  err.flush

noncomputable def chunk0091LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0091SuffixChars00 : List Char := [',']
noncomputable def chunk0091Chars00 : List Char := chunk0091LeadChars00 ++ fragment0294984Chars ++ chunk0091SuffixChars00
noncomputable def chunk0091Push00 (acc : List SourceJson) : List SourceJson := fragment0294984Value :: acc

noncomputable def chunk0091AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0091_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 566)
      (SourceJson.white (chunk0091LeadChars00 ++ (fragment0294984Chars ++ rest))) acc =
      (SourceJson.value (fuel + 565) (fragment0294984Chars ++ rest)).bind
        (chunk0091AfterValue00 (fuel + 565) acc) := by rfl

theorem array_chunk0091 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 566) (SourceJson.white (chunk0091Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 565) (SourceJson.white tail) (chunk0091Push00 acc) := by
  have hinput : chunk0091Chars00 ++ tail = chunk0091LeadChars00 ++ (fragment0294984Chars ++ (chunk0091SuffixChars00 ++ tail)) := by
    simp only [chunk0091Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 566) (SourceJson.white (chunk0091Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 566)
          (SourceJson.white (chunk0091LeadChars00 ++ (fragment0294984Chars ++ (chunk0091SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 566) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 565) (fragment0294984Chars ++ (chunk0091SuffixChars00 ++ tail))).bind
        (chunk0091AfterValue00 (fuel + 565) acc) := array_chunk0091_head fuel (chunk0091SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0294984Value, chunk0091SuffixChars00 ++ tail)).bind
        (chunk0091AfterValue00 (fuel + 565) acc) :=
      congrArg (fun result => result.bind (chunk0091AfterValue00 (fuel + 565) acc))
        (value_fragment0294984 (fuel + 0) (chunk0091SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 565) (SourceJson.white tail) (chunk0091Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0091_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0092_before_reader"
  err.flush

noncomputable def chunk0092LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0092SuffixChars00 : List Char := [',']
noncomputable def chunk0092Chars00 : List Char := chunk0092LeadChars00 ++ fragment0297291Chars ++ chunk0092SuffixChars00
noncomputable def chunk0092Push00 (acc : List SourceJson) : List SourceJson := fragment0297291Value :: acc

noncomputable def chunk0092AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0092_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 565)
      (SourceJson.white (chunk0092LeadChars00 ++ (fragment0297291Chars ++ rest))) acc =
      (SourceJson.value (fuel + 564) (fragment0297291Chars ++ rest)).bind
        (chunk0092AfterValue00 (fuel + 564) acc) := by rfl

theorem array_chunk0092 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 565) (SourceJson.white (chunk0092Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 564) (SourceJson.white tail) (chunk0092Push00 acc) := by
  have hinput : chunk0092Chars00 ++ tail = chunk0092LeadChars00 ++ (fragment0297291Chars ++ (chunk0092SuffixChars00 ++ tail)) := by
    simp only [chunk0092Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 565) (SourceJson.white (chunk0092Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 565)
          (SourceJson.white (chunk0092LeadChars00 ++ (fragment0297291Chars ++ (chunk0092SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 565) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 564) (fragment0297291Chars ++ (chunk0092SuffixChars00 ++ tail))).bind
        (chunk0092AfterValue00 (fuel + 564) acc) := array_chunk0092_head fuel (chunk0092SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0297291Value, chunk0092SuffixChars00 ++ tail)).bind
        (chunk0092AfterValue00 (fuel + 564) acc) :=
      congrArg (fun result => result.bind (chunk0092AfterValue00 (fuel + 564) acc))
        (value_fragment0297291 (fuel + 50) (chunk0092SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 564) (SourceJson.white tail) (chunk0092Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0092_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0093_before_reader"
  err.flush

noncomputable def chunk0093LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0093SuffixChars00 : List Char := [',']
noncomputable def chunk0093Chars00 : List Char := chunk0093LeadChars00 ++ fragment0299497Chars ++ chunk0093SuffixChars00
noncomputable def chunk0093Push00 (acc : List SourceJson) : List SourceJson := fragment0299497Value :: acc

noncomputable def chunk0093AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0093_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 564)
      (SourceJson.white (chunk0093LeadChars00 ++ (fragment0299497Chars ++ rest))) acc =
      (SourceJson.value (fuel + 563) (fragment0299497Chars ++ rest)).bind
        (chunk0093AfterValue00 (fuel + 563) acc) := by rfl

theorem array_chunk0093 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 564) (SourceJson.white (chunk0093Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 563) (SourceJson.white tail) (chunk0093Push00 acc) := by
  have hinput : chunk0093Chars00 ++ tail = chunk0093LeadChars00 ++ (fragment0299497Chars ++ (chunk0093SuffixChars00 ++ tail)) := by
    simp only [chunk0093Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 564) (SourceJson.white (chunk0093Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 564)
          (SourceJson.white (chunk0093LeadChars00 ++ (fragment0299497Chars ++ (chunk0093SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 564) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 563) (fragment0299497Chars ++ (chunk0093SuffixChars00 ++ tail))).bind
        (chunk0093AfterValue00 (fuel + 563) acc) := array_chunk0093_head fuel (chunk0093SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0299497Value, chunk0093SuffixChars00 ++ tail)).bind
        (chunk0093AfterValue00 (fuel + 563) acc) :=
      congrArg (fun result => result.bind (chunk0093AfterValue00 (fuel + 563) acc))
        (value_fragment0299497 (fuel + 90) (chunk0093SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 563) (SourceJson.white tail) (chunk0093Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0093_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0094_before_reader"
  err.flush

noncomputable def chunk0094LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0094SuffixChars00 : List Char := [',']
noncomputable def chunk0094Chars00 : List Char := chunk0094LeadChars00 ++ fragment0301614Chars ++ chunk0094SuffixChars00
noncomputable def chunk0094Push00 (acc : List SourceJson) : List SourceJson := fragment0301614Value :: acc

noncomputable def chunk0094AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0094_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 563)
      (SourceJson.white (chunk0094LeadChars00 ++ (fragment0301614Chars ++ rest))) acc =
      (SourceJson.value (fuel + 562) (fragment0301614Chars ++ rest)).bind
        (chunk0094AfterValue00 (fuel + 562) acc) := by rfl

theorem array_chunk0094 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 563) (SourceJson.white (chunk0094Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 562) (SourceJson.white tail) (chunk0094Push00 acc) := by
  have hinput : chunk0094Chars00 ++ tail = chunk0094LeadChars00 ++ (fragment0301614Chars ++ (chunk0094SuffixChars00 ++ tail)) := by
    simp only [chunk0094Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 563) (SourceJson.white (chunk0094Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 563)
          (SourceJson.white (chunk0094LeadChars00 ++ (fragment0301614Chars ++ (chunk0094SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 563) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 562) (fragment0301614Chars ++ (chunk0094SuffixChars00 ++ tail))).bind
        (chunk0094AfterValue00 (fuel + 562) acc) := array_chunk0094_head fuel (chunk0094SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0301614Value, chunk0094SuffixChars00 ++ tail)).bind
        (chunk0094AfterValue00 (fuel + 562) acc) :=
      congrArg (fun result => result.bind (chunk0094AfterValue00 (fuel + 562) acc))
        (value_fragment0301614 (fuel + 152) (chunk0094SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 562) (SourceJson.white tail) (chunk0094Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0094_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0095_before_reader"
  err.flush

noncomputable def chunk0095LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0095SuffixChars00 : List Char := [',']
noncomputable def chunk0095Chars00 : List Char := chunk0095LeadChars00 ++ fragment0303596Chars ++ chunk0095SuffixChars00
noncomputable def chunk0095Push00 (acc : List SourceJson) : List SourceJson := fragment0303596Value :: acc

noncomputable def chunk0095AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0095_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 562)
      (SourceJson.white (chunk0095LeadChars00 ++ (fragment0303596Chars ++ rest))) acc =
      (SourceJson.value (fuel + 561) (fragment0303596Chars ++ rest)).bind
        (chunk0095AfterValue00 (fuel + 561) acc) := by rfl

theorem array_chunk0095 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 562) (SourceJson.white (chunk0095Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 561) (SourceJson.white tail) (chunk0095Push00 acc) := by
  have hinput : chunk0095Chars00 ++ tail = chunk0095LeadChars00 ++ (fragment0303596Chars ++ (chunk0095SuffixChars00 ++ tail)) := by
    simp only [chunk0095Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 562) (SourceJson.white (chunk0095Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 562)
          (SourceJson.white (chunk0095LeadChars00 ++ (fragment0303596Chars ++ (chunk0095SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 562) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 561) (fragment0303596Chars ++ (chunk0095SuffixChars00 ++ tail))).bind
        (chunk0095AfterValue00 (fuel + 561) acc) := array_chunk0095_head fuel (chunk0095SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0303596Value, chunk0095SuffixChars00 ++ tail)).bind
        (chunk0095AfterValue00 (fuel + 561) acc) :=
      congrArg (fun result => result.bind (chunk0095AfterValue00 (fuel + 561) acc))
        (value_fragment0303596 (fuel + 312) (chunk0095SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 561) (SourceJson.white tail) (chunk0095Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0095_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0088Chars00 ++ chunk0089Chars00 ++ chunk0090Chars00 ++ chunk0091Chars00 ++ chunk0092Chars00 ++ chunk0093Chars00 ++ chunk0094Chars00 ++ chunk0095Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0095Push00 (chunk0094Push00 (chunk0093Push00 (chunk0092Push00 (chunk0091Push00 (chunk0090Push00 (chunk0089Push00 (chunk0088Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 569) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 561) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0088Chars00 ++ (chunk0089Chars00 ++ (chunk0090Chars00 ++ (chunk0091Chars00 ++ (chunk0092Chars00 ++ (chunk0093Chars00 ++ (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 569) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 569) (SourceJson.white (chunk0088Chars00 ++ (chunk0089Chars00 ++ (chunk0090Chars00 ++ (chunk0091Chars00 ++ (chunk0092Chars00 ++ (chunk0093Chars00 ++ (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 569) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 568) (SourceJson.white (chunk0089Chars00 ++ (chunk0090Chars00 ++ (chunk0091Chars00 ++ (chunk0092Chars00 ++ (chunk0093Chars00 ++ (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail))))))))) (chunk0088Push00 (acc)) := array_chunk0088 fuel (chunk0089Chars00 ++ (chunk0090Chars00 ++ (chunk0091Chars00 ++ (chunk0092Chars00 ++ (chunk0093Chars00 ++ (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 567) (SourceJson.white (chunk0090Chars00 ++ (chunk0091Chars00 ++ (chunk0092Chars00 ++ (chunk0093Chars00 ++ (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail)))))))) (chunk0089Push00 (chunk0088Push00 (acc))) := array_chunk0089 fuel (chunk0090Chars00 ++ (chunk0091Chars00 ++ (chunk0092Chars00 ++ (chunk0093Chars00 ++ (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail))))))) (chunk0088Push00 (acc))
    _ = SourceJson.array (fuel + 566) (SourceJson.white (chunk0091Chars00 ++ (chunk0092Chars00 ++ (chunk0093Chars00 ++ (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail))))))) (chunk0090Push00 (chunk0089Push00 (chunk0088Push00 (acc)))) := array_chunk0090 fuel (chunk0091Chars00 ++ (chunk0092Chars00 ++ (chunk0093Chars00 ++ (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail)))))) (chunk0089Push00 (chunk0088Push00 (acc)))
    _ = SourceJson.array (fuel + 565) (SourceJson.white (chunk0092Chars00 ++ (chunk0093Chars00 ++ (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail)))))) (chunk0091Push00 (chunk0090Push00 (chunk0089Push00 (chunk0088Push00 (acc))))) := array_chunk0091 fuel (chunk0092Chars00 ++ (chunk0093Chars00 ++ (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail))))) (chunk0090Push00 (chunk0089Push00 (chunk0088Push00 (acc))))
    _ = SourceJson.array (fuel + 564) (SourceJson.white (chunk0093Chars00 ++ (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail))))) (chunk0092Push00 (chunk0091Push00 (chunk0090Push00 (chunk0089Push00 (chunk0088Push00 (acc)))))) := array_chunk0092 fuel (chunk0093Chars00 ++ (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail)))) (chunk0091Push00 (chunk0090Push00 (chunk0089Push00 (chunk0088Push00 (acc)))))
    _ = SourceJson.array (fuel + 563) (SourceJson.white (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail)))) (chunk0093Push00 (chunk0092Push00 (chunk0091Push00 (chunk0090Push00 (chunk0089Push00 (chunk0088Push00 (acc))))))) := array_chunk0093 fuel (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail))) (chunk0092Push00 (chunk0091Push00 (chunk0090Push00 (chunk0089Push00 (chunk0088Push00 (acc))))))
    _ = SourceJson.array (fuel + 562) (SourceJson.white (chunk0095Chars00 ++ (tail))) (chunk0094Push00 (chunk0093Push00 (chunk0092Push00 (chunk0091Push00 (chunk0090Push00 (chunk0089Push00 (chunk0088Push00 (acc)))))))) := array_chunk0094 fuel (chunk0095Chars00 ++ (tail)) (chunk0093Push00 (chunk0092Push00 (chunk0091Push00 (chunk0090Push00 (chunk0089Push00 (chunk0088Push00 (acc)))))))
    _ = SourceJson.array (fuel + 561) (SourceJson.white tail) (blockPush acc) := array_chunk0095 fuel (tail) (chunk0094Push00 (chunk0093Push00 (chunk0092Push00 (chunk0091Push00 (chunk0090Push00 (chunk0089Push00 (chunk0088Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 289759).take 15489 = blockChars := by rfl

theorem block_original_split : sourceRest 289759 = blockChars ++ sourceRest 305248 := by
  calc
    sourceRest 289759 = (sourceRest 289759).take 15489 ++ (sourceRest 289759).drop 15489 :=
      (List.take_append_drop 15489 (sourceRest 289759)).symm
    _ = blockChars ++ (sourceRest 289759).drop 15489 :=
      congrArg (fun part => part ++ (sourceRest 289759).drop 15489) block_original_prefix
    _ = blockChars ++ sourceRest 305248 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 289759 15489)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 569) (SourceJson.white (sourceRest 289759)) acc =
      SourceJson.array (fuel + 561) (SourceJson.white (sourceRest 305248)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 569) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 305248) acc)

#print axioms object_fragment0289765_field_000
#print axioms object_fragment0289765_field_001
#print axioms object_fragment0289765_field_002
#print axioms object_fragment0289765_field_003
#print axioms object_fragment0289765_field_004
#print axioms object_fragment0289765_field_005
#print axioms object_fragment0289765_field_006
#print axioms object_fragment0289765_field_007
#print axioms object_fragment0289765_field_008
#print axioms object_fragment0289765_field_009
#print axioms value_fragment0289765
#print axioms object_fragment0291390_field_000
#print axioms object_fragment0291390_field_001
#print axioms object_fragment0291390_field_002
#print axioms object_fragment0291390_field_003
#print axioms object_fragment0291390_field_004
#print axioms object_fragment0291390_field_005
#print axioms object_fragment0291390_field_006
#print axioms object_fragment0291390_field_007
#print axioms object_fragment0291390_field_008
#print axioms object_fragment0291390_field_009
#print axioms value_fragment0291390
#print axioms object_fragment0293440_field_000
#print axioms object_fragment0293440_field_001
#print axioms object_fragment0293440_field_002
#print axioms object_fragment0293440_field_003
#print axioms object_fragment0293440_field_004
#print axioms object_fragment0293440_field_005
#print axioms object_fragment0293440_field_006
#print axioms object_fragment0293440_field_007
#print axioms object_fragment0293440_field_008
#print axioms object_fragment0293440_field_009
#print axioms value_fragment0293440
#print axioms object_fragment0294984_field_000
#print axioms object_fragment0294984_field_001
#print axioms object_fragment0294984_field_002
#print axioms object_fragment0294984_field_003
#print axioms object_fragment0294984_field_004
#print axioms object_fragment0294984_field_005
#print axioms object_fragment0294984_field_006
#print axioms object_fragment0294984_field_007
#print axioms object_fragment0294984_field_008
#print axioms object_fragment0294984_field_009
#print axioms value_fragment0294984
#print axioms object_fragment0297291_field_000
#print axioms object_fragment0297291_field_001
#print axioms object_fragment0297291_field_002
#print axioms object_fragment0297291_field_003
#print axioms object_fragment0297291_field_004
#print axioms object_fragment0297291_field_005
#print axioms object_fragment0297291_field_006
#print axioms object_fragment0297291_field_007
#print axioms object_fragment0297291_field_008
#print axioms object_fragment0297291_field_009
#print axioms value_fragment0297291
#print axioms object_fragment0299497_field_000
#print axioms object_fragment0299497_field_001
#print axioms object_fragment0299497_field_002
#print axioms object_fragment0299497_field_003
#print axioms object_fragment0299497_field_004
#print axioms object_fragment0299497_field_005
#print axioms object_fragment0299497_field_006
#print axioms object_fragment0299497_field_007
#print axioms object_fragment0299497_field_008
#print axioms object_fragment0299497_field_009
#print axioms value_fragment0299497
#print axioms object_fragment0301614_field_000
#print axioms object_fragment0301614_field_001
#print axioms object_fragment0301614_field_002
#print axioms object_fragment0301614_field_003
#print axioms object_fragment0301614_field_004
#print axioms object_fragment0301614_field_005
#print axioms object_fragment0301614_field_006
#print axioms object_fragment0301614_field_007
#print axioms object_fragment0301614_field_008
#print axioms object_fragment0301614_field_009
#print axioms value_fragment0301614
#print axioms object_fragment0303596_field_000
#print axioms object_fragment0303596_field_001
#print axioms object_fragment0303596_field_002
#print axioms object_fragment0303596_field_003
#print axioms object_fragment0303596_field_004
#print axioms object_fragment0303596_field_005
#print axioms object_fragment0303596_field_006
#print axioms object_fragment0303596_field_007
#print axioms object_fragment0303596_field_008
#print axioms object_fragment0303596_field_009
#print axioms value_fragment0303596
#print axioms array_chunk0088_head
#print axioms array_chunk0088
#print axioms array_chunk0089_head
#print axioms array_chunk0089
#print axioms array_chunk0090_head
#print axioms array_chunk0090
#print axioms array_chunk0091_head
#print axioms array_chunk0091
#print axioms array_chunk0092_head
#print axioms array_chunk0092
#print axioms array_chunk0093_head
#print axioms array_chunk0093
#print axioms array_chunk0094_head
#print axioms array_chunk0094
#print axioms array_chunk0095_head
#print axioms array_chunk0095
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock011

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
