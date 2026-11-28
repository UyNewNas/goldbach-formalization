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

namespace SimplicesBlock008

noncomputable def fragment0246486Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0246486Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0246486Field000Value00 : SourceJson := .number (String.ofList ['6', '4'])
noncomputable def fragment0246486Acc00100 : List (String × SourceJson) := (fragment0246486Field000Key00, fragment0246486Field000Value00) :: fragment0246486Acc00000
noncomputable def fragment0246486Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '4', ',']

theorem object_fragment0246486_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0246486Field000Chars00 ++ tail)) fragment0246486Acc00000 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0246486Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246486_object_field_000"
  err.flush

noncomputable def fragment0246486Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0246486Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0246486Acc00200 : List (String × SourceJson) := (fragment0246486Field001Key00, fragment0246486Field001Value00) :: fragment0246486Acc00100
noncomputable def fragment0246486Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0246486_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0246486Field001Chars00 ++ tail)) fragment0246486Acc00100 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0246486Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246486_object_field_001"
  err.flush

noncomputable def fragment0246486Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0246486Field002Value00 : SourceJson := .str (String.ofList ['2', '1', '3', '4', '4', '8', '9', '6', '8', '6', '1', '1', '6', '2', '2', '6', '5', '3', '8', '6', '6', '6', '0', '7', '3', '5', '4', '8', '5', '8', '3', '1', '4', '1', '2', '7', '/', '3', '9', '9', '5', '0', '2', '2', '9', '2', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0246486Acc00300 : List (String × SourceJson) := (fragment0246486Field002Key00, fragment0246486Field002Value00) :: fragment0246486Acc00200
noncomputable def fragment0246486Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '1', '3', '4', '4', '8', '9', '6', '8', '6', '1', '1', '6', '2', '2', '6', '5', '3', '8', '6', '6', '6', '0', '7', '3', '5', '4', '8', '5', '8', '3', '1', '4', '1', '2', '7', '/', '3', '9', '9', '5', '0', '2', '2', '9', '2', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0246486_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0246486Field002Chars00 ++ tail)) fragment0246486Acc00200 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0246486Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246486_object_field_002"
  err.flush

noncomputable def fragment0246486Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0246486Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0246486Acc00400 : List (String × SourceJson) := (fragment0246486Field003Key00, fragment0246486Field003Value00) :: fragment0246486Acc00300
noncomputable def fragment0246486Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0246486_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0246486Field003Chars00 ++ tail)) fragment0246486Acc00300 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0246486Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246486_object_field_003"
  err.flush

noncomputable def fragment0246486Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0246486Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0246486Acc00500 : List (String × SourceJson) := (fragment0246486Field004Key00, fragment0246486Field004Value00) :: fragment0246486Acc00400
noncomputable def fragment0246486Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0246486_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0246486Field004Chars00 ++ tail)) fragment0246486Acc00400 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0246486Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246486_object_field_004"
  err.flush

noncomputable def fragment0246486Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0246486Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '3', '2', '7', '3', '0', '9', '0', '0', '3', '9', '0', '7', '/', '1', '5', '2', '5', '5', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '0', '5', '4', '0', '4', '7', '0', '3', '9', '/', '2', '3', '8', '3', '7', '3', '4', '3', '7', '5', '0', '0']), .str (String.ofList ['1', '8', '9', '1', '1', '1', '0', '3', '1', '4', '5', '5', '7', '/', '1', '6', '0', '1', '8', '6', '9', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '5', '0', '7', '2', '3', '5', '6', '7', '6', '1', '6', '3', '/', '1', '6', '0', '1', '8', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '4', '2', '0', '1', '8', '7', '7', '6', '5', '9', '8', '3', '/', '1', '6', '0', '1', '8', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '6', '1', '1', '9', '5', '1', '5', '2', '4', '0', '7', '/', '2', '9', '1', '2', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '4', '4', '5', '2', '5', '2', '6', '4', '1', '7', '/', '5', '8', '2', '4', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '2', '2', '7', '6', '4', '4', '7', '2', '5', '1', '/', '8', '3', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '3', '2', '2', '4', '1', '4', '2', '1', '3', '1', '/', '8', '3', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '2', '4', '0', '4', '9', '2', '7', '9', '1', '7', '/', '5', '7', '2', '0', '9', '6', '2', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0246486Acc00600 : List (String × SourceJson) := (fragment0246486Field005Key00, fragment0246486Field005Value00) :: fragment0246486Acc00500
noncomputable def fragment0246486Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '7', '3', '0', '9', '0', '0', '3', '9', '0', '7', '/', '1', '5', '2', '5', '5', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '0', '5', '4', '0', '4', '7', '0', '3', '9', '/', '2', '3', '8', '3', '7', '3', '4', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '1', '1', '1', '0', '3', '1', '4', '5', '5', '7', '/', '1', '6', '0', '1', '8', '6', '9', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '0', '7', '2', '3', '5', '6', '7', '6', '1', '6', '3', '/', '1', '6', '0', '1', '8', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '2', '0', '1', '8', '7', '7', '6', '5', '9', '8', '3', '/', '1', '6', '0', '1', '8', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '6', '1', '1', '9', '5', '1', '5', '2', '4', '0', '7', '/', '2', '9', '1', '2', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '4', '4', '5', '2', '5', '2', '6', '4', '1', '7', '/', '5', '8', '2', '4', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '2', '2', '7', '6', '4', '4', '7', '2', '5', '1', '/', '8', '3', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '2', '2', '4', '1', '4', '2', '1', '3', '1', '/', '8', '3', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '4', '0', '4', '9', '2', '7', '9', '1', '7', '/', '5', '7', '2', '0', '9', '6', '2', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0246486_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0246486Field005Chars00 ++ tail)) fragment0246486Acc00500 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0246486Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246486_object_field_005"
  err.flush

noncomputable def fragment0246486Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0246486Field006Value00 : SourceJson := .str (String.ofList ['6', '3', '2', '7', '7', '7', '5', '0', '1', '7', '6', '5', '3', '5', '6', '1', '5', '7', '3', '2', '4', '0', '7', '7', '5', '2', '1', '6', '0', '8', '5', '8', '5', '1', '6', '6', '8', '2', '5', '3', '8', '3', '0', '6', '5', '0', '0', '0', '0', '/', '1', '2', '3', '9', '9', '2', '5', '5', '9', '0', '3', '5', '7', '4', '5', '6', '1', '1', '8', '4', '4', '9', '9', '9', '4', '1', '9', '3', '7', '4', '3', '3', '8', '7', '1', '3', '4', '2', '7', '8', '6', '0', '7', '1', '2', '4', '9', '5', '8', '7', '8', '0', '1', '3', '0', '8', '0', '7', '8', '1', '5', '8', '0', '0', '6', '3'])
noncomputable def fragment0246486Acc00700 : List (String × SourceJson) := (fragment0246486Field006Key00, fragment0246486Field006Value00) :: fragment0246486Acc00600
noncomputable def fragment0246486Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '3', '2', '7', '7', '7', '5', '0', '1', '7', '6', '5', '3', '5', '6', '1', '5', '7', '3', '2', '4', '0', '7', '7', '5', '2', '1', '6', '0', '8', '5', '8', '5', '1', '6', '6', '8', '2', '5', '3', '8', '3', '0', '6', '5', '0', '0', '0', '0', '/', '1', '2', '3', '9', '9', '2', '5', '5', '9', '0', '3', '5', '7', '4', '5', '6', '1', '1', '8', '4', '4', '9', '9', '9', '4', '1', '9', '3', '7', '4', '3', '3', '8', '7', '1', '3', '4', '2', '7', '8', '6', '0', '7', '1', '2', '4', '9', '5', '8', '7', '8', '0', '1', '3', '0', '8', '0', '7', '8', '1', '5', '8', '0', '0', '6', '3', '"', ',']

theorem object_fragment0246486_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0246486Field006Chars00 ++ tail)) fragment0246486Acc00600 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0246486Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246486_object_field_006"
  err.flush

noncomputable def fragment0246486Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0246486Field007Value00 : SourceJson := .str (String.ofList ['1', '5', '7', '5', '4', '2', '4', '1', '5', '4', '4', '5', '2', '4', '9', '6', '9', '3', '7', '7', '2', '8', '8', '8', '1', '9', '4', '2', '7', '4', '7', '3', '8', '8', '5', '7', '9', '7', '1', '9', '7', '7', '0', '0', '1', '7', '6', '9', '5', '5', '1', '8', '4', '8', '4', '5', '9', '0', '6', '6', '5', '0', '0', '4', '2', '0', '0', '1', '7', '9', '6', '1', '9', '7', '3', '2', '5', '4', '6', '9', '0', '8', '1', '2', '7', '7', '4', '6', '5', '8', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '2', '8', '9', '4', '7', '9', '5', '9', '5', '8', '7', '5', '7', '5', '1', '3', '2', '3', '5', '4', '2', '9', '6', '1', '6', '3', '8', '9', '3', '2', '1', '7', '5', '4', '9', '4', '8', '7', '7', '0', '2', '2', '7', '6', '2', '4', '6', '1', '8', '1', '0', '2', '9', '6', '4', '3', '7', '9', '4', '1', '5', '1', '4', '4', '5', '8', '4', '5', '9', '4', '5', '6', '4', '0', '2', '3', '0', '4', '5', '6', '7', '2', '7', '2', '2', '3', '8', '2', '9', '3', '7', '2', '0', '1', '2', '1', '6', '1', '2', '9', '7', '1', '9', '5', '5', '6', '2', '3', '0', '4', '3', '1', '8', '8', '2', '0', '4', '4', '7'])
noncomputable def fragment0246486Acc00800 : List (String × SourceJson) := (fragment0246486Field007Key00, fragment0246486Field007Value00) :: fragment0246486Acc00700
noncomputable def fragment0246486Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '7', '5', '4', '2', '4', '1', '5', '4', '4', '5', '2', '4', '9', '6', '9', '3', '7', '7', '2', '8', '8', '8', '1', '9', '4', '2', '7', '4', '7', '3', '8', '8', '5', '7', '9', '7', '1', '9', '7', '7', '0', '0', '1', '7', '6', '9', '5', '5', '1', '8', '4', '8', '4', '5', '9', '0', '6', '6', '5', '0', '0', '4', '2', '0', '0', '1', '7', '9', '6', '1', '9', '7', '3', '2', '5', '4', '6', '9', '0', '8', '1', '2', '7', '7', '4', '6', '5', '8', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '2', '8', '9', '4', '7', '9', '5', '9', '5', '8', '7', '5', '7', '5', '1', '3', '2', '3', '5', '4', '2', '9', '6', '1', '6', '3', '8', '9', '3', '2', '1', '7', '5', '4', '9', '4', '8', '7', '7', '0', '2', '2', '7', '6', '2', '4', '6', '1', '8', '1', '0', '2', '9', '6', '4', '3', '7', '9', '4', '1', '5', '1', '4', '4', '5', '8', '4', '5', '9', '4', '5', '6', '4', '0', '2', '3', '0', '4', '5', '6', '7', '2', '7', '2', '2', '3', '8', '2', '9', '3', '7', '2', '0', '1', '2', '1', '6', '1', '2', '9', '7', '1', '9', '5', '5', '6', '2', '3', '0', '4', '3', '1', '8', '8', '2', '0', '4', '4', '7', '"', ',']

theorem object_fragment0246486_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0246486Field007Chars00 ++ tail)) fragment0246486Acc00700 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0246486Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246486_object_field_007"
  err.flush

noncomputable def fragment0246486Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0246486Field008Value00 : SourceJson := .str (String.ofList ['4', '0', '4', '3', '2', '9', '0', '9', '1', '4', '8', '0', '2'])
noncomputable def fragment0246486Acc00900 : List (String × SourceJson) := (fragment0246486Field008Key00, fragment0246486Field008Value00) :: fragment0246486Acc00800
noncomputable def fragment0246486Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '4', '3', '2', '9', '0', '9', '1', '4', '8', '0', '2', '"', ',']

theorem object_fragment0246486_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0246486Field008Chars00 ++ tail)) fragment0246486Acc00800 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0246486Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246486_object_field_008"
  err.flush

noncomputable def fragment0246486Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0246486Field009Value00 : SourceJson := .str (String.ofList ['1', '7', '1', '2', '3', '0', '2', '7', '6', '8', '6', '1', '5', '7'])
noncomputable def fragment0246486Acc01000 : List (String × SourceJson) := (fragment0246486Field009Key00, fragment0246486Field009Value00) :: fragment0246486Acc00900
noncomputable def fragment0246486Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '1', '2', '3', '0', '2', '7', '6', '8', '6', '1', '5', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0246486_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0246486Field009Chars00 ++ tail)) fragment0246486Acc00900 =
      .ok (.obj (fragment0246486Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246486_object_field_009"
  err.flush

noncomputable def fragment0246486Chars : List Char := '{' :: (fragment0246486Field000Chars00 ++ fragment0246486Field001Chars00 ++ fragment0246486Field002Chars00 ++ fragment0246486Field003Chars00 ++ fragment0246486Field004Chars00 ++ fragment0246486Field005Chars00 ++ fragment0246486Field006Chars00 ++ fragment0246486Field007Chars00 ++ fragment0246486Field008Chars00 ++ fragment0246486Field009Chars00)
noncomputable def fragment0246486Value : SourceJson := .obj (fragment0246486Acc01000.reverse)

theorem value_fragment0246486 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 237) (fragment0246486Chars ++ tail) =
      .ok (fragment0246486Value, tail) := by
  have hinput : fragment0246486Chars ++ tail = '{' :: (fragment0246486Field000Chars00 ++ (fragment0246486Field001Chars00 ++ (fragment0246486Field002Chars00 ++ (fragment0246486Field003Chars00 ++ (fragment0246486Field004Chars00 ++ (fragment0246486Field005Chars00 ++ (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0246486Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 237) (fragment0246486Chars ++ tail) =
        SourceJson.value (fuel + 237) ('{' :: (fragment0246486Field000Chars00 ++ (fragment0246486Field001Chars00 ++ (fragment0246486Field002Chars00 ++ (fragment0246486Field003Chars00 ++ (fragment0246486Field004Chars00 ++ (fragment0246486Field005Chars00 ++ (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 237)) hinput
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0246486Field000Chars00 ++ (fragment0246486Field001Chars00 ++ (fragment0246486Field002Chars00 ++ (fragment0246486Field003Chars00 ++ (fragment0246486Field004Chars00 ++ (fragment0246486Field005Chars00 ++ (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail)))))))))))) fragment0246486Acc00000 := by rfl
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0246486Field001Chars00 ++ (fragment0246486Field002Chars00 ++ (fragment0246486Field003Chars00 ++ (fragment0246486Field004Chars00 ++ (fragment0246486Field005Chars00 ++ (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail))))))))))) fragment0246486Acc00100 := object_fragment0246486_field_000 fuel (fragment0246486Field001Chars00 ++ (fragment0246486Field002Chars00 ++ (fragment0246486Field003Chars00 ++ (fragment0246486Field004Chars00 ++ (fragment0246486Field005Chars00 ++ (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0246486Field002Chars00 ++ (fragment0246486Field003Chars00 ++ (fragment0246486Field004Chars00 ++ (fragment0246486Field005Chars00 ++ (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail)))))))))) fragment0246486Acc00200 := object_fragment0246486_field_001 fuel (fragment0246486Field002Chars00 ++ (fragment0246486Field003Chars00 ++ (fragment0246486Field004Chars00 ++ (fragment0246486Field005Chars00 ++ (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0246486Field003Chars00 ++ (fragment0246486Field004Chars00 ++ (fragment0246486Field005Chars00 ++ (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail))))))))) fragment0246486Acc00300 := object_fragment0246486_field_002 fuel (fragment0246486Field003Chars00 ++ (fragment0246486Field004Chars00 ++ (fragment0246486Field005Chars00 ++ (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0246486Field004Chars00 ++ (fragment0246486Field005Chars00 ++ (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail)))))))) fragment0246486Acc00400 := object_fragment0246486_field_003 fuel (fragment0246486Field004Chars00 ++ (fragment0246486Field005Chars00 ++ (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0246486Field005Chars00 ++ (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail))))))) fragment0246486Acc00500 := object_fragment0246486_field_004 fuel (fragment0246486Field005Chars00 ++ (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail)))))) fragment0246486Acc00600 := object_fragment0246486_field_005 fuel (fragment0246486Field006Chars00 ++ (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail))))) fragment0246486Acc00700 := object_fragment0246486_field_006 fuel (fragment0246486Field007Chars00 ++ (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail)))) fragment0246486Acc00800 := object_fragment0246486_field_007 fuel (fragment0246486Field008Chars00 ++ (fragment0246486Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0246486Field009Chars00 ++ (tail))) fragment0246486Acc00900 := object_fragment0246486_field_008 fuel (fragment0246486Field009Chars00 ++ (tail))
    _ = .ok (fragment0246486Value, tail) := object_fragment0246486_field_009 fuel (tail)

noncomputable def fragment0248090Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0248090Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0248090Field000Value00 : SourceJson := .number (String.ofList ['6', '5'])
noncomputable def fragment0248090Acc00100 : List (String × SourceJson) := (fragment0248090Field000Key00, fragment0248090Field000Value00) :: fragment0248090Acc00000
noncomputable def fragment0248090Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '5', ',']

theorem object_fragment0248090_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 439) (SourceJson.white (fragment0248090Field000Chars00 ++ tail)) fragment0248090Acc00000 =
      SourceJson.object (fuel + 438) (SourceJson.white tail) fragment0248090Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248090_object_field_000"
  err.flush

noncomputable def fragment0248090Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0248090Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['3']), .number (String.ofList ['0'])]
noncomputable def fragment0248090Acc00200 : List (String × SourceJson) := (fragment0248090Field001Key00, fragment0248090Field001Value00) :: fragment0248090Acc00100
noncomputable def fragment0248090Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0248090_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 438) (SourceJson.white (fragment0248090Field001Chars00 ++ tail)) fragment0248090Acc00100 =
      SourceJson.object (fuel + 437) (SourceJson.white tail) fragment0248090Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248090_object_field_001"
  err.flush

noncomputable def fragment0248090Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0248090Field002Value00 : SourceJson := .str (String.ofList ['7', '0', '3', '2', '5', '1', '9', '7', '4', '3', '7', '7', '7', '5', '1', '0', '1', '0', '3', '6', '4', '4', '5', '3', '3', '8', '0', '3', '4', '8', '4', '9', '5', '5', '8', '9', '3', '3', '/', '3', '9', '5', '8', '8', '5', '3', '9', '9', '1', '3', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0248090Acc00300 : List (String × SourceJson) := (fragment0248090Field002Key00, fragment0248090Field002Value00) :: fragment0248090Acc00200
noncomputable def fragment0248090Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '0', '3', '2', '5', '1', '9', '7', '4', '3', '7', '7', '7', '5', '1', '0', '1', '0', '3', '6', '4', '4', '5', '3', '3', '8', '0', '3', '4', '8', '4', '9', '5', '5', '8', '9', '3', '3', '/', '3', '9', '5', '8', '8', '5', '3', '9', '9', '1', '3', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0248090_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 437) (SourceJson.white (fragment0248090Field002Chars00 ++ tail)) fragment0248090Acc00200 =
      SourceJson.object (fuel + 436) (SourceJson.white tail) fragment0248090Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248090_object_field_002"
  err.flush

noncomputable def fragment0248090Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0248090Field003Value00 : SourceJson := .str (String.ofList ['3', '1', '7', '2', '9', '3', '8', '7', '/', '2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0248090Acc00400 : List (String × SourceJson) := (fragment0248090Field003Key00, fragment0248090Field003Value00) :: fragment0248090Acc00300
noncomputable def fragment0248090Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '1', '7', '2', '9', '3', '8', '7', '/', '2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0248090_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 436) (SourceJson.white (fragment0248090Field003Chars00 ++ tail)) fragment0248090Acc00300 =
      SourceJson.object (fuel + 435) (SourceJson.white tail) fragment0248090Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248090_object_field_003"
  err.flush

noncomputable def fragment0248090Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0248090Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0248090Acc00500 : List (String × SourceJson) := (fragment0248090Field004Key00, fragment0248090Field004Value00) :: fragment0248090Acc00400
noncomputable def fragment0248090Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0248090_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 435) (SourceJson.white (fragment0248090Field004Chars00 ++ tail)) fragment0248090Acc00400 =
      SourceJson.object (fuel + 434) (SourceJson.white tail) fragment0248090Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248090_object_field_004"
  err.flush

noncomputable def fragment0248090Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0248090Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '1', '2', '4', '3', '3', '5', '3', '9', '6', '1', '0', '4', '9', '6', '9', '8', '0', '4', '3', '7', '1', '1', '/', '5', '8', '2', '8', '0', '8', '6', '6', '7', '5', '8', '0', '4', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '2', '0', '8', '1', '5', '6', '2', '5', '7', '4', '1', '8', '9', '8', '3', '5', '9', '9', '3', '7', '9', '/', '2', '9', '1', '4', '0', '4', '3', '3', '3', '7', '9', '0', '2', '4', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '3', '8', '4', '5', '4', '8', '5', '2', '4', '4', '5', '7', '7', '2', '5', '2', '6', '6', '5', '9', '/', '1', '1', '6', '5', '6', '1', '7', '3', '3', '5', '1', '6', '0', '9', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '7', '2', '0', '8', '5', '3', '0', '3', '6', '9', '8', '7', '4', '9', '8', '1', '3', '0', '9', '2', '1', '/', '1', '9', '4', '2', '6', '9', '5', '5', '5', '8', '6', '0', '1', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '6', '1', '5', '2', '8', '4', '1', '4', '4', '8', '3', '2', '2', '7', '5', '2', '2', '8', '3', '6', '1', '/', '1', '9', '4', '2', '6', '9', '5', '5', '5', '8', '6', '0', '1', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '6', '8', '4', '2', '1', '5', '5', '6', '7', '4', '8', '3', '1', '5', '1', '2', '5', '9', '4', '1', '/', '5', '2', '9', '8', '2', '6', '0', '6', '1', '4', '3', '6', '8', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '0', '7', '3', '6', '5', '6', '0', '3', '0', '0', '6', '2', '1', '8', '5', '1', '8', '5', '9', '1', '/', '1', '0', '5', '9', '6', '5', '2', '1', '2', '2', '8', '7', '3', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '3', '4', '8', '7', '6', '8', '1', '4', '9', '2', '2', '7', '4', '4', '4', '5', '6', '9', '7', '1', '/', '1', '0', '5', '9', '6', '5', '2', '1', '2', '2', '8', '7', '3', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '2', '8', '1', '6', '4', '9', '2', '3', '3', '8', '1', '8', '6', '6', '7', '8', '7', '7', '3', '/', '5', '2', '9', '8', '2', '6', '0', '6', '1', '4', '3', '6', '8', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '3', '8', '3', '9', '8', '9', '3', '8', '0', '8', '9', '0', '3', '3', '7', '6', '8', '5', '1', '3', '/', '2', '9', '1', '4', '0', '4', '3', '3', '3', '7', '9', '0', '2', '4', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0248090Acc00600 : List (String × SourceJson) := (fragment0248090Field005Key00, fragment0248090Field005Value00) :: fragment0248090Acc00500
noncomputable def fragment0248090Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '2', '4', '3', '3', '5', '3', '9', '6', '1', '0', '4', '9', '6', '9', '8', '0', '4', '3', '7', '1', '1', '/', '5', '8', '2', '8', '0', '8', '6', '6', '7', '5', '8', '0', '4', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '2', '0', '8', '1', '5', '6', '2', '5', '7', '4', '1', '8', '9', '8', '3', '5', '9', '9', '3', '7', '9', '/', '2', '9', '1', '4', '0', '4', '3', '3', '3', '7', '9', '0', '2', '4', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '3', '8', '4', '5', '4', '8', '5', '2', '4', '4', '5', '7', '7', '2', '5', '2', '6', '6', '5', '9', '/', '1', '1', '6', '5', '6', '1', '7', '3', '3', '5', '1', '6', '0', '9', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '7', '2', '0', '8', '5', '3', '0', '3', '6', '9', '8', '7', '4', '9', '8', '1', '3', '0', '9', '2', '1', '/', '1', '9', '4', '2', '6', '9', '5', '5', '5', '8', '6', '0', '1', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '1', '5', '2', '8', '4', '1', '4', '4', '8', '3', '2', '2', '7', '5', '2', '2', '8', '3', '6', '1', '/', '1', '9', '4', '2', '6', '9', '5', '5', '5', '8', '6', '0', '1', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '6', '8', '4', '2', '1', '5', '5', '6', '7', '4', '8', '3', '1', '5', '1', '2', '5', '9', '4', '1', '/', '5', '2', '9', '8', '2', '6', '0', '6', '1', '4', '3', '6', '8', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '0', '7', '3', '6', '5', '6', '0', '3', '0', '0', '6', '2', '1', '8', '5', '1', '8', '5', '9', '1', '/', '1', '0', '5', '9', '6', '5', '2', '1', '2', '2', '8', '7', '3', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '3', '4', '8', '7', '6', '8', '1', '4', '9', '2', '2', '7', '4', '4', '4', '5', '6', '9', '7', '1', '/', '1', '0', '5', '9', '6', '5', '2', '1', '2', '2', '8', '7', '3', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '2', '8', '1', '6', '4', '9', '2', '3', '3', '8', '1', '8', '6', '6', '7', '8', '7', '7', '3', '/', '5', '2', '9', '8', '2', '6', '0', '6', '1', '4', '3', '6', '8', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '3', '8', '3', '9', '8', '9', '3', '8', '0', '8', '9', '0', '3', '3', '7', '6', '8', '5', '1', '3', '/', '2', '9', '1', '4', '0', '4', '3', '3', '3', '7', '9', '0', '2', '4', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0248090_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 434) (SourceJson.white (fragment0248090Field005Chars00 ++ tail)) fragment0248090Acc00500 =
      SourceJson.object (fuel + 433) (SourceJson.white tail) fragment0248090Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248090_object_field_005"
  err.flush

noncomputable def fragment0248090Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0248090Field006Value00 : SourceJson := .str (String.ofList ['4', '1', '3', '9', '1', '0', '9', '1', '7', '1', '3', '3', '7', '4', '7', '3', '2', '9', '6', '8', '0', '8', '0', '1', '4', '1', '8', '5', '6', '4', '3', '6', '5', '1', '2', '2', '6', '1', '0', '5', '9', '0', '0', '5', '0', '1', '9', '5', '0', '0', '0', '0', '0', '0', '0', '/', '9', '9', '4', '0', '0', '4', '7', '8', '3', '2', '6', '9', '9', '3', '7', '4', '5', '5', '6', '0', '6', '8', '4', '6', '9', '9', '8', '5', '0', '0', '6', '4', '8', '1', '4', '1', '3', '2', '4', '0', '6', '5', '8', '0', '7', '5', '8', '5', '7', '4', '8', '4', '6', '4', '2', '7', '9', '1', '5', '6', '4', '3', '2', '4', '5', '8', '3'])
noncomputable def fragment0248090Acc00700 : List (String × SourceJson) := (fragment0248090Field006Key00, fragment0248090Field006Value00) :: fragment0248090Acc00600
noncomputable def fragment0248090Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '1', '3', '9', '1', '0', '9', '1', '7', '1', '3', '3', '7', '4', '7', '3', '2', '9', '6', '8', '0', '8', '0', '1', '4', '1', '8', '5', '6', '4', '3', '6', '5', '1', '2', '2', '6', '1', '0', '5', '9', '0', '0', '5', '0', '1', '9', '5', '0', '0', '0', '0', '0', '0', '0', '/', '9', '9', '4', '0', '0', '4', '7', '8', '3', '2', '6', '9', '9', '3', '7', '4', '5', '5', '6', '0', '6', '8', '4', '6', '9', '9', '8', '5', '0', '0', '6', '4', '8', '1', '4', '1', '3', '2', '4', '0', '6', '5', '8', '0', '7', '5', '8', '5', '7', '4', '8', '4', '6', '4', '2', '7', '9', '1', '5', '6', '4', '3', '2', '4', '5', '8', '3', '"', ',']

theorem object_fragment0248090_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 433) (SourceJson.white (fragment0248090Field006Chars00 ++ tail)) fragment0248090Acc00600 =
      SourceJson.object (fuel + 432) (SourceJson.white tail) fragment0248090Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248090_object_field_006"
  err.flush

noncomputable def fragment0248090Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0248090Field007Value00 : SourceJson := .str (String.ofList ['7', '2', '6', '8', '8', '5', '9', '2', '5', '5', '0', '6', '8', '4', '4', '6', '4', '6', '2', '8', '4', '8', '9', '3', '3', '4', '8', '7', '5', '4', '8', '5', '5', '7', '9', '9', '6', '1', '3', '6', '7', '9', '5', '3', '4', '5', '2', '4', '8', '5', '3', '9', '5', '1', '7', '8', '1', '3', '7', '6', '0', '2', '6', '1', '7', '2', '8', '7', '8', '2', '0', '7', '6', '0', '3', '6', '0', '1', '8', '6', '1', '4', '4', '1', '2', '2', '9', '4', '2', '4', '2', '6', '0', '0', '2', '3', '9', '0', '9', '4', '5', '7', '6', '5', '8', '4', '3', '3', '9', '6', '0', '5', '7', '2', '9', '2', '5', '2', '5', '9', '3', '1', '8', '8', '9', '1', '5', '3', '2', '8', '5', '9', '7', '5', '7', '5', '2', '1', '3', '8', '0', '6', '0', '5', '6', '5', '6', '8', '2', '3', '6', '0', '5', '2', '7', '1', '5', '2', '8', '9', '2', '7', '7', '9', '3', '1', '5', '0', '2', '4', '3', '4', '5', '3', '9', '1', '2', '1', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '9', '1', '0', '6', '4', '1', '8', '2', '3', '1', '2', '7', '8', '2', '6', '5', '7', '8', '1', '5', '2', '4', '1', '6', '0', '3', '4', '2', '0', '9', '1', '8', '3', '7', '7', '4', '1', '6', '9', '7', '4', '9', '9', '8', '0', '6', '5', '8', '1', '6', '3', '3', '9', '9', '1', '3', '2', '9', '6', '2', '8', '2', '1', '2', '4', '0', '5', '2', '3', '1', '3', '1', '8', '2', '1', '4', '0', '5', '4', '8', '8', '5', '3', '7', '8', '3', '7', '3', '7', '2', '3', '7', '4', '2', '4', '0', '0', '4', '1', '3', '0', '4', '4', '2', '6', '8', '0', '3', '7', '0', '8', '1', '8', '0', '8', '6', '2', '6', '4', '5', '2', '0', '9', '9', '9', '4', '9', '8', '3', '4', '7', '4', '7', '5', '0', '1', '7', '5', '1', '3', '6', '3', '5', '6', '7', '8', '2', '9', '4', '8', '9', '8', '2', '7', '9', '8', '9', '9', '4', '1', '1', '8', '0', '3', '4', '6', '2', '2', '3', '5', '9', '4', '9', '2', '7', '5', '5', '5', '7', '6', '2', '1', '7', '0', '1', '7', '1', '8', '3', '5', '6', '9', '9', '5', '4', '7', '3', '1', '1', '4', '0', '0', '1', '4', '0', '9', '9', '7', '1', '2', '6', '2', '1', '1', '0', '2', '6', '9', '9'])
noncomputable def fragment0248090Acc00800 : List (String × SourceJson) := (fragment0248090Field007Key00, fragment0248090Field007Value00) :: fragment0248090Acc00700
noncomputable def fragment0248090Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '2', '6', '8', '8', '5', '9', '2', '5', '5', '0', '6', '8', '4', '4', '6', '4', '6', '2', '8', '4', '8', '9', '3', '3', '4', '8', '7', '5', '4', '8', '5', '5', '7', '9', '9', '6', '1', '3', '6', '7', '9', '5', '3', '4', '5', '2', '4', '8', '5', '3', '9', '5', '1', '7', '8', '1', '3', '7', '6', '0', '2', '6', '1', '7', '2', '8', '7', '8', '2', '0', '7', '6', '0', '3', '6', '0', '1', '8', '6', '1', '4', '4', '1', '2', '2', '9', '4', '2', '4', '2', '6', '0', '0', '2', '3', '9', '0', '9', '4', '5', '7', '6', '5', '8', '4', '3', '3', '9', '6', '0', '5', '7', '2', '9', '2', '5', '2', '5', '9', '3', '1', '8', '8', '9', '1', '5', '3', '2', '8', '5', '9', '7', '5', '7', '5', '2', '1', '3', '8', '0', '6', '0', '5', '6', '5', '6', '8', '2', '3', '6', '0', '5', '2', '7', '1', '5', '2', '8', '9', '2', '7', '7', '9', '3', '1', '5', '0', '2', '4', '3', '4', '5', '3', '9', '1', '2', '1', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '9', '1', '0', '6', '4', '1', '8', '2', '3', '1', '2', '7', '8', '2', '6', '5', '7', '8', '1', '5', '2', '4', '1', '6', '0', '3', '4', '2', '0', '9', '1', '8', '3', '7', '7', '4', '1', '6', '9', '7', '4', '9', '9', '8', '0', '6', '5', '8', '1', '6', '3', '3', '9', '9', '1', '3', '2', '9', '6', '2', '8', '2', '1', '2', '4', '0', '5', '2', '3', '1', '3', '1', '8', '2', '1', '4', '0', '5', '4', '8', '8', '5', '3', '7', '8', '3', '7', '3', '7', '2', '3', '7', '4', '2', '4', '0', '0', '4', '1', '3', '0', '4', '4', '2', '6', '8', '0', '3', '7', '0', '8', '1', '8', '0', '8', '6', '2', '6', '4', '5', '2', '0', '9', '9', '9', '4', '9', '8', '3', '4', '7', '4', '7', '5', '0', '1', '7', '5', '1', '3', '6', '3', '5', '6', '7', '8', '2', '9', '4', '8', '9', '8', '2', '7', '9', '8', '9', '9', '4', '1', '1', '8', '0', '3', '4', '6', '2', '2', '3', '5', '9', '4', '9', '2', '7', '5', '5', '5', '7', '6', '2', '1', '7', '0', '1', '7', '1', '8', '3', '5', '6', '9', '9', '5', '4', '7', '3', '1', '1', '4', '0', '0', '1', '4', '0', '9', '9', '7', '1', '2', '6', '2', '1', '1', '0', '2', '6', '9', '9', '"', ',']

theorem object_fragment0248090_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 432) (SourceJson.white (fragment0248090Field007Chars00 ++ tail)) fragment0248090Acc00700 =
      SourceJson.object (fuel + 431) (SourceJson.white tail) fragment0248090Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248090_object_field_007"
  err.flush

noncomputable def fragment0248090Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0248090Field008Value00 : SourceJson := .str (String.ofList ['3', '2', '9', '9', '1', '1', '9', '0', '7', '4', '7', '8', '1', '6', '7', '2', '8'])
noncomputable def fragment0248090Acc00900 : List (String × SourceJson) := (fragment0248090Field008Key00, fragment0248090Field008Value00) :: fragment0248090Acc00800
noncomputable def fragment0248090Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '9', '9', '1', '1', '9', '0', '7', '4', '7', '8', '1', '6', '7', '2', '8', '"', ',']

theorem object_fragment0248090_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 431) (SourceJson.white (fragment0248090Field008Chars00 ++ tail)) fragment0248090Acc00800 =
      SourceJson.object (fuel + 430) (SourceJson.white tail) fragment0248090Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248090_object_field_008"
  err.flush

noncomputable def fragment0248090Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0248090Field009Value00 : SourceJson := .str (String.ofList ['1', '1', '7', '2', '7', '5', '5', '7', '8', '8', '5', '4', '3', '8', '6', '8', '2', '1'])
noncomputable def fragment0248090Acc01000 : List (String × SourceJson) := (fragment0248090Field009Key00, fragment0248090Field009Value00) :: fragment0248090Acc00900
noncomputable def fragment0248090Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '7', '2', '7', '5', '5', '7', '8', '8', '5', '4', '3', '8', '6', '8', '2', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0248090_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 430) (SourceJson.white (fragment0248090Field009Chars00 ++ tail)) fragment0248090Acc00900 =
      .ok (.obj (fragment0248090Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248090_object_field_009"
  err.flush

noncomputable def fragment0248090Chars : List Char := '{' :: (fragment0248090Field000Chars00 ++ fragment0248090Field001Chars00 ++ fragment0248090Field002Chars00 ++ fragment0248090Field003Chars00 ++ fragment0248090Field004Chars00 ++ fragment0248090Field005Chars00 ++ fragment0248090Field006Chars00 ++ fragment0248090Field007Chars00 ++ fragment0248090Field008Chars00 ++ fragment0248090Field009Chars00)
noncomputable def fragment0248090Value : SourceJson := .obj (fragment0248090Acc01000.reverse)

theorem value_fragment0248090 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 440) (fragment0248090Chars ++ tail) =
      .ok (fragment0248090Value, tail) := by
  have hinput : fragment0248090Chars ++ tail = '{' :: (fragment0248090Field000Chars00 ++ (fragment0248090Field001Chars00 ++ (fragment0248090Field002Chars00 ++ (fragment0248090Field003Chars00 ++ (fragment0248090Field004Chars00 ++ (fragment0248090Field005Chars00 ++ (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0248090Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 440) (fragment0248090Chars ++ tail) =
        SourceJson.value (fuel + 440) ('{' :: (fragment0248090Field000Chars00 ++ (fragment0248090Field001Chars00 ++ (fragment0248090Field002Chars00 ++ (fragment0248090Field003Chars00 ++ (fragment0248090Field004Chars00 ++ (fragment0248090Field005Chars00 ++ (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 440)) hinput
    _ = SourceJson.object (fuel + 439) (SourceJson.white (fragment0248090Field000Chars00 ++ (fragment0248090Field001Chars00 ++ (fragment0248090Field002Chars00 ++ (fragment0248090Field003Chars00 ++ (fragment0248090Field004Chars00 ++ (fragment0248090Field005Chars00 ++ (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail)))))))))))) fragment0248090Acc00000 := by rfl
    _ = SourceJson.object (fuel + 438) (SourceJson.white (fragment0248090Field001Chars00 ++ (fragment0248090Field002Chars00 ++ (fragment0248090Field003Chars00 ++ (fragment0248090Field004Chars00 ++ (fragment0248090Field005Chars00 ++ (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail))))))))))) fragment0248090Acc00100 := object_fragment0248090_field_000 fuel (fragment0248090Field001Chars00 ++ (fragment0248090Field002Chars00 ++ (fragment0248090Field003Chars00 ++ (fragment0248090Field004Chars00 ++ (fragment0248090Field005Chars00 ++ (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 437) (SourceJson.white (fragment0248090Field002Chars00 ++ (fragment0248090Field003Chars00 ++ (fragment0248090Field004Chars00 ++ (fragment0248090Field005Chars00 ++ (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail)))))))))) fragment0248090Acc00200 := object_fragment0248090_field_001 fuel (fragment0248090Field002Chars00 ++ (fragment0248090Field003Chars00 ++ (fragment0248090Field004Chars00 ++ (fragment0248090Field005Chars00 ++ (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 436) (SourceJson.white (fragment0248090Field003Chars00 ++ (fragment0248090Field004Chars00 ++ (fragment0248090Field005Chars00 ++ (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail))))))))) fragment0248090Acc00300 := object_fragment0248090_field_002 fuel (fragment0248090Field003Chars00 ++ (fragment0248090Field004Chars00 ++ (fragment0248090Field005Chars00 ++ (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 435) (SourceJson.white (fragment0248090Field004Chars00 ++ (fragment0248090Field005Chars00 ++ (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail)))))))) fragment0248090Acc00400 := object_fragment0248090_field_003 fuel (fragment0248090Field004Chars00 ++ (fragment0248090Field005Chars00 ++ (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 434) (SourceJson.white (fragment0248090Field005Chars00 ++ (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail))))))) fragment0248090Acc00500 := object_fragment0248090_field_004 fuel (fragment0248090Field005Chars00 ++ (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 433) (SourceJson.white (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail)))))) fragment0248090Acc00600 := object_fragment0248090_field_005 fuel (fragment0248090Field006Chars00 ++ (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 432) (SourceJson.white (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail))))) fragment0248090Acc00700 := object_fragment0248090_field_006 fuel (fragment0248090Field007Chars00 ++ (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 431) (SourceJson.white (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail)))) fragment0248090Acc00800 := object_fragment0248090_field_007 fuel (fragment0248090Field008Chars00 ++ (fragment0248090Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 430) (SourceJson.white (fragment0248090Field009Chars00 ++ (tail))) fragment0248090Acc00900 := object_fragment0248090_field_008 fuel (fragment0248090Field009Chars00 ++ (tail))
    _ = .ok (fragment0248090Value, tail) := object_fragment0248090_field_009 fuel (tail)

noncomputable def fragment0250111Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0250111Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0250111Field000Value00 : SourceJson := .number (String.ofList ['6', '6'])
noncomputable def fragment0250111Acc00100 : List (String × SourceJson) := (fragment0250111Field000Key00, fragment0250111Field000Value00) :: fragment0250111Acc00000
noncomputable def fragment0250111Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '6', ',']

theorem object_fragment0250111_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0250111Field000Chars00 ++ tail)) fragment0250111Acc00000 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0250111Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250111_object_field_000"
  err.flush

noncomputable def fragment0250111Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0250111Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0250111Acc00200 : List (String × SourceJson) := (fragment0250111Field001Key00, fragment0250111Field001Value00) :: fragment0250111Acc00100
noncomputable def fragment0250111Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0250111_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0250111Field001Chars00 ++ tail)) fragment0250111Acc00100 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0250111Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250111_object_field_001"
  err.flush

noncomputable def fragment0250111Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0250111Field002Value00 : SourceJson := .str (String.ofList ['3', '8', '9', '0', '6', '8', '3', '7', '6', '0', '9', '9', '8', '3', '8', '6', '7', '2', '6', '1', '6', '2', '1', '5', '7', '0', '5', '9', '7', '7', '8', '1', '3', '5', '3', '9', '1', '6', '9', '3', '9', '/', '4', '9', '7', '1', '5', '8', '4', '0', '8', '2', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0250111Acc00300 : List (String × SourceJson) := (fragment0250111Field002Key00, fragment0250111Field002Value00) :: fragment0250111Acc00200
noncomputable def fragment0250111Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '8', '9', '0', '6', '8', '3', '7', '6', '0', '9', '9', '8', '3', '8', '6', '7', '2', '6', '1', '6', '2', '1', '5', '7', '0', '5', '9', '7', '7', '8', '1', '3', '5', '3', '9', '1', '6', '9', '3', '9', '/', '4', '9', '7', '1', '5', '8', '4', '0', '8', '2', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0250111_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0250111Field002Chars00 ++ tail)) fragment0250111Acc00200 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0250111Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250111_object_field_002"
  err.flush

noncomputable def fragment0250111Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0250111Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0250111Acc00400 : List (String × SourceJson) := (fragment0250111Field003Key00, fragment0250111Field003Value00) :: fragment0250111Acc00300
noncomputable def fragment0250111Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0250111_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0250111Field003Chars00 ++ tail)) fragment0250111Acc00300 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0250111Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250111_object_field_003"
  err.flush

noncomputable def fragment0250111Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0250111Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0250111Acc00500 : List (String × SourceJson) := (fragment0250111Field004Key00, fragment0250111Field004Value00) :: fragment0250111Acc00400
noncomputable def fragment0250111Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0250111_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0250111Field004Chars00 ++ tail)) fragment0250111Acc00400 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0250111Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250111_object_field_004"
  err.flush

noncomputable def fragment0250111Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0250111Field005Value00 : SourceJson := .arr [.str (String.ofList ['9', '2', '9', '1', '1', '6', '9', '1', '2', '9', '7', '0', '9', '/', '1', '0', '6', '7', '9', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '9', '0', '2', '7', '3', '9', '6', '9', '7', '9', '/', '1', '3', '3', '4', '8', '9', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '2', '7', '7', '7', '6', '1', '6', '7', '7', '9', '/', '4', '0', '0', '4', '6', '7', '3', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '5', '0', '7', '2', '3', '4', '1', '5', '0', '5', '7', '3', '/', '1', '6', '0', '1', '8', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '4', '2', '0', '1', '8', '6', '2', '4', '0', '3', '9', '3', '/', '1', '6', '0', '1', '8', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '6', '1', '1', '9', '4', '8', '7', '5', '0', '2', '7', '/', '2', '9', '1', '2', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '7', '5', '1', '4', '6', '7', '3', '0', '0', '2', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '6', '5', '6', '2', '7', '4', '7', '4', '7', '9', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '1', '2', '5', '6', '6', '2', '2', '1', '1', '1', '7', '/', '5', '8', '2', '4', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '0', '3', '4', '1', '7', '6', '2', '9', '1', '0', '7', '/', '2', '0', '0', '2', '3', '3', '6', '8', '7', '5', '0', '0', '0', '0'])]
noncomputable def fragment0250111Acc00600 : List (String × SourceJson) := (fragment0250111Field005Key00, fragment0250111Field005Value00) :: fragment0250111Acc00500
noncomputable def fragment0250111Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '9', '1', '1', '6', '9', '1', '2', '9', '7', '0', '9', '/', '1', '0', '6', '7', '9', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '9', '0', '2', '7', '3', '9', '6', '9', '7', '9', '/', '1', '3', '3', '4', '8', '9', '1', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '2', '7', '7', '7', '6', '1', '6', '7', '7', '9', '/', '4', '0', '0', '4', '6', '7', '3', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '0', '7', '2', '3', '4', '1', '5', '0', '5', '7', '3', '/', '1', '6', '0', '1', '8', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '2', '0', '1', '8', '6', '2', '4', '0', '3', '9', '3', '/', '1', '6', '0', '1', '8', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '6', '1', '1', '9', '4', '8', '7', '5', '0', '2', '7', '/', '2', '9', '1', '2', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '7', '5', '1', '4', '6', '7', '3', '0', '0', '2', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '6', '5', '6', '2', '7', '4', '7', '4', '7', '9', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '1', '2', '5', '6', '6', '2', '2', '1', '1', '1', '7', '/', '5', '8', '2', '4', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '3', '4', '1', '7', '6', '2', '9', '1', '0', '7', '/', '2', '0', '0', '2', '3', '3', '6', '8', '7', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0250111_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0250111Field005Chars00 ++ tail)) fragment0250111Acc00500 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0250111Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250111_object_field_005"
  err.flush

noncomputable def fragment0250111Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0250111Field006Value00 : SourceJson := .str (String.ofList ['2', '1', '6', '2', '6', '3', '9', '7', '1', '0', '6', '0', '9', '6', '8', '2', '6', '3', '3', '9', '2', '8', '6', '9', '7', '0', '6', '4', '5', '0', '8', '3', '2', '2', '5', '3', '2', '2', '7', '5', '7', '4', '6', '9', '1', '9', '6', '1', '6', '3', '4', '3', '7', '5', '/', '2', '8', '9', '3', '1', '4', '3', '4', '3', '2', '3', '3', '2', '8', '3', '1', '2', '3', '7', '7', '7', '7', '3', '1', '7', '3', '3', '7', '4', '6', '0', '3', '1', '8', '7', '6', '6', '8', '9', '2', '8', '0', '3', '2', '7', '6', '8', '1', '0', '4', '1', '1', '7', '1', '4', '0', '6', '8', '9', '0', '7', '7', '6', '6', '5', '1'])
noncomputable def fragment0250111Acc00700 : List (String × SourceJson) := (fragment0250111Field006Key00, fragment0250111Field006Value00) :: fragment0250111Acc00600
noncomputable def fragment0250111Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '6', '2', '6', '3', '9', '7', '1', '0', '6', '0', '9', '6', '8', '2', '6', '3', '3', '9', '2', '8', '6', '9', '7', '0', '6', '4', '5', '0', '8', '3', '2', '2', '5', '3', '2', '2', '7', '5', '7', '4', '6', '9', '1', '9', '6', '1', '6', '3', '4', '3', '7', '5', '/', '2', '8', '9', '3', '1', '4', '3', '4', '3', '2', '3', '3', '2', '8', '3', '1', '2', '3', '7', '7', '7', '7', '3', '1', '7', '3', '3', '7', '4', '6', '0', '3', '1', '8', '7', '6', '6', '8', '9', '2', '8', '0', '3', '2', '7', '6', '8', '1', '0', '4', '1', '1', '7', '1', '4', '0', '6', '8', '9', '0', '7', '7', '6', '6', '5', '1', '"', ',']

theorem object_fragment0250111_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0250111Field006Chars00 ++ tail)) fragment0250111Acc00600 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0250111Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250111_object_field_006"
  err.flush

noncomputable def fragment0250111Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0250111Field007Value00 : SourceJson := .str (String.ofList ['1', '4', '1', '0', '2', '9', '9', '5', '4', '0', '7', '8', '2', '1', '0', '2', '2', '8', '2', '1', '0', '9', '7', '6', '8', '0', '9', '2', '4', '3', '6', '8', '6', '0', '9', '3', '3', '4', '1', '6', '3', '9', '3', '0', '7', '4', '6', '3', '0', '5', '5', '7', '7', '0', '4', '5', '5', '6', '9', '9', '3', '0', '3', '8', '7', '6', '5', '5', '6', '7', '7', '8', '9', '7', '6', '1', '5', '8', '3', '5', '0', '9', '4', '7', '1', '3', '1', '4', '1', '5', '4', '0', '5', '1', '9', '7', '1', '4', '3', '5', '5', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '/', '4', '4', '6', '9', '6', '8', '8', '3', '3', '1', '0', '5', '8', '0', '5', '7', '6', '0', '9', '1', '2', '3', '5', '4', '8', '5', '4', '0', '9', '7', '2', '6', '7', '8', '4', '8', '8', '3', '1', '7', '0', '5', '9', '8', '2', '3', '8', '8', '3', '4', '2', '0', '9', '8', '5', '1', '2', '7', '9', '2', '2', '0', '2', '2', '8', '3', '9', '4', '1', '1', '2', '8', '2', '4', '2', '0', '4', '7', '0', '2', '7', '5', '8', '0', '8', '3', '0', '5', '5', '2', '5', '8', '8', '7', '7', '9', '3', '1', '7', '0', '3', '0', '6', '6', '1', '1', '4', '1', '1', '2', '4', '6', '0', '2', '0', '2', '2', '2', '7', '5', '6', '8', '1', '3'])
noncomputable def fragment0250111Acc00800 : List (String × SourceJson) := (fragment0250111Field007Key00, fragment0250111Field007Value00) :: fragment0250111Acc00700
noncomputable def fragment0250111Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '1', '0', '2', '9', '9', '5', '4', '0', '7', '8', '2', '1', '0', '2', '2', '8', '2', '1', '0', '9', '7', '6', '8', '0', '9', '2', '4', '3', '6', '8', '6', '0', '9', '3', '3', '4', '1', '6', '3', '9', '3', '0', '7', '4', '6', '3', '0', '5', '5', '7', '7', '0', '4', '5', '5', '6', '9', '9', '3', '0', '3', '8', '7', '6', '5', '5', '6', '7', '7', '8', '9', '7', '6', '1', '5', '8', '3', '5', '0', '9', '4', '7', '1', '3', '1', '4', '1', '5', '4', '0', '5', '1', '9', '7', '1', '4', '3', '5', '5', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '/', '4', '4', '6', '9', '6', '8', '8', '3', '3', '1', '0', '5', '8', '0', '5', '7', '6', '0', '9', '1', '2', '3', '5', '4', '8', '5', '4', '0', '9', '7', '2', '6', '7', '8', '4', '8', '8', '3', '1', '7', '0', '5', '9', '8', '2', '3', '8', '8', '3', '4', '2', '0', '9', '8', '5', '1', '2', '7', '9', '2', '2', '0', '2', '2', '8', '3', '9', '4', '1', '1', '2', '8', '2', '4', '2', '0', '4', '7', '0', '2', '7', '5', '8', '0', '8', '3', '0', '5', '5', '2', '5', '8', '8', '7', '7', '9', '3', '1', '7', '0', '3', '0', '6', '6', '1', '1', '4', '1', '1', '2', '4', '6', '0', '2', '0', '2', '2', '2', '7', '5', '6', '8', '1', '3', '"', ',']

theorem object_fragment0250111_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0250111Field007Chars00 ++ tail)) fragment0250111Acc00700 =
      SourceJson.object (fuel + 240) (SourceJson.white tail) fragment0250111Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250111_object_field_007"
  err.flush

noncomputable def fragment0250111Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0250111Field008Value00 : SourceJson := .str (String.ofList ['5', '9', '2', '2', '3', '4', '6', '2', '1', '1', '2', '9', '1', '2', '6', '6', '3'])
noncomputable def fragment0250111Acc00900 : List (String × SourceJson) := (fragment0250111Field008Key00, fragment0250111Field008Value00) :: fragment0250111Acc00800
noncomputable def fragment0250111Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '2', '2', '3', '4', '6', '2', '1', '1', '2', '9', '1', '2', '6', '6', '3', '"', ',']

theorem object_fragment0250111_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 240) (SourceJson.white (fragment0250111Field008Chars00 ++ tail)) fragment0250111Acc00800 =
      SourceJson.object (fuel + 239) (SourceJson.white tail) fragment0250111Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250111_object_field_008"
  err.flush

noncomputable def fragment0250111Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0250111Field009Value00 : SourceJson := .str (String.ofList ['2', '4', '9', '9', '8', '4', '8', '6', '0', '0', '9', '5', '2', '1', '5', '9', '1', '6'])
noncomputable def fragment0250111Acc01000 : List (String × SourceJson) := (fragment0250111Field009Key00, fragment0250111Field009Value00) :: fragment0250111Acc00900
noncomputable def fragment0250111Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '9', '9', '8', '4', '8', '6', '0', '0', '9', '5', '2', '1', '5', '9', '1', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0250111_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0250111Field009Chars00 ++ tail)) fragment0250111Acc00900 =
      .ok (.obj (fragment0250111Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0250111_object_field_009"
  err.flush

noncomputable def fragment0250111Chars : List Char := '{' :: (fragment0250111Field000Chars00 ++ fragment0250111Field001Chars00 ++ fragment0250111Field002Chars00 ++ fragment0250111Field003Chars00 ++ fragment0250111Field004Chars00 ++ fragment0250111Field005Chars00 ++ fragment0250111Field006Chars00 ++ fragment0250111Field007Chars00 ++ fragment0250111Field008Chars00 ++ fragment0250111Field009Chars00)
noncomputable def fragment0250111Value : SourceJson := .obj (fragment0250111Acc01000.reverse)

theorem value_fragment0250111 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 249) (fragment0250111Chars ++ tail) =
      .ok (fragment0250111Value, tail) := by
  have hinput : fragment0250111Chars ++ tail = '{' :: (fragment0250111Field000Chars00 ++ (fragment0250111Field001Chars00 ++ (fragment0250111Field002Chars00 ++ (fragment0250111Field003Chars00 ++ (fragment0250111Field004Chars00 ++ (fragment0250111Field005Chars00 ++ (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0250111Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 249) (fragment0250111Chars ++ tail) =
        SourceJson.value (fuel + 249) ('{' :: (fragment0250111Field000Chars00 ++ (fragment0250111Field001Chars00 ++ (fragment0250111Field002Chars00 ++ (fragment0250111Field003Chars00 ++ (fragment0250111Field004Chars00 ++ (fragment0250111Field005Chars00 ++ (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 249)) hinput
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0250111Field000Chars00 ++ (fragment0250111Field001Chars00 ++ (fragment0250111Field002Chars00 ++ (fragment0250111Field003Chars00 ++ (fragment0250111Field004Chars00 ++ (fragment0250111Field005Chars00 ++ (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail)))))))))))) fragment0250111Acc00000 := by rfl
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0250111Field001Chars00 ++ (fragment0250111Field002Chars00 ++ (fragment0250111Field003Chars00 ++ (fragment0250111Field004Chars00 ++ (fragment0250111Field005Chars00 ++ (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail))))))))))) fragment0250111Acc00100 := object_fragment0250111_field_000 fuel (fragment0250111Field001Chars00 ++ (fragment0250111Field002Chars00 ++ (fragment0250111Field003Chars00 ++ (fragment0250111Field004Chars00 ++ (fragment0250111Field005Chars00 ++ (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0250111Field002Chars00 ++ (fragment0250111Field003Chars00 ++ (fragment0250111Field004Chars00 ++ (fragment0250111Field005Chars00 ++ (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail)))))))))) fragment0250111Acc00200 := object_fragment0250111_field_001 fuel (fragment0250111Field002Chars00 ++ (fragment0250111Field003Chars00 ++ (fragment0250111Field004Chars00 ++ (fragment0250111Field005Chars00 ++ (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0250111Field003Chars00 ++ (fragment0250111Field004Chars00 ++ (fragment0250111Field005Chars00 ++ (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail))))))))) fragment0250111Acc00300 := object_fragment0250111_field_002 fuel (fragment0250111Field003Chars00 ++ (fragment0250111Field004Chars00 ++ (fragment0250111Field005Chars00 ++ (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0250111Field004Chars00 ++ (fragment0250111Field005Chars00 ++ (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail)))))))) fragment0250111Acc00400 := object_fragment0250111_field_003 fuel (fragment0250111Field004Chars00 ++ (fragment0250111Field005Chars00 ++ (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0250111Field005Chars00 ++ (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail))))))) fragment0250111Acc00500 := object_fragment0250111_field_004 fuel (fragment0250111Field005Chars00 ++ (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail)))))) fragment0250111Acc00600 := object_fragment0250111_field_005 fuel (fragment0250111Field006Chars00 ++ (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail))))) fragment0250111Acc00700 := object_fragment0250111_field_006 fuel (fragment0250111Field007Chars00 ++ (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 240) (SourceJson.white (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail)))) fragment0250111Acc00800 := object_fragment0250111_field_007 fuel (fragment0250111Field008Chars00 ++ (fragment0250111Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0250111Field009Chars00 ++ (tail))) fragment0250111Acc00900 := object_fragment0250111_field_008 fuel (fragment0250111Field009Chars00 ++ (tail))
    _ = .ok (fragment0250111Value, tail) := object_fragment0250111_field_009 fuel (tail)

noncomputable def fragment0251756Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0251756Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0251756Field000Value00 : SourceJson := .number (String.ofList ['6', '7'])
noncomputable def fragment0251756Acc00100 : List (String × SourceJson) := (fragment0251756Field000Key00, fragment0251756Field000Value00) :: fragment0251756Acc00000
noncomputable def fragment0251756Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '7', ',']

theorem object_fragment0251756_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 421) (SourceJson.white (fragment0251756Field000Chars00 ++ tail)) fragment0251756Acc00000 =
      SourceJson.object (fuel + 420) (SourceJson.white tail) fragment0251756Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251756_object_field_000"
  err.flush

noncomputable def fragment0251756Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0251756Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['3'])]
noncomputable def fragment0251756Acc00200 : List (String × SourceJson) := (fragment0251756Field001Key00, fragment0251756Field001Value00) :: fragment0251756Acc00100
noncomputable def fragment0251756Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0251756_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 420) (SourceJson.white (fragment0251756Field001Chars00 ++ tail)) fragment0251756Acc00100 =
      SourceJson.object (fuel + 419) (SourceJson.white tail) fragment0251756Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251756_object_field_001"
  err.flush

noncomputable def fragment0251756Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0251756Field002Value00 : SourceJson := .str (String.ofList ['1', '3', '4', '7', '6', '4', '9', '2', '3', '2', '9', '6', '4', '6', '5', '6', '4', '1', '1', '3', '5', '2', '1', '8', '4', '7', '7', '1', '9', '2', '1', '5', '4', '4', '4', '6', '1', '0', '5', '1', '/', '1', '0', '5', '5', '6', '9', '4', '3', '9', '7', '6', '8', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0251756Acc00300 : List (String × SourceJson) := (fragment0251756Field002Key00, fragment0251756Field002Value00) :: fragment0251756Acc00200
noncomputable def fragment0251756Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '3', '4', '7', '6', '4', '9', '2', '3', '2', '9', '6', '4', '6', '5', '6', '4', '1', '1', '3', '5', '2', '1', '8', '4', '7', '7', '1', '9', '2', '1', '5', '4', '4', '4', '6', '1', '0', '5', '1', '/', '1', '0', '5', '5', '6', '9', '4', '3', '9', '7', '6', '8', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0251756_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 419) (SourceJson.white (fragment0251756Field002Chars00 ++ tail)) fragment0251756Acc00200 =
      SourceJson.object (fuel + 418) (SourceJson.white tail) fragment0251756Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251756_object_field_002"
  err.flush

noncomputable def fragment0251756Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0251756Field003Value00 : SourceJson := .str (String.ofList ['4', '9', '2', '9', '0', '1', '6', '7', '/', '3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0251756Acc00400 : List (String × SourceJson) := (fragment0251756Field003Key00, fragment0251756Field003Value00) :: fragment0251756Acc00300
noncomputable def fragment0251756Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '4', '9', '2', '9', '0', '1', '6', '7', '/', '3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0251756_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 418) (SourceJson.white (fragment0251756Field003Chars00 ++ tail)) fragment0251756Acc00300 =
      SourceJson.object (fuel + 417) (SourceJson.white tail) fragment0251756Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251756_object_field_003"
  err.flush

noncomputable def fragment0251756Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0251756Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '2', '1', '7', '0', '3', '/', '1', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0251756Acc00500 : List (String × SourceJson) := (fragment0251756Field004Key00, fragment0251756Field004Value00) :: fragment0251756Acc00400
noncomputable def fragment0251756Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '2', '1', '7', '0', '3', '/', '1', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0251756_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 417) (SourceJson.white (fragment0251756Field004Chars00 ++ tail)) fragment0251756Acc00400 =
      SourceJson.object (fuel + 416) (SourceJson.white tail) fragment0251756Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251756_object_field_004"
  err.flush

noncomputable def fragment0251756Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0251756Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '0', '3', '0', '6', '0', '8', '9', '7', '8', '3', '2', '3', '4', '8', '1', '8', '3', '8', '9', '0', '3', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '1', '9', '0', '8', '0', '8', '1', '3', '7', '5', '2', '3', '6', '9', '3', '1', '1', '0', '3', '/', '2', '2', '6', '3', '4', '1', '7', '2', '3', '4', '7', '9', '3', '2', '5', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '3', '5', '6', '6', '5', '8', '5', '6', '0', '1', '0', '5', '2', '0', '4', '9', '2', '0', '2', '7', '/', '1', '1', '3', '1', '7', '0', '8', '6', '1', '7', '3', '9', '6', '6', '2', '6', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '7', '8', '2', '2', '7', '6', '8', '7', '8', '6', '3', '8', '3', '3', '2', '3', '0', '8', '7', '/', '5', '0', '2', '9', '8', '1', '6', '0', '7', '7', '3', '1', '8', '3', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '5', '2', '6', '8', '4', '8', '1', '5', '0', '2', '2', '5', '0', '0', '7', '5', '8', '1', '3', '/', '1', '5', '0', '8', '9', '4', '4', '8', '2', '3', '1', '9', '5', '5', '0', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '5', '1', '6', '1', '1', '9', '2', '0', '9', '0', '1', '0', '6', '0', '7', '2', '5', '3', '/', '2', '2', '6', '3', '4', '1', '7', '2', '3', '4', '7', '9', '3', '2', '5', '3', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '8', '7', '7', '5', '0', '6', '0', '2', '7', '0', '8', '5', '3', '2', '5', '9', '6', '4', '3', '/', '3', '6', '2', '1', '4', '6', '7', '5', '7', '5', '6', '6', '9', '2', '0', '4', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '0', '7', '3', '6', '6', '3', '7', '5', '8', '1', '8', '1', '9', '3', '0', '3', '3', '3', '5', '3', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '3', '5', '0', '6', '2', '1', '0', '8', '2', '7', '9', '7', '6', '5', '4', '5', '4', '2', '5', '3', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '9', '6', '8', '6', '1', '9', '4', '4', '1', '5', '7', '4', '4', '8', '3', '7', '9', '7', '7', '/', '2', '2', '6', '3', '4', '1', '7', '2', '3', '4', '7', '9', '3', '2', '5', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0251756Acc00600 : List (String × SourceJson) := (fragment0251756Field005Key00, fragment0251756Field005Value00) :: fragment0251756Acc00500
noncomputable def fragment0251756Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '3', '0', '6', '0', '8', '9', '7', '8', '3', '2', '3', '4', '8', '1', '8', '3', '8', '9', '0', '3', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '1', '9', '0', '8', '0', '8', '1', '3', '7', '5', '2', '3', '6', '9', '3', '1', '1', '0', '3', '/', '2', '2', '6', '3', '4', '1', '7', '2', '3', '4', '7', '9', '3', '2', '5', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '5', '6', '6', '5', '8', '5', '6', '0', '1', '0', '5', '2', '0', '4', '9', '2', '0', '2', '7', '/', '1', '1', '3', '1', '7', '0', '8', '6', '1', '7', '3', '9', '6', '6', '2', '6', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '7', '8', '2', '2', '7', '6', '8', '7', '8', '6', '3', '8', '3', '3', '2', '3', '0', '8', '7', '/', '5', '0', '2', '9', '8', '1', '6', '0', '7', '7', '3', '1', '8', '3', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '6', '5', '2', '6', '8', '4', '8', '1', '5', '0', '2', '2', '5', '0', '0', '7', '5', '8', '1', '3', '/', '1', '5', '0', '8', '9', '4', '4', '8', '2', '3', '1', '9', '5', '5', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '1', '6', '1', '1', '9', '2', '0', '9', '0', '1', '0', '6', '0', '7', '2', '5', '3', '/', '2', '2', '6', '3', '4', '1', '7', '2', '3', '4', '7', '9', '3', '2', '5', '3', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '6', '8', '7', '7', '5', '0', '6', '0', '2', '7', '0', '8', '5', '3', '2', '5', '9', '6', '4', '3', '/', '3', '6', '2', '1', '4', '6', '7', '5', '7', '5', '6', '6', '9', '2', '0', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '0', '7', '3', '6', '6', '3', '7', '5', '8', '1', '8', '1', '9', '3', '0', '3', '3', '3', '5', '3', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '3', '5', '0', '6', '2', '1', '0', '8', '2', '7', '9', '7', '6', '5', '4', '5', '4', '2', '5', '3', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '9', '6', '8', '6', '1', '9', '4', '4', '1', '5', '7', '4', '4', '8', '3', '7', '9', '7', '7', '/', '2', '2', '6', '3', '4', '1', '7', '2', '3', '4', '7', '9', '3', '2', '5', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0251756_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 416) (SourceJson.white (fragment0251756Field005Chars00 ++ tail)) fragment0251756Acc00500 =
      SourceJson.object (fuel + 415) (SourceJson.white tail) fragment0251756Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251756_object_field_005"
  err.flush

noncomputable def fragment0251756Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0251756Field006Value00 : SourceJson := .str (String.ofList ['2', '1', '1', '7', '7', '9', '5', '9', '2', '6', '5', '8', '2', '8', '9', '3', '7', '5', '1', '7', '2', '9', '5', '4', '2', '6', '5', '4', '7', '4', '0', '5', '0', '2', '1', '3', '0', '7', '7', '3', '1', '8', '9', '7', '5', '9', '8', '4', '2', '4', '2', '1', '8', '7', '5', '/', '6', '8', '3', '4', '6', '7', '4', '2', '6', '7', '8', '0', '9', '4', '5', '1', '8', '3', '6', '2', '2', '7', '2', '4', '1', '7', '2', '5', '2', '4', '6', '2', '0', '5', '1', '8', '1', '6', '4', '2', '5', '8', '9', '2', '2', '4', '5', '7', '1', '6', '9', '9', '1', '2', '4', '0', '1', '5', '4', '5', '9', '9', '7', '6', '5', '2', '9'])
noncomputable def fragment0251756Acc00700 : List (String × SourceJson) := (fragment0251756Field006Key00, fragment0251756Field006Value00) :: fragment0251756Acc00600
noncomputable def fragment0251756Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '1', '7', '7', '9', '5', '9', '2', '6', '5', '8', '2', '8', '9', '3', '7', '5', '1', '7', '2', '9', '5', '4', '2', '6', '5', '4', '7', '4', '0', '5', '0', '2', '1', '3', '0', '7', '7', '3', '1', '8', '9', '7', '5', '9', '8', '4', '2', '4', '2', '1', '8', '7', '5', '/', '6', '8', '3', '4', '6', '7', '4', '2', '6', '7', '8', '0', '9', '4', '5', '1', '8', '3', '6', '2', '2', '7', '2', '4', '1', '7', '2', '5', '2', '4', '6', '2', '0', '5', '1', '8', '1', '6', '4', '2', '5', '8', '9', '2', '2', '4', '5', '7', '1', '6', '9', '9', '1', '2', '4', '0', '1', '5', '4', '5', '9', '9', '7', '6', '5', '2', '9', '"', ',']

theorem object_fragment0251756_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 415) (SourceJson.white (fragment0251756Field006Chars00 ++ tail)) fragment0251756Acc00600 =
      SourceJson.object (fuel + 414) (SourceJson.white tail) fragment0251756Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251756_object_field_006"
  err.flush

noncomputable def fragment0251756Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0251756Field007Value00 : SourceJson := .str (String.ofList ['3', '9', '5', '6', '4', '6', '8', '0', '6', '0', '5', '8', '6', '1', '5', '3', '2', '8', '7', '7', '0', '8', '1', '8', '7', '4', '5', '5', '5', '7', '8', '9', '4', '2', '7', '5', '7', '2', '2', '8', '0', '5', '3', '6', '5', '7', '7', '5', '5', '1', '2', '0', '3', '2', '9', '5', '9', '2', '7', '0', '5', '6', '4', '0', '9', '8', '2', '8', '2', '1', '9', '7', '8', '4', '8', '4', '0', '7', '4', '8', '0', '1', '9', '1', '4', '0', '5', '2', '8', '0', '5', '8', '2', '2', '5', '5', '4', '4', '8', '4', '4', '9', '4', '7', '5', '0', '5', '7', '3', '0', '0', '5', '5', '2', '0', '4', '7', '7', '7', '1', '9', '1', '2', '8', '8', '5', '9', '6', '2', '7', '7', '1', '8', '9', '5', '9', '9', '2', '1', '8', '2', '6', '1', '8', '0', '1', '6', '2', '1', '5', '2', '1', '2', '6', '1', '4', '2', '9', '6', '3', '0', '9', '9', '5', '8', '2', '9', '1', '1', '6', '5', '8', '8', '0', '4', '6', '4', '5', '6', '1', '8', '8', '3', '6', '2', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '8', '2', '9', '4', '2', '0', '0', '9', '5', '9', '5', '2', '9', '3', '7', '1', '5', '7', '8', '1', '7', '7', '6', '0', '4', '0', '0', '2', '4', '7', '4', '4', '2', '2', '5', '1', '9', '2', '0', '7', '4', '9', '7', '4', '4', '5', '9', '3', '0', '2', '4', '1', '3', '2', '4', '7', '2', '6', '1', '0', '1', '5', '7', '4', '1', '3', '3', '9', '3', '6', '2', '8', '2', '3', '4', '7', '5', '7', '4', '2', '3', '3', '4', '0', '9', '4', '1', '6', '8', '2', '1', '0', '1', '6', '6', '5', '8', '2', '9', '1', '0', '2', '7', '4', '3', '0', '5', '2', '4', '2', '0', '3', '2', '6', '6', '8', '6', '0', '8', '2', '9', '9', '3', '6', '8', '0', '3', '5', '1', '0', '1', '4', '6', '6', '7', '2', '3', '0', '1', '1', '0', '7', '2', '9', '8', '5', '0', '6', '5', '2', '5', '5', '7', '8', '5', '1', '7', '1', '4', '7', '9', '0', '7', '9', '6', '1', '4', '2', '3', '4', '1', '1', '3', '0', '7', '3', '0', '8', '6', '0', '7', '7', '4', '6', '4', '9', '0', '8', '1', '2', '5', '6', '1', '3', '3', '1', '1', '5', '0', '3', '9', '6', '3', '5', '9', '5', '4', '6', '5', '1'])
noncomputable def fragment0251756Acc00800 : List (String × SourceJson) := (fragment0251756Field007Key00, fragment0251756Field007Value00) :: fragment0251756Acc00700
noncomputable def fragment0251756Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '9', '5', '6', '4', '6', '8', '0', '6', '0', '5', '8', '6', '1', '5', '3', '2', '8', '7', '7', '0', '8', '1', '8', '7', '4', '5', '5', '5', '7', '8', '9', '4', '2', '7', '5', '7', '2', '2', '8', '0', '5', '3', '6', '5', '7', '7', '5', '5', '1', '2', '0', '3', '2', '9', '5', '9', '2', '7', '0', '5', '6', '4', '0', '9', '8', '2', '8', '2', '1', '9', '7', '8', '4', '8', '4', '0', '7', '4', '8', '0', '1', '9', '1', '4', '0', '5', '2', '8', '0', '5', '8', '2', '2', '5', '5', '4', '4', '8', '4', '4', '9', '4', '7', '5', '0', '5', '7', '3', '0', '0', '5', '5', '2', '0', '4', '7', '7', '7', '1', '9', '1', '2', '8', '8', '5', '9', '6', '2', '7', '7', '1', '8', '9', '5', '9', '9', '2', '1', '8', '2', '6', '1', '8', '0', '1', '6', '2', '1', '5', '2', '1', '2', '6', '1', '4', '2', '9', '6', '3', '0', '9', '9', '5', '8', '2', '9', '1', '1', '6', '5', '8', '8', '0', '4', '6', '4', '5', '6', '1', '8', '8', '3', '6', '2', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '8', '2', '9', '4', '2', '0', '0', '9', '5', '9', '5', '2', '9', '3', '7', '1', '5', '7', '8', '1', '7', '7', '6', '0', '4', '0', '0', '2', '4', '7', '4', '4', '2', '2', '5', '1', '9', '2', '0', '7', '4', '9', '7', '4', '4', '5', '9', '3', '0', '2', '4', '1', '3', '2', '4', '7', '2', '6', '1', '0', '1', '5', '7', '4', '1', '3', '3', '9', '3', '6', '2', '8', '2', '3', '4', '7', '5', '7', '4', '2', '3', '3', '4', '0', '9', '4', '1', '6', '8', '2', '1', '0', '1', '6', '6', '5', '8', '2', '9', '1', '0', '2', '7', '4', '3', '0', '5', '2', '4', '2', '0', '3', '2', '6', '6', '8', '6', '0', '8', '2', '9', '9', '3', '6', '8', '0', '3', '5', '1', '0', '1', '4', '6', '6', '7', '2', '3', '0', '1', '1', '0', '7', '2', '9', '8', '5', '0', '6', '5', '2', '5', '5', '7', '8', '5', '1', '7', '1', '4', '7', '9', '0', '7', '9', '6', '1', '4', '2', '3', '4', '1', '1', '3', '0', '7', '3', '0', '8', '6', '0', '7', '7', '4', '6', '4', '9', '0', '8', '1', '2', '5', '6', '1', '3', '3', '1', '1', '5', '0', '3', '9', '6', '3', '5', '9', '5', '4', '6', '5', '1', '"', ',']

theorem object_fragment0251756_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 414) (SourceJson.white (fragment0251756Field007Chars00 ++ tail)) fragment0251756Acc00700 =
      SourceJson.object (fuel + 413) (SourceJson.white tail) fragment0251756Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251756_object_field_007"
  err.flush

noncomputable def fragment0251756Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0251756Field008Value00 : SourceJson := .str (String.ofList ['2', '4', '5', '4', '9', '6', '8', '1', '9', '9', '9', '2', '7', '5', '9', '9', '3'])
noncomputable def fragment0251756Acc00900 : List (String × SourceJson) := (fragment0251756Field008Key00, fragment0251756Field008Value00) :: fragment0251756Acc00800
noncomputable def fragment0251756Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '5', '4', '9', '6', '8', '1', '9', '9', '9', '2', '7', '5', '9', '9', '3', '"', ',']

theorem object_fragment0251756_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 413) (SourceJson.white (fragment0251756Field008Chars00 ++ tail)) fragment0251756Acc00800 =
      SourceJson.object (fuel + 412) (SourceJson.white tail) fragment0251756Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251756_object_field_008"
  err.flush

noncomputable def fragment0251756Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0251756Field009Value00 : SourceJson := .str (String.ofList ['8', '1', '8', '5', '6', '7', '0', '0', '6', '5', '7', '5', '9', '9', '6', '2', '0'])
noncomputable def fragment0251756Acc01000 : List (String × SourceJson) := (fragment0251756Field009Key00, fragment0251756Field009Value00) :: fragment0251756Acc00900
noncomputable def fragment0251756Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '1', '8', '5', '6', '7', '0', '0', '6', '5', '7', '5', '9', '9', '6', '2', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0251756_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 412) (SourceJson.white (fragment0251756Field009Chars00 ++ tail)) fragment0251756Acc00900 =
      .ok (.obj (fragment0251756Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0251756_object_field_009"
  err.flush

noncomputable def fragment0251756Chars : List Char := '{' :: (fragment0251756Field000Chars00 ++ fragment0251756Field001Chars00 ++ fragment0251756Field002Chars00 ++ fragment0251756Field003Chars00 ++ fragment0251756Field004Chars00 ++ fragment0251756Field005Chars00 ++ fragment0251756Field006Chars00 ++ fragment0251756Field007Chars00 ++ fragment0251756Field008Chars00 ++ fragment0251756Field009Chars00)
noncomputable def fragment0251756Value : SourceJson := .obj (fragment0251756Acc01000.reverse)

theorem value_fragment0251756 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 422) (fragment0251756Chars ++ tail) =
      .ok (fragment0251756Value, tail) := by
  have hinput : fragment0251756Chars ++ tail = '{' :: (fragment0251756Field000Chars00 ++ (fragment0251756Field001Chars00 ++ (fragment0251756Field002Chars00 ++ (fragment0251756Field003Chars00 ++ (fragment0251756Field004Chars00 ++ (fragment0251756Field005Chars00 ++ (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0251756Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 422) (fragment0251756Chars ++ tail) =
        SourceJson.value (fuel + 422) ('{' :: (fragment0251756Field000Chars00 ++ (fragment0251756Field001Chars00 ++ (fragment0251756Field002Chars00 ++ (fragment0251756Field003Chars00 ++ (fragment0251756Field004Chars00 ++ (fragment0251756Field005Chars00 ++ (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 422)) hinput
    _ = SourceJson.object (fuel + 421) (SourceJson.white (fragment0251756Field000Chars00 ++ (fragment0251756Field001Chars00 ++ (fragment0251756Field002Chars00 ++ (fragment0251756Field003Chars00 ++ (fragment0251756Field004Chars00 ++ (fragment0251756Field005Chars00 ++ (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail)))))))))))) fragment0251756Acc00000 := by rfl
    _ = SourceJson.object (fuel + 420) (SourceJson.white (fragment0251756Field001Chars00 ++ (fragment0251756Field002Chars00 ++ (fragment0251756Field003Chars00 ++ (fragment0251756Field004Chars00 ++ (fragment0251756Field005Chars00 ++ (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail))))))))))) fragment0251756Acc00100 := object_fragment0251756_field_000 fuel (fragment0251756Field001Chars00 ++ (fragment0251756Field002Chars00 ++ (fragment0251756Field003Chars00 ++ (fragment0251756Field004Chars00 ++ (fragment0251756Field005Chars00 ++ (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 419) (SourceJson.white (fragment0251756Field002Chars00 ++ (fragment0251756Field003Chars00 ++ (fragment0251756Field004Chars00 ++ (fragment0251756Field005Chars00 ++ (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail)))))))))) fragment0251756Acc00200 := object_fragment0251756_field_001 fuel (fragment0251756Field002Chars00 ++ (fragment0251756Field003Chars00 ++ (fragment0251756Field004Chars00 ++ (fragment0251756Field005Chars00 ++ (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 418) (SourceJson.white (fragment0251756Field003Chars00 ++ (fragment0251756Field004Chars00 ++ (fragment0251756Field005Chars00 ++ (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail))))))))) fragment0251756Acc00300 := object_fragment0251756_field_002 fuel (fragment0251756Field003Chars00 ++ (fragment0251756Field004Chars00 ++ (fragment0251756Field005Chars00 ++ (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 417) (SourceJson.white (fragment0251756Field004Chars00 ++ (fragment0251756Field005Chars00 ++ (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail)))))))) fragment0251756Acc00400 := object_fragment0251756_field_003 fuel (fragment0251756Field004Chars00 ++ (fragment0251756Field005Chars00 ++ (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 416) (SourceJson.white (fragment0251756Field005Chars00 ++ (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail))))))) fragment0251756Acc00500 := object_fragment0251756_field_004 fuel (fragment0251756Field005Chars00 ++ (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 415) (SourceJson.white (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail)))))) fragment0251756Acc00600 := object_fragment0251756_field_005 fuel (fragment0251756Field006Chars00 ++ (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 414) (SourceJson.white (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail))))) fragment0251756Acc00700 := object_fragment0251756_field_006 fuel (fragment0251756Field007Chars00 ++ (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 413) (SourceJson.white (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail)))) fragment0251756Acc00800 := object_fragment0251756_field_007 fuel (fragment0251756Field008Chars00 ++ (fragment0251756Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 412) (SourceJson.white (fragment0251756Field009Chars00 ++ (tail))) fragment0251756Acc00900 := object_fragment0251756_field_008 fuel (fragment0251756Field009Chars00 ++ (tail))
    _ = .ok (fragment0251756Value, tail) := object_fragment0251756_field_009 fuel (tail)

noncomputable def fragment0253745Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0253745Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0253745Field000Value00 : SourceJson := .number (String.ofList ['6', '8'])
noncomputable def fragment0253745Acc00100 : List (String × SourceJson) := (fragment0253745Field000Key00, fragment0253745Field000Value00) :: fragment0253745Acc00000
noncomputable def fragment0253745Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '8', ',']

theorem object_fragment0253745_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 474) (SourceJson.white (fragment0253745Field000Chars00 ++ tail)) fragment0253745Acc00000 =
      SourceJson.object (fuel + 473) (SourceJson.white tail) fragment0253745Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253745_object_field_000"
  err.flush

noncomputable def fragment0253745Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0253745Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0253745Acc00200 : List (String × SourceJson) := (fragment0253745Field001Key00, fragment0253745Field001Value00) :: fragment0253745Acc00100
noncomputable def fragment0253745Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0253745_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 473) (SourceJson.white (fragment0253745Field001Chars00 ++ tail)) fragment0253745Acc00100 =
      SourceJson.object (fuel + 472) (SourceJson.white tail) fragment0253745Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253745_object_field_001"
  err.flush

noncomputable def fragment0253745Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0253745Field002Value00 : SourceJson := .str (String.ofList ['3', '3', '1', '4', '3', '0', '6', '2', '2', '9', '7', '8', '5', '9', '1', '0', '9', '6', '4', '3', '6', '6', '8', '8', '1', '1', '8', '3', '2', '5', '2', '6', '5', '4', '8', '3', '6', '5', '9', '/', '7', '2', '9', '5', '5', '4', '0', '7', '0', '3', '8', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0253745Acc00300 : List (String × SourceJson) := (fragment0253745Field002Key00, fragment0253745Field002Value00) :: fragment0253745Acc00200
noncomputable def fragment0253745Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '3', '1', '4', '3', '0', '6', '2', '2', '9', '7', '8', '5', '9', '1', '0', '9', '6', '4', '3', '6', '6', '8', '8', '1', '1', '8', '3', '2', '5', '2', '6', '5', '4', '8', '3', '6', '5', '9', '/', '7', '2', '9', '5', '5', '4', '0', '7', '0', '3', '8', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0253745_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 472) (SourceJson.white (fragment0253745Field002Chars00 ++ tail)) fragment0253745Acc00200 =
      SourceJson.object (fuel + 471) (SourceJson.white tail) fragment0253745Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253745_object_field_002"
  err.flush

noncomputable def fragment0253745Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0253745Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0253745Acc00400 : List (String × SourceJson) := (fragment0253745Field003Key00, fragment0253745Field003Value00) :: fragment0253745Acc00300
noncomputable def fragment0253745Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0253745_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 471) (SourceJson.white (fragment0253745Field003Chars00 ++ tail)) fragment0253745Acc00300 =
      SourceJson.object (fuel + 470) (SourceJson.white tail) fragment0253745Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253745_object_field_003"
  err.flush

noncomputable def fragment0253745Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0253745Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0253745Acc00500 : List (String × SourceJson) := (fragment0253745Field004Key00, fragment0253745Field004Value00) :: fragment0253745Acc00400
noncomputable def fragment0253745Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0253745_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 470) (SourceJson.white (fragment0253745Field004Chars00 ++ tail)) fragment0253745Acc00400 =
      SourceJson.object (fuel + 469) (SourceJson.white tail) fragment0253745Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253745_object_field_004"
  err.flush

noncomputable def fragment0253745Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0253745Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '0', '8', '5', '5', '2', '4', '3', '9', '1', '4', '9', '5', '0', '9', '2', '6', '0', '6', '2', '7', '0', '1', '3', '/', '1', '8', '4', '7', '5', '1', '4', '1', '6', '0', '2', '5', '0', '0', '0', '3', '5', '8', '1', '8', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '1', '0', '2', '2', '6', '4', '1', '7', '8', '0', '9', '2', '9', '3', '9', '8', '4', '1', '3', '0', '9', '/', '9', '8', '2', '0', '6', '7', '3', '2', '7', '7', '0', '7', '6', '4', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '0', '4', '0', '6', '5', '4', '6', '6', '4', '9', '8', '2', '8', '4', '6', '9', '8', '1', '7', '8', '3', '1', '1', '/', '5', '1', '4', '0', '9', '0', '8', '9', '6', '7', '6', '5', '2', '1', '8', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '0', '5', '6', '3', '0', '7', '7', '4', '1', '6', '5', '3', '4', '9', '3', '3', '0', '1', '8', '6', '7', '1', '4', '7', '/', '6', '5', '6', '8', '9', '3', '9', '2', '3', '6', '4', '4', '4', '4', '5', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '0', '6', '1', '8', '3', '3', '5', '2', '1', '4', '6', '7', '4', '2', '4', '7', '8', '0', '1', '0', '6', '4', '8', '1', '/', '1', '9', '7', '0', '6', '8', '1', '7', '7', '0', '9', '3', '3', '3', '3', '7', '1', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '4', '4', '3', '4', '9', '1', '3', '5', '3', '4', '6', '0', '5', '2', '6', '7', '4', '2', '2', '4', '5', '3', '1', '/', '5', '3', '7', '4', '5', '8', '6', '6', '4', '8', '0', '0', '0', '0', '1', '0', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '4', '6', '1', '8', '7', '9', '8', '4', '4', '7', '9', '7', '6', '5', '9', '2', '9', '6', '9', '1', '6', '8', '3', '/', '5', '3', '7', '4', '5', '8', '6', '6', '4', '8', '0', '0', '0', '0', '1', '0', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '2', '7', '2', '4', '2', '5', '0', '7', '4', '9', '8', '9', '7', '3', '6', '2', '0', '0', '4', '1', '1', '/', '6', '7', '1', '8', '2', '3', '3', '3', '1', '0', '0', '0', '0', '0', '1', '3', '0', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '9', '8', '2', '2', '7', '3', '8', '5', '0', '3', '5', '3', '4', '8', '5', '0', '6', '9', '7', '6', '3', '/', '3', '3', '5', '9', '1', '1', '6', '6', '5', '5', '0', '0', '0', '0', '0', '6', '5', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '0', '4', '9', '3', '5', '4', '3', '9', '5', '9', '1', '2', '2', '3', '8', '3', '1', '3', '6', '2', '3', '/', '9', '8', '2', '0', '6', '7', '3', '2', '7', '7', '0', '7', '6', '4', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0253745Acc00600 : List (String × SourceJson) := (fragment0253745Field005Key00, fragment0253745Field005Value00) :: fragment0253745Acc00500
noncomputable def fragment0253745Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '8', '5', '5', '2', '4', '3', '9', '1', '4', '9', '5', '0', '9', '2', '6', '0', '6', '2', '7', '0', '1', '3', '/', '1', '8', '4', '7', '5', '1', '4', '1', '6', '0', '2', '5', '0', '0', '0', '3', '5', '8', '1', '8', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '1', '0', '2', '2', '6', '4', '1', '7', '8', '0', '9', '2', '9', '3', '9', '8', '4', '1', '3', '0', '9', '/', '9', '8', '2', '0', '6', '7', '3', '2', '7', '7', '0', '7', '6', '4', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '4', '0', '6', '5', '4', '6', '6', '4', '9', '8', '2', '8', '4', '6', '9', '8', '1', '7', '8', '3', '1', '1', '/', '5', '1', '4', '0', '9', '0', '8', '9', '6', '7', '6', '5', '2', '1', '8', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '5', '6', '3', '0', '7', '7', '4', '1', '6', '5', '3', '4', '9', '3', '3', '0', '1', '8', '6', '7', '1', '4', '7', '/', '6', '5', '6', '8', '9', '3', '9', '2', '3', '6', '4', '4', '4', '4', '5', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '0', '6', '1', '8', '3', '3', '5', '2', '1', '4', '6', '7', '4', '2', '4', '7', '8', '0', '1', '0', '6', '4', '8', '1', '/', '1', '9', '7', '0', '6', '8', '1', '7', '7', '0', '9', '3', '3', '3', '3', '7', '1', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '4', '4', '3', '4', '9', '1', '3', '5', '3', '4', '6', '0', '5', '2', '6', '7', '4', '2', '2', '4', '5', '3', '1', '/', '5', '3', '7', '4', '5', '8', '6', '6', '4', '8', '0', '0', '0', '0', '1', '0', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '4', '6', '1', '8', '7', '9', '8', '4', '4', '7', '9', '7', '6', '5', '9', '2', '9', '6', '9', '1', '6', '8', '3', '/', '5', '3', '7', '4', '5', '8', '6', '6', '4', '8', '0', '0', '0', '0', '1', '0', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '1', '2', '7', '2', '4', '2', '5', '0', '7', '4', '9', '8', '9', '7', '3', '6', '2', '0', '0', '4', '1', '1', '/', '6', '7', '1', '8', '2', '3', '3', '3', '1', '0', '0', '0', '0', '0', '1', '3', '0', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '9', '8', '2', '2', '7', '3', '8', '5', '0', '3', '5', '3', '4', '8', '5', '0', '6', '9', '7', '6', '3', '/', '3', '3', '5', '9', '1', '1', '6', '6', '5', '5', '0', '0', '0', '0', '0', '6', '5', '1', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '0', '4', '9', '3', '5', '4', '3', '9', '5', '9', '1', '2', '2', '3', '8', '3', '1', '3', '6', '2', '3', '/', '9', '8', '2', '0', '6', '7', '3', '2', '7', '7', '0', '7', '6', '4', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0253745_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 469) (SourceJson.white (fragment0253745Field005Chars00 ++ tail)) fragment0253745Acc00500 =
      SourceJson.object (fuel + 468) (SourceJson.white tail) fragment0253745Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253745_object_field_005"
  err.flush

noncomputable def fragment0253745Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0253745Field006Value00 : SourceJson := .str (String.ofList ['6', '3', '4', '4', '8', '5', '7', '5', '5', '0', '3', '9', '0', '4', '6', '5', '6', '0', '1', '1', '9', '8', '8', '4', '8', '6', '2', '6', '3', '7', '0', '0', '9', '8', '9', '2', '1', '2', '1', '5', '7', '8', '5', '7', '3', '0', '1', '0', '2', '8', '1', '6', '6', '6', '2', '5', '/', '3', '0', '7', '1', '5', '2', '1', '1', '2', '9', '7', '4', '6', '7', '9', '8', '6', '3', '8', '7', '8', '9', '1', '1', '3', '7', '2', '1', '6', '3', '3', '6', '0', '8', '3', '3', '9', '1', '5', '9', '4', '3', '3', '5', '9', '7', '2', '5', '8', '7', '9', '0', '4', '9', '0', '7', '1', '3', '1', '2', '3', '3', '5', '7', '1', '5', '9', '9', '3', '6'])
noncomputable def fragment0253745Acc00700 : List (String × SourceJson) := (fragment0253745Field006Key00, fragment0253745Field006Value00) :: fragment0253745Acc00600
noncomputable def fragment0253745Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '3', '4', '4', '8', '5', '7', '5', '5', '0', '3', '9', '0', '4', '6', '5', '6', '0', '1', '1', '9', '8', '8', '4', '8', '6', '2', '6', '3', '7', '0', '0', '9', '8', '9', '2', '1', '2', '1', '5', '7', '8', '5', '7', '3', '0', '1', '0', '2', '8', '1', '6', '6', '6', '2', '5', '/', '3', '0', '7', '1', '5', '2', '1', '1', '2', '9', '7', '4', '6', '7', '9', '8', '6', '3', '8', '7', '8', '9', '1', '1', '3', '7', '2', '1', '6', '3', '3', '6', '0', '8', '3', '3', '9', '1', '5', '9', '4', '3', '3', '5', '9', '7', '2', '5', '8', '7', '9', '0', '4', '9', '0', '7', '1', '3', '1', '2', '3', '3', '5', '7', '1', '5', '9', '9', '3', '6', '"', ',']

theorem object_fragment0253745_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 468) (SourceJson.white (fragment0253745Field006Chars00 ++ tail)) fragment0253745Acc00600 =
      SourceJson.object (fuel + 467) (SourceJson.white tail) fragment0253745Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253745_object_field_006"
  err.flush

noncomputable def fragment0253745Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0253745Field007Value00 : SourceJson := .str (String.ofList ['2', '8', '1', '4', '9', '4', '8', '0', '4', '0', '5', '6', '4', '8', '0', '2', '1', '4', '1', '0', '1', '4', '1', '7', '4', '8', '7', '6', '9', '7', '9', '9', '6', '4', '1', '6', '9', '0', '3', '3', '4', '4', '9', '8', '2', '1', '9', '2', '9', '9', '5', '3', '7', '8', '3', '1', '6', '2', '6', '6', '5', '0', '9', '3', '6', '6', '7', '2', '3', '1', '8', '5', '0', '6', '6', '1', '5', '7', '4', '9', '6', '8', '5', '1', '8', '1', '3', '2', '4', '0', '4', '1', '8', '3', '3', '4', '1', '8', '9', '2', '7', '7', '4', '2', '5', '9', '2', '9', '0', '8', '9', '5', '8', '5', '5', '2', '5', '7', '9', '8', '6', '6', '0', '9', '8', '9', '8', '8', '0', '4', '6', '7', '2', '1', '6', '9', '0', '6', '4', '4', '3', '7', '0', '8', '4', '9', '6', '4', '9', '1', '6', '0', '3', '5', '0', '4', '5', '6', '2', '2', '7', '2', '5', '6', '2', '7', '6', '2', '9', '1', '8', '7', '5', '4', '3', '5', '0', '2', '9', '4', '7', '3', '9', '3', '2', '5', '7', '2', '6', '2', '1', '5', '4', '5', '9', '3', '0', '1', '2', '8', '0', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '9', '5', '6', '7', '7', '5', '8', '2', '3', '8', '3', '7', '2', '7', '9', '1', '2', '1', '8', '9', '6', '8', '6', '0', '4', '3', '3', '8', '0', '0', '9', '4', '2', '4', '2', '2', '0', '8', '9', '8', '8', '4', '9', '9', '5', '3', '8', '3', '1', '3', '5', '3', '2', '9', '8', '0', '2', '6', '4', '0', '2', '9', '9', '6', '6', '8', '0', '5', '5', '9', '4', '3', '0', '7', '7', '4', '4', '9', '6', '7', '5', '9', '0', '5', '3', '1', '4', '6', '3', '8', '8', '1', '8', '6', '2', '5', '5', '2', '5', '1', '8', '1', '4', '4', '4', '5', '1', '6', '3', '1', '3', '7', '9', '2', '3', '4', '7', '5', '0', '7', '6', '0', '3', '8', '5', '2', '9', '6', '2', '1', '2', '8', '3', '0', '8', '5', '7', '8', '9', '6', '4', '3', '7', '5', '4', '1', '1', '2', '3', '6', '1', '7', '2', '7', '1', '2', '0', '6', '6', '1', '7', '4', '2', '9', '4', '4', '2', '3', '2', '9', '7', '0', '4', '1', '7', '0', '4', '0', '8', '0', '8', '3', '1', '0', '6', '0', '0', '5', '0', '3', '6', '9', '1', '9', '5', '7', '3', '2', '5', '2', '1', '0', '6', '4', '7', '9', '5', '7', '3', '7', '8', '2', '9', '6', '0', '3', '9', '4', '5', '9', '3', '4', '7', '9', '4', '8', '2', '8', '9', '4', '5', '2', '2', '4', '3', '9', '3'])
noncomputable def fragment0253745Acc00800 : List (String × SourceJson) := (fragment0253745Field007Key00, fragment0253745Field007Value00) :: fragment0253745Acc00700
noncomputable def fragment0253745Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '8', '1', '4', '9', '4', '8', '0', '4', '0', '5', '6', '4', '8', '0', '2', '1', '4', '1', '0', '1', '4', '1', '7', '4', '8', '7', '6', '9', '7', '9', '9', '6', '4', '1', '6', '9', '0', '3', '3', '4', '4', '9', '8', '2', '1', '9', '2', '9', '9', '5', '3', '7', '8', '3', '1', '6', '2', '6', '6', '5', '0', '9', '3', '6', '6', '7', '2', '3', '1', '8', '5', '0', '6', '6', '1', '5', '7', '4', '9', '6', '8', '5', '1', '8', '1', '3', '2', '4', '0', '4', '1', '8', '3', '3', '4', '1', '8', '9', '2', '7', '7', '4', '2', '5', '9', '2', '9', '0', '8', '9', '5', '8', '5', '5', '2', '5', '7', '9', '8', '6', '6', '0', '9', '8', '9', '8', '8', '0', '4', '6', '7', '2', '1', '6', '9', '0', '6', '4', '4', '3', '7', '0', '8', '4', '9', '6', '4', '9', '1', '6', '0', '3', '5', '0', '4', '5', '6', '2', '2', '7', '2', '5', '6', '2', '7', '6', '2', '9', '1', '8', '7', '5', '4', '3', '5', '0', '2', '9', '4', '7', '3', '9', '3', '2', '5', '7', '2', '6', '2', '1', '5', '4', '5', '9', '3', '0', '1', '2', '8', '0', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '9', '5', '6', '7', '7', '5', '8', '2', '3', '8', '3', '7', '2', '7', '9', '1', '2', '1', '8', '9', '6', '8', '6', '0', '4', '3', '3', '8', '0', '0', '9', '4', '2', '4', '2', '2', '0', '8', '9', '8', '8', '4', '9', '9', '5', '3', '8', '3', '1', '3', '5', '3', '2', '9', '8', '0', '2', '6', '4', '0', '2', '9', '9', '6', '6', '8', '0', '5', '5', '9', '4', '3', '0', '7', '7', '4', '4', '9', '6', '7', '5', '9', '0', '5', '3', '1', '4', '6', '3', '8', '8', '1', '8', '6', '2', '5', '5', '2', '5', '1', '8', '1', '4', '4', '4', '5', '1', '6', '3', '1', '3', '7', '9', '2', '3', '4', '7', '5', '0', '7', '6', '0', '3', '8', '5', '2', '9', '6', '2', '1', '2', '8', '3', '0', '8', '5', '7', '8', '9', '6', '4', '3', '7', '5', '4', '1', '1', '2', '3', '6', '1', '7', '2', '7', '1', '2', '0', '6', '6', '1', '7', '4', '2', '9', '4', '4', '2', '3', '2', '9', '7', '0', '4', '1', '7', '0', '4', '0', '8', '0', '8', '3', '1', '0', '6', '0', '0', '5', '0', '3', '6', '9', '1', '9', '5', '7', '3', '2', '5', '2', '1', '0', '6', '4', '7', '9', '5', '7', '3', '7', '8', '2', '9', '6', '0', '3', '9', '4', '5', '9', '3', '4', '7', '9', '4', '8', '2', '8', '9', '4', '5', '2', '2', '4', '3', '9', '3', '"', ',']

theorem object_fragment0253745_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 467) (SourceJson.white (fragment0253745Field007Chars00 ++ tail)) fragment0253745Acc00700 =
      SourceJson.object (fuel + 466) (SourceJson.white tail) fragment0253745Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253745_object_field_007"
  err.flush

noncomputable def fragment0253745Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0253745Field008Value00 : SourceJson := .str (String.ofList ['1', '6', '3', '6', '6', '2', '0', '3', '7', '1', '1', '3', '7', '1', '9', '0'])
noncomputable def fragment0253745Acc00900 : List (String × SourceJson) := (fragment0253745Field008Key00, fragment0253745Field008Value00) :: fragment0253745Acc00800
noncomputable def fragment0253745Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '3', '6', '6', '2', '0', '3', '7', '1', '1', '3', '7', '1', '9', '0', '"', ',']

theorem object_fragment0253745_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 466) (SourceJson.white (fragment0253745Field008Chars00 ++ tail)) fragment0253745Acc00800 =
      SourceJson.object (fuel + 465) (SourceJson.white tail) fragment0253745Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253745_object_field_008"
  err.flush

noncomputable def fragment0253745Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0253745Field009Value00 : SourceJson := .str (String.ofList ['4', '4', '9', '9', '3', '5', '9', '4', '3', '7', '5', '3', '1', '0', '1', '0'])
noncomputable def fragment0253745Acc01000 : List (String × SourceJson) := (fragment0253745Field009Key00, fragment0253745Field009Value00) :: fragment0253745Acc00900
noncomputable def fragment0253745Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '4', '9', '9', '3', '5', '9', '4', '3', '7', '5', '3', '1', '0', '1', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0253745_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 465) (SourceJson.white (fragment0253745Field009Chars00 ++ tail)) fragment0253745Acc00900 =
      .ok (.obj (fragment0253745Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253745_object_field_009"
  err.flush

noncomputable def fragment0253745Chars : List Char := '{' :: (fragment0253745Field000Chars00 ++ fragment0253745Field001Chars00 ++ fragment0253745Field002Chars00 ++ fragment0253745Field003Chars00 ++ fragment0253745Field004Chars00 ++ fragment0253745Field005Chars00 ++ fragment0253745Field006Chars00 ++ fragment0253745Field007Chars00 ++ fragment0253745Field008Chars00 ++ fragment0253745Field009Chars00)
noncomputable def fragment0253745Value : SourceJson := .obj (fragment0253745Acc01000.reverse)

theorem value_fragment0253745 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 475) (fragment0253745Chars ++ tail) =
      .ok (fragment0253745Value, tail) := by
  have hinput : fragment0253745Chars ++ tail = '{' :: (fragment0253745Field000Chars00 ++ (fragment0253745Field001Chars00 ++ (fragment0253745Field002Chars00 ++ (fragment0253745Field003Chars00 ++ (fragment0253745Field004Chars00 ++ (fragment0253745Field005Chars00 ++ (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0253745Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 475) (fragment0253745Chars ++ tail) =
        SourceJson.value (fuel + 475) ('{' :: (fragment0253745Field000Chars00 ++ (fragment0253745Field001Chars00 ++ (fragment0253745Field002Chars00 ++ (fragment0253745Field003Chars00 ++ (fragment0253745Field004Chars00 ++ (fragment0253745Field005Chars00 ++ (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 475)) hinput
    _ = SourceJson.object (fuel + 474) (SourceJson.white (fragment0253745Field000Chars00 ++ (fragment0253745Field001Chars00 ++ (fragment0253745Field002Chars00 ++ (fragment0253745Field003Chars00 ++ (fragment0253745Field004Chars00 ++ (fragment0253745Field005Chars00 ++ (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail)))))))))))) fragment0253745Acc00000 := by rfl
    _ = SourceJson.object (fuel + 473) (SourceJson.white (fragment0253745Field001Chars00 ++ (fragment0253745Field002Chars00 ++ (fragment0253745Field003Chars00 ++ (fragment0253745Field004Chars00 ++ (fragment0253745Field005Chars00 ++ (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail))))))))))) fragment0253745Acc00100 := object_fragment0253745_field_000 fuel (fragment0253745Field001Chars00 ++ (fragment0253745Field002Chars00 ++ (fragment0253745Field003Chars00 ++ (fragment0253745Field004Chars00 ++ (fragment0253745Field005Chars00 ++ (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 472) (SourceJson.white (fragment0253745Field002Chars00 ++ (fragment0253745Field003Chars00 ++ (fragment0253745Field004Chars00 ++ (fragment0253745Field005Chars00 ++ (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail)))))))))) fragment0253745Acc00200 := object_fragment0253745_field_001 fuel (fragment0253745Field002Chars00 ++ (fragment0253745Field003Chars00 ++ (fragment0253745Field004Chars00 ++ (fragment0253745Field005Chars00 ++ (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 471) (SourceJson.white (fragment0253745Field003Chars00 ++ (fragment0253745Field004Chars00 ++ (fragment0253745Field005Chars00 ++ (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail))))))))) fragment0253745Acc00300 := object_fragment0253745_field_002 fuel (fragment0253745Field003Chars00 ++ (fragment0253745Field004Chars00 ++ (fragment0253745Field005Chars00 ++ (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 470) (SourceJson.white (fragment0253745Field004Chars00 ++ (fragment0253745Field005Chars00 ++ (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail)))))))) fragment0253745Acc00400 := object_fragment0253745_field_003 fuel (fragment0253745Field004Chars00 ++ (fragment0253745Field005Chars00 ++ (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 469) (SourceJson.white (fragment0253745Field005Chars00 ++ (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail))))))) fragment0253745Acc00500 := object_fragment0253745_field_004 fuel (fragment0253745Field005Chars00 ++ (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 468) (SourceJson.white (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail)))))) fragment0253745Acc00600 := object_fragment0253745_field_005 fuel (fragment0253745Field006Chars00 ++ (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 467) (SourceJson.white (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail))))) fragment0253745Acc00700 := object_fragment0253745_field_006 fuel (fragment0253745Field007Chars00 ++ (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 466) (SourceJson.white (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail)))) fragment0253745Acc00800 := object_fragment0253745_field_007 fuel (fragment0253745Field008Chars00 ++ (fragment0253745Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 465) (SourceJson.white (fragment0253745Field009Chars00 ++ (tail))) fragment0253745Acc00900 := object_fragment0253745_field_008 fuel (fragment0253745Field009Chars00 ++ (tail))
    _ = .ok (fragment0253745Value, tail) := object_fragment0253745_field_009 fuel (tail)

noncomputable def fragment0255834Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0255834Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0255834Field000Value00 : SourceJson := .number (String.ofList ['6', '9'])
noncomputable def fragment0255834Acc00100 : List (String × SourceJson) := (fragment0255834Field000Key00, fragment0255834Field000Value00) :: fragment0255834Acc00000
noncomputable def fragment0255834Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '9', ',']

theorem object_fragment0255834_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 402) (SourceJson.white (fragment0255834Field000Chars00 ++ tail)) fragment0255834Acc00000 =
      SourceJson.object (fuel + 401) (SourceJson.white tail) fragment0255834Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0255834_object_field_000"
  err.flush

noncomputable def fragment0255834Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0255834Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0255834Acc00200 : List (String × SourceJson) := (fragment0255834Field001Key00, fragment0255834Field001Value00) :: fragment0255834Acc00100
noncomputable def fragment0255834Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0255834_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 401) (SourceJson.white (fragment0255834Field001Chars00 ++ tail)) fragment0255834Acc00100 =
      SourceJson.object (fuel + 400) (SourceJson.white tail) fragment0255834Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0255834_object_field_001"
  err.flush

noncomputable def fragment0255834Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0255834Field002Value00 : SourceJson := .str (String.ofList ['2', '3', '7', '3', '8', '0', '9', '6', '4', '4', '9', '8', '1', '7', '4', '4', '9', '2', '1', '8', '8', '3', '6', '8', '8', '8', '9', '7', '3', '3', '7', '0', '6', '4', '5', '9', '3', '9', '4', '7', '1', '/', '4', '3', '7', '7', '3', '2', '4', '4', '2', '2', '3', '0', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0255834Acc00300 : List (String × SourceJson) := (fragment0255834Field002Key00, fragment0255834Field002Value00) :: fragment0255834Acc00200
noncomputable def fragment0255834Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '3', '7', '3', '8', '0', '9', '6', '4', '4', '9', '8', '1', '7', '4', '4', '9', '2', '1', '8', '8', '3', '6', '8', '8', '8', '9', '7', '3', '3', '7', '0', '6', '4', '5', '9', '3', '9', '4', '7', '1', '/', '4', '3', '7', '7', '3', '2', '4', '4', '2', '2', '3', '0', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0255834_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0255834Field002Chars00 ++ tail)) fragment0255834Acc00200 =
      SourceJson.object (fuel + 399) (SourceJson.white tail) fragment0255834Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0255834_object_field_002"
  err.flush

noncomputable def fragment0255834Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0255834Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0255834Acc00400 : List (String × SourceJson) := (fragment0255834Field003Key00, fragment0255834Field003Value00) :: fragment0255834Acc00300
noncomputable def fragment0255834Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0255834_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 399) (SourceJson.white (fragment0255834Field003Chars00 ++ tail)) fragment0255834Acc00300 =
      SourceJson.object (fuel + 398) (SourceJson.white tail) fragment0255834Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0255834_object_field_003"
  err.flush

noncomputable def fragment0255834Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0255834Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0255834Acc00500 : List (String × SourceJson) := (fragment0255834Field004Key00, fragment0255834Field004Value00) :: fragment0255834Acc00400
noncomputable def fragment0255834Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0255834_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 398) (SourceJson.white (fragment0255834Field004Chars00 ++ tail)) fragment0255834Acc00400 =
      SourceJson.object (fuel + 397) (SourceJson.white tail) fragment0255834Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0255834_object_field_004"
  err.flush

noncomputable def fragment0255834Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0255834Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '1', '7', '4', '8', '1', '4', '7', '4', '1', '7', '1', '3', '4', '1', '3', '3', '4', '9', '2', '8', '9', '/', '1', '3', '3', '9', '6', '5', '7', '6', '1', '6', '7', '0', '1', '9', '2', '3', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '3', '1', '8', '8', '6', '5', '0', '7', '4', '4', '4', '8', '7', '2', '7', '4', '9', '8', '3', '/', '1', '5', '3', '1', '0', '3', '7', '2', '7', '6', '2', '3', '0', '7', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '8', '9', '3', '5', '3', '9', '0', '2', '3', '8', '6', '2', '0', '3', '4', '2', '3', '/', '9', '3', '1', '9', '3', '5', '7', '3', '3', '3', '5', '7', '8', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '6', '2', '3', '5', '0', '2', '1', '7', '3', '5', '1', '0', '7', '0', '9', '3', '2', '6', '2', '7', '/', '3', '5', '7', '2', '4', '2', '0', '3', '1', '1', '2', '0', '5', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '4', '2', '9', '3', '7', '1', '6', '7', '6', '3', '7', '9', '0', '8', '1', '6', '8', '5', '0', '7', '/', '3', '5', '7', '2', '4', '2', '0', '3', '1', '1', '2', '0', '5', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '6', '5', '5', '0', '9', '1', '2', '5', '2', '8', '8', '6', '4', '3', '0', '0', '2', '6', '3', '/', '2', '4', '3', '5', '7', '4', '1', '1', '2', '1', '2', '7', '6', '2', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '7', '7', '6', '0', '0', '2', '4', '2', '3', '5', '6', '9', '5', '6', '1', '5', '7', '9', '/', '2', '4', '3', '5', '7', '4', '1', '1', '2', '1', '2', '7', '6', '2', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '6', '0', '0', '3', '9', '6', '4', '1', '9', '8', '9', '1', '7', '6', '6', '7', '2', '9', '/', '2', '4', '3', '5', '7', '4', '1', '1', '2', '1', '2', '7', '6', '2', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '9', '8', '7', '7', '1', '8', '9', '5', '9', '4', '6', '3', '2', '0', '5', '5', '4', '1', '/', '6', '0', '8', '9', '3', '5', '2', '8', '0', '3', '1', '9', '0', '5', '6', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '8', '3', '6', '0', '8', '4', '6', '2', '7', '3', '9', '7', '1', '6', '7', '2', '5', '0', '1', '/', '1', '5', '3', '1', '0', '3', '7', '2', '7', '6', '2', '3', '0', '7', '7', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0255834Acc00600 : List (String × SourceJson) := (fragment0255834Field005Key00, fragment0255834Field005Value00) :: fragment0255834Acc00500
noncomputable def fragment0255834Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '4', '8', '1', '4', '7', '4', '1', '7', '1', '3', '4', '1', '3', '3', '4', '9', '2', '8', '9', '/', '1', '3', '3', '9', '6', '5', '7', '6', '1', '6', '7', '0', '1', '9', '2', '3', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '3', '1', '8', '8', '6', '5', '0', '7', '4', '4', '4', '8', '7', '2', '7', '4', '9', '8', '3', '/', '1', '5', '3', '1', '0', '3', '7', '2', '7', '6', '2', '3', '0', '7', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '8', '9', '3', '5', '3', '9', '0', '2', '3', '8', '6', '2', '0', '3', '4', '2', '3', '/', '9', '3', '1', '9', '3', '5', '7', '3', '3', '3', '5', '7', '8', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '6', '2', '3', '5', '0', '2', '1', '7', '3', '5', '1', '0', '7', '0', '9', '3', '2', '6', '2', '7', '/', '3', '5', '7', '2', '4', '2', '0', '3', '1', '1', '2', '0', '5', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '4', '2', '9', '3', '7', '1', '6', '7', '6', '3', '7', '9', '0', '8', '1', '6', '8', '5', '0', '7', '/', '3', '5', '7', '2', '4', '2', '0', '3', '1', '1', '2', '0', '5', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '5', '5', '0', '9', '1', '2', '5', '2', '8', '8', '6', '4', '3', '0', '0', '2', '6', '3', '/', '2', '4', '3', '5', '7', '4', '1', '1', '2', '1', '2', '7', '6', '2', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '7', '7', '6', '0', '0', '2', '4', '2', '3', '5', '6', '9', '5', '6', '1', '5', '7', '9', '/', '2', '4', '3', '5', '7', '4', '1', '1', '2', '1', '2', '7', '6', '2', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '6', '0', '0', '3', '9', '6', '4', '1', '9', '8', '9', '1', '7', '6', '6', '7', '2', '9', '/', '2', '4', '3', '5', '7', '4', '1', '1', '2', '1', '2', '7', '6', '2', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '9', '8', '7', '7', '1', '8', '9', '5', '9', '4', '6', '3', '2', '0', '5', '5', '4', '1', '/', '6', '0', '8', '9', '3', '5', '2', '8', '0', '3', '1', '9', '0', '5', '6', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '8', '3', '6', '0', '8', '4', '6', '2', '7', '3', '9', '7', '1', '6', '7', '2', '5', '0', '1', '/', '1', '5', '3', '1', '0', '3', '7', '2', '7', '6', '2', '3', '0', '7', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0255834_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 397) (SourceJson.white (fragment0255834Field005Chars00 ++ tail)) fragment0255834Acc00500 =
      SourceJson.object (fuel + 396) (SourceJson.white tail) fragment0255834Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0255834_object_field_005"
  err.flush

noncomputable def fragment0255834Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0255834Field006Value00 : SourceJson := .str (String.ofList ['3', '9', '4', '9', '5', '9', '1', '8', '5', '1', '3', '7', '4', '6', '5', '2', '9', '5', '5', '2', '8', '5', '8', '3', '5', '1', '7', '6', '0', '7', '2', '8', '3', '9', '5', '5', '5', '3', '4', '8', '8', '4', '5', '9', '2', '4', '4', '1', '5', '5', '7', '5', '/', '3', '0', '2', '8', '0', '9', '9', '9', '1', '1', '9', '7', '7', '1', '0', '5', '7', '3', '3', '5', '4', '4', '3', '5', '5', '2', '6', '8', '5', '2', '1', '8', '8', '2', '6', '8', '9', '1', '2', '7', '2', '4', '6', '3', '8', '6', '1', '4', '6', '3', '9', '4', '8', '1', '4', '2', '1', '3', '5', '4', '9', '9', '3', '5', '2'])
noncomputable def fragment0255834Acc00700 : List (String × SourceJson) := (fragment0255834Field006Key00, fragment0255834Field006Value00) :: fragment0255834Acc00600
noncomputable def fragment0255834Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '9', '4', '9', '5', '9', '1', '8', '5', '1', '3', '7', '4', '6', '5', '2', '9', '5', '5', '2', '8', '5', '8', '3', '5', '1', '7', '6', '0', '7', '2', '8', '3', '9', '5', '5', '5', '3', '4', '8', '8', '4', '5', '9', '2', '4', '4', '1', '5', '5', '7', '5', '/', '3', '0', '2', '8', '0', '9', '9', '9', '1', '1', '9', '7', '7', '1', '0', '5', '7', '3', '3', '5', '4', '4', '3', '5', '5', '2', '6', '8', '5', '2', '1', '8', '8', '2', '6', '8', '9', '1', '2', '7', '2', '4', '6', '3', '8', '6', '1', '4', '6', '3', '9', '4', '8', '1', '4', '2', '1', '3', '5', '4', '9', '9', '3', '5', '2', '"', ',']

theorem object_fragment0255834_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 396) (SourceJson.white (fragment0255834Field006Chars00 ++ tail)) fragment0255834Acc00600 =
      SourceJson.object (fuel + 395) (SourceJson.white tail) fragment0255834Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0255834_object_field_006"
  err.flush

noncomputable def fragment0255834Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0255834Field007Value00 : SourceJson := .str (String.ofList ['7', '9', '0', '3', '0', '8', '3', '1', '2', '5', '9', '7', '6', '4', '6', '7', '4', '5', '5', '0', '3', '9', '4', '7', '8', '2', '8', '2', '0', '2', '3', '4', '2', '4', '8', '4', '5', '9', '6', '3', '8', '3', '1', '1', '0', '6', '0', '3', '5', '6', '7', '4', '9', '0', '3', '3', '7', '0', '5', '3', '8', '7', '5', '6', '6', '1', '9', '6', '1', '5', '2', '8', '9', '2', '6', '2', '3', '4', '7', '4', '7', '4', '7', '8', '4', '0', '9', '6', '2', '3', '3', '7', '6', '1', '3', '3', '4', '9', '5', '6', '1', '7', '8', '8', '2', '2', '2', '2', '9', '4', '0', '1', '0', '4', '4', '6', '7', '3', '6', '1', '2', '4', '4', '0', '9', '1', '5', '3', '5', '8', '2', '4', '9', '4', '6', '9', '6', '4', '8', '4', '3', '3', '1', '8', '4', '0', '3', '9', '6', '3', '1', '6', '8', '1', '1', '9', '8', '3', '5', '1', '7', '0', '9', '4', '7', '4', '0', '8', '6', '7', '0', '0', '4', '3', '9', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '6', '2', '9', '3', '2', '8', '4', '8', '5', '4', '7', '6', '0', '1', '6', '2', '3', '1', '8', '3', '7', '6', '6', '3', '2', '7', '0', '1', '3', '4', '6', '6', '1', '2', '5', '1', '1', '5', '8', '9', '7', '1', '1', '5', '5', '9', '0', '6', '3', '3', '2', '4', '2', '8', '7', '0', '5', '4', '3', '9', '3', '3', '7', '8', '0', '7', '2', '2', '3', '7', '1', '7', '1', '4', '5', '0', '6', '2', '8', '9', '6', '5', '2', '1', '3', '2', '7', '0', '9', '7', '0', '8', '3', '1', '1', '4', '7', '4', '0', '1', '2', '8', '9', '3', '0', '7', '2', '4', '1', '3', '6', '2', '1', '5', '9', '8', '7', '8', '7', '8', '8', '4', '0', '9', '6', '2', '9', '8', '5', '4', '6', '2', '5', '3', '7', '0', '9', '2', '7', '8', '1', '0', '7', '0', '2', '6', '6', '3', '7', '7', '8', '4', '8', '9', '2', '8', '4', '8', '7', '7', '6', '8', '7', '8', '0', '1', '0', '9', '0', '0', '9', '4', '6', '8', '8', '4', '0', '6', '6', '4', '9', '7', '3', '7', '0', '0', '1', '8', '1', '4', '9', '3', '9', '8', '8', '8', '9', '4', '4', '9'])
noncomputable def fragment0255834Acc00800 : List (String × SourceJson) := (fragment0255834Field007Key00, fragment0255834Field007Value00) :: fragment0255834Acc00700
noncomputable def fragment0255834Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '9', '0', '3', '0', '8', '3', '1', '2', '5', '9', '7', '6', '4', '6', '7', '4', '5', '5', '0', '3', '9', '4', '7', '8', '2', '8', '2', '0', '2', '3', '4', '2', '4', '8', '4', '5', '9', '6', '3', '8', '3', '1', '1', '0', '6', '0', '3', '5', '6', '7', '4', '9', '0', '3', '3', '7', '0', '5', '3', '8', '7', '5', '6', '6', '1', '9', '6', '1', '5', '2', '8', '9', '2', '6', '2', '3', '4', '7', '4', '7', '4', '7', '8', '4', '0', '9', '6', '2', '3', '3', '7', '6', '1', '3', '3', '4', '9', '5', '6', '1', '7', '8', '8', '2', '2', '2', '2', '9', '4', '0', '1', '0', '4', '4', '6', '7', '3', '6', '1', '2', '4', '4', '0', '9', '1', '5', '3', '5', '8', '2', '4', '9', '4', '6', '9', '6', '4', '8', '4', '3', '3', '1', '8', '4', '0', '3', '9', '6', '3', '1', '6', '8', '1', '1', '9', '8', '3', '5', '1', '7', '0', '9', '4', '7', '4', '0', '8', '6', '7', '0', '0', '4', '3', '9', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '6', '2', '9', '3', '2', '8', '4', '8', '5', '4', '7', '6', '0', '1', '6', '2', '3', '1', '8', '3', '7', '6', '6', '3', '2', '7', '0', '1', '3', '4', '6', '6', '1', '2', '5', '1', '1', '5', '8', '9', '7', '1', '1', '5', '5', '9', '0', '6', '3', '3', '2', '4', '2', '8', '7', '0', '5', '4', '3', '9', '3', '3', '7', '8', '0', '7', '2', '2', '3', '7', '1', '7', '1', '4', '5', '0', '6', '2', '8', '9', '6', '5', '2', '1', '3', '2', '7', '0', '9', '7', '0', '8', '3', '1', '1', '4', '7', '4', '0', '1', '2', '8', '9', '3', '0', '7', '2', '4', '1', '3', '6', '2', '1', '5', '9', '8', '7', '8', '7', '8', '8', '4', '0', '9', '6', '2', '9', '8', '5', '4', '6', '2', '5', '3', '7', '0', '9', '2', '7', '8', '1', '0', '7', '0', '2', '6', '6', '3', '7', '7', '8', '4', '8', '9', '2', '8', '4', '8', '7', '7', '6', '8', '7', '8', '0', '1', '0', '9', '0', '0', '9', '4', '6', '8', '8', '4', '0', '6', '6', '4', '9', '7', '3', '7', '0', '0', '1', '8', '1', '4', '9', '3', '9', '8', '8', '8', '9', '4', '4', '9', '"', ',']

theorem object_fragment0255834_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 395) (SourceJson.white (fragment0255834Field007Chars00 ++ tail)) fragment0255834Acc00700 =
      SourceJson.object (fuel + 394) (SourceJson.white tail) fragment0255834Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0255834_object_field_007"
  err.flush

noncomputable def fragment0255834Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0255834Field008Value00 : SourceJson := .str (String.ofList ['1', '0', '3', '3', '3', '8', '3', '6', '8', '6', '6', '7', '4', '3', '7', '4', '8'])
noncomputable def fragment0255834Acc00900 : List (String × SourceJson) := (fragment0255834Field008Key00, fragment0255834Field008Value00) :: fragment0255834Acc00800
noncomputable def fragment0255834Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '3', '3', '3', '8', '3', '6', '8', '6', '6', '7', '4', '3', '7', '4', '8', '"', ',']

theorem object_fragment0255834_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 394) (SourceJson.white (fragment0255834Field008Chars00 ++ tail)) fragment0255834Acc00800 =
      SourceJson.object (fuel + 393) (SourceJson.white tail) fragment0255834Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0255834_object_field_008"
  err.flush

noncomputable def fragment0255834Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0255834Field009Value00 : SourceJson := .str (String.ofList ['3', '5', '5', '1', '7', '3', '3', '4', '3', '5', '4', '7', '6', '3', '2', '5', '5'])
noncomputable def fragment0255834Acc01000 : List (String × SourceJson) := (fragment0255834Field009Key00, fragment0255834Field009Value00) :: fragment0255834Acc00900
noncomputable def fragment0255834Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '5', '5', '1', '7', '3', '3', '4', '3', '5', '4', '7', '6', '3', '2', '5', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0255834_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 393) (SourceJson.white (fragment0255834Field009Chars00 ++ tail)) fragment0255834Acc00900 =
      .ok (.obj (fragment0255834Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0255834_object_field_009"
  err.flush

noncomputable def fragment0255834Chars : List Char := '{' :: (fragment0255834Field000Chars00 ++ fragment0255834Field001Chars00 ++ fragment0255834Field002Chars00 ++ fragment0255834Field003Chars00 ++ fragment0255834Field004Chars00 ++ fragment0255834Field005Chars00 ++ fragment0255834Field006Chars00 ++ fragment0255834Field007Chars00 ++ fragment0255834Field008Chars00 ++ fragment0255834Field009Chars00)
noncomputable def fragment0255834Value : SourceJson := .obj (fragment0255834Acc01000.reverse)

theorem value_fragment0255834 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 403) (fragment0255834Chars ++ tail) =
      .ok (fragment0255834Value, tail) := by
  have hinput : fragment0255834Chars ++ tail = '{' :: (fragment0255834Field000Chars00 ++ (fragment0255834Field001Chars00 ++ (fragment0255834Field002Chars00 ++ (fragment0255834Field003Chars00 ++ (fragment0255834Field004Chars00 ++ (fragment0255834Field005Chars00 ++ (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0255834Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 403) (fragment0255834Chars ++ tail) =
        SourceJson.value (fuel + 403) ('{' :: (fragment0255834Field000Chars00 ++ (fragment0255834Field001Chars00 ++ (fragment0255834Field002Chars00 ++ (fragment0255834Field003Chars00 ++ (fragment0255834Field004Chars00 ++ (fragment0255834Field005Chars00 ++ (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 403)) hinput
    _ = SourceJson.object (fuel + 402) (SourceJson.white (fragment0255834Field000Chars00 ++ (fragment0255834Field001Chars00 ++ (fragment0255834Field002Chars00 ++ (fragment0255834Field003Chars00 ++ (fragment0255834Field004Chars00 ++ (fragment0255834Field005Chars00 ++ (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail)))))))))))) fragment0255834Acc00000 := by rfl
    _ = SourceJson.object (fuel + 401) (SourceJson.white (fragment0255834Field001Chars00 ++ (fragment0255834Field002Chars00 ++ (fragment0255834Field003Chars00 ++ (fragment0255834Field004Chars00 ++ (fragment0255834Field005Chars00 ++ (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail))))))))))) fragment0255834Acc00100 := object_fragment0255834_field_000 fuel (fragment0255834Field001Chars00 ++ (fragment0255834Field002Chars00 ++ (fragment0255834Field003Chars00 ++ (fragment0255834Field004Chars00 ++ (fragment0255834Field005Chars00 ++ (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0255834Field002Chars00 ++ (fragment0255834Field003Chars00 ++ (fragment0255834Field004Chars00 ++ (fragment0255834Field005Chars00 ++ (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail)))))))))) fragment0255834Acc00200 := object_fragment0255834_field_001 fuel (fragment0255834Field002Chars00 ++ (fragment0255834Field003Chars00 ++ (fragment0255834Field004Chars00 ++ (fragment0255834Field005Chars00 ++ (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 399) (SourceJson.white (fragment0255834Field003Chars00 ++ (fragment0255834Field004Chars00 ++ (fragment0255834Field005Chars00 ++ (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail))))))))) fragment0255834Acc00300 := object_fragment0255834_field_002 fuel (fragment0255834Field003Chars00 ++ (fragment0255834Field004Chars00 ++ (fragment0255834Field005Chars00 ++ (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 398) (SourceJson.white (fragment0255834Field004Chars00 ++ (fragment0255834Field005Chars00 ++ (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail)))))))) fragment0255834Acc00400 := object_fragment0255834_field_003 fuel (fragment0255834Field004Chars00 ++ (fragment0255834Field005Chars00 ++ (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 397) (SourceJson.white (fragment0255834Field005Chars00 ++ (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail))))))) fragment0255834Acc00500 := object_fragment0255834_field_004 fuel (fragment0255834Field005Chars00 ++ (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 396) (SourceJson.white (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail)))))) fragment0255834Acc00600 := object_fragment0255834_field_005 fuel (fragment0255834Field006Chars00 ++ (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 395) (SourceJson.white (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail))))) fragment0255834Acc00700 := object_fragment0255834_field_006 fuel (fragment0255834Field007Chars00 ++ (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 394) (SourceJson.white (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail)))) fragment0255834Acc00800 := object_fragment0255834_field_007 fuel (fragment0255834Field008Chars00 ++ (fragment0255834Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 393) (SourceJson.white (fragment0255834Field009Chars00 ++ (tail))) fragment0255834Acc00900 := object_fragment0255834_field_008 fuel (fragment0255834Field009Chars00 ++ (tail))
    _ = .ok (fragment0255834Value, tail) := object_fragment0255834_field_009 fuel (tail)

noncomputable def fragment0257782Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0257782Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0257782Field000Value00 : SourceJson := .number (String.ofList ['7', '0'])
noncomputable def fragment0257782Acc00100 : List (String × SourceJson) := (fragment0257782Field000Key00, fragment0257782Field000Value00) :: fragment0257782Acc00000
noncomputable def fragment0257782Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '0', ',']

theorem object_fragment0257782_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0257782Field000Chars00 ++ tail)) fragment0257782Acc00000 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0257782Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0257782_object_field_000"
  err.flush

noncomputable def fragment0257782Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0257782Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0257782Acc00200 : List (String × SourceJson) := (fragment0257782Field001Key00, fragment0257782Field001Value00) :: fragment0257782Acc00100
noncomputable def fragment0257782Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0257782_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0257782Field001Chars00 ++ tail)) fragment0257782Acc00100 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0257782Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0257782_object_field_001"
  err.flush

noncomputable def fragment0257782Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0257782Field002Value00 : SourceJson := .str (String.ofList ['5', '2', '5', '2', '9', '6', '4', '1', '9', '1', '7', '9', '6', '5', '1', '0', '6', '7', '6', '5', '4', '1', '4', '0', '9', '6', '3', '1', '7', '4', '1', '7', '1', '8', '4', '8', '2', '4', '7', '3', '3', '1', '/', '9', '6', '4', '7', '9', '8', '0', '3', '5', '9', '3', '7', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0257782Acc00300 : List (String × SourceJson) := (fragment0257782Field002Key00, fragment0257782Field002Value00) :: fragment0257782Acc00200
noncomputable def fragment0257782Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '2', '5', '2', '9', '6', '4', '1', '9', '1', '7', '9', '6', '5', '1', '0', '6', '7', '6', '5', '4', '1', '4', '0', '9', '6', '3', '1', '7', '4', '1', '7', '1', '8', '4', '8', '2', '4', '7', '3', '3', '1', '/', '9', '6', '4', '7', '9', '8', '0', '3', '5', '9', '3', '7', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0257782_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0257782Field002Chars00 ++ tail)) fragment0257782Acc00200 =
      SourceJson.object (fuel + 240) (SourceJson.white tail) fragment0257782Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0257782_object_field_002"
  err.flush

noncomputable def fragment0257782Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0257782Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0257782Acc00400 : List (String × SourceJson) := (fragment0257782Field003Key00, fragment0257782Field003Value00) :: fragment0257782Acc00300
noncomputable def fragment0257782Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0257782_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 240) (SourceJson.white (fragment0257782Field003Chars00 ++ tail)) fragment0257782Acc00300 =
      SourceJson.object (fuel + 239) (SourceJson.white tail) fragment0257782Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0257782_object_field_003"
  err.flush

noncomputable def fragment0257782Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0257782Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0257782Acc00500 : List (String × SourceJson) := (fragment0257782Field004Key00, fragment0257782Field004Value00) :: fragment0257782Acc00400
noncomputable def fragment0257782Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0257782_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0257782Field004Chars00 ++ tail)) fragment0257782Acc00400 =
      SourceJson.object (fuel + 238) (SourceJson.white tail) fragment0257782Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0257782_object_field_004"
  err.flush

noncomputable def fragment0257782Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0257782Field005Value00 : SourceJson := .arr [.str (String.ofList ['9', '2', '9', '1', '1', '5', '6', '9', '2', '4', '9', '8', '9', '/', '1', '0', '6', '7', '9', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '9', '0', '2', '5', '8', '7', '1', '3', '8', '9', '/', '1', '3', '3', '4', '8', '9', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '8', '2', '5', '0', '5', '4', '2', '3', '3', '9', '/', '5', '5', '7', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '0', '8', '3', '3', '5', '4', '6', '9', '6', '0', '7', '7', '/', '6', '4', '0', '7', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '7', '3', '5', '1', '6', '3', '0', '5', '5', '3', '5', '7', '/', '6', '4', '0', '7', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '8', '7', '7', '6', '8', '9', '3', '0', '1', '6', '9', '/', '5', '8', '2', '4', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '5', '0', '6', '6', '0', '8', '5', '4', '9', '3', '/', '1', '4', '5', '6', '2', '4', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '7', '9', '2', '8', '8', '4', '8', '6', '5', '1', '/', '8', '3', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '8', '7', '7', '0', '9', '8', '2', '9', '1', '/', '8', '3', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '4', '2', '7', '1', '0', '8', '2', '8', '9', '/', '2', '5', '0', '2', '9', '2', '1', '0', '9', '3', '7', '5', '0'])]
noncomputable def fragment0257782Acc00600 : List (String × SourceJson) := (fragment0257782Field005Key00, fragment0257782Field005Value00) :: fragment0257782Acc00500
noncomputable def fragment0257782Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '9', '1', '1', '5', '6', '9', '2', '4', '9', '8', '9', '/', '1', '0', '6', '7', '9', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '9', '0', '2', '5', '8', '7', '1', '3', '8', '9', '/', '1', '3', '3', '4', '8', '9', '1', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '8', '2', '5', '0', '5', '4', '2', '3', '3', '9', '/', '5', '5', '7', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '0', '8', '3', '3', '5', '4', '6', '9', '6', '0', '7', '7', '/', '6', '4', '0', '7', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '7', '3', '5', '1', '6', '3', '0', '5', '5', '3', '5', '7', '/', '6', '4', '0', '7', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '8', '7', '7', '6', '8', '9', '3', '0', '1', '6', '9', '/', '5', '8', '2', '4', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '5', '0', '6', '6', '0', '8', '5', '4', '9', '3', '/', '1', '4', '5', '6', '2', '4', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '9', '2', '8', '8', '4', '8', '6', '5', '1', '/', '8', '3', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '8', '7', '7', '0', '9', '8', '2', '9', '1', '/', '8', '3', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '4', '2', '7', '1', '0', '8', '2', '8', '9', '/', '2', '5', '0', '2', '9', '2', '1', '0', '9', '3', '7', '5', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0257782_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0257782Field005Chars00 ++ tail)) fragment0257782Acc00500 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment0257782Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0257782_object_field_005"
  err.flush

noncomputable def fragment0257782Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0257782Field006Value00 : SourceJson := .str (String.ofList ['3', '1', '1', '4', '5', '2', '2', '0', '1', '4', '1', '0', '8', '1', '2', '9', '2', '2', '3', '5', '0', '8', '0', '0', '3', '0', '1', '7', '7', '1', '3', '3', '1', '8', '9', '7', '0', '0', '7', '3', '4', '9', '9', '6', '0', '1', '9', '3', '8', '8', '9', '0', '0', '0', '0', '0', '/', '5', '9', '8', '8', '8', '4', '0', '6', '0', '1', '4', '2', '6', '5', '1', '3', '0', '5', '2', '1', '1', '3', '4', '7', '1', '9', '5', '5', '7', '8', '0', '5', '5', '9', '8', '5', '8', '5', '6', '5', '6', '7', '2', '4', '1', '3', '5', '5', '0', '9', '0', '8', '0', '3', '1', '8', '0', '1', '7', '5', '0', '3', '1', '7', '0', '4', '2', '9'])
noncomputable def fragment0257782Acc00700 : List (String × SourceJson) := (fragment0257782Field006Key00, fragment0257782Field006Value00) :: fragment0257782Acc00600
noncomputable def fragment0257782Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '1', '1', '4', '5', '2', '2', '0', '1', '4', '1', '0', '8', '1', '2', '9', '2', '2', '3', '5', '0', '8', '0', '0', '3', '0', '1', '7', '7', '1', '3', '3', '1', '8', '9', '7', '0', '0', '7', '3', '4', '9', '9', '6', '0', '1', '9', '3', '8', '8', '9', '0', '0', '0', '0', '0', '/', '5', '9', '8', '8', '8', '4', '0', '6', '0', '1', '4', '2', '6', '5', '1', '3', '0', '5', '2', '1', '1', '3', '4', '7', '1', '9', '5', '5', '7', '8', '0', '5', '5', '9', '8', '5', '8', '5', '6', '5', '6', '7', '2', '4', '1', '3', '5', '5', '0', '9', '0', '8', '0', '3', '1', '8', '0', '1', '7', '5', '0', '3', '1', '7', '0', '4', '2', '9', '"', ',']

theorem object_fragment0257782_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0257782Field006Chars00 ++ tail)) fragment0257782Acc00600 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0257782Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0257782_object_field_006"
  err.flush

noncomputable def fragment0257782Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0257782Field007Value00 : SourceJson := .str (String.ofList ['6', '9', '6', '4', '8', '9', '0', '9', '5', '9', '3', '4', '6', '9', '8', '2', '2', '6', '1', '0', '7', '1', '3', '6', '7', '6', '8', '7', '0', '6', '5', '9', '6', '5', '6', '3', '6', '5', '5', '0', '5', '6', '6', '3', '4', '2', '1', '3', '2', '1', '4', '2', '6', '9', '0', '3', '2', '8', '9', '3', '2', '0', '5', '8', '1', '3', '0', '7', '2', '3', '8', '6', '1', '7', '8', '1', '8', '1', '6', '4', '8', '5', '9', '7', '0', '9', '7', '9', '1', '0', '1', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '6', '8', '7', '3', '0', '5', '7', '6', '4', '4', '1', '7', '7', '5', '5', '0', '2', '7', '1', '6', '7', '9', '3', '5', '0', '6', '1', '0', '9', '5', '0', '8', '0', '6', '8', '8', '5', '2', '9', '6', '1', '6', '0', '7', '7', '2', '1', '7', '3', '4', '1', '5', '4', '2', '6', '2', '5', '5', '8', '9', '9', '8', '5', '5', '7', '9', '0', '7', '6', '3', '3', '3', '2', '3', '7', '2', '7', '7', '3', '2', '1', '5', '4', '1', '8', '2', '3', '9', '4', '7', '7', '2', '5', '2', '7', '8', '3', '6', '5', '0', '2', '1', '5', '7', '6', '7', '7', '4', '5', '4', '2', '9', '5', '7', '8', '9', '9', '9', '7', '3'])
noncomputable def fragment0257782Acc00800 : List (String × SourceJson) := (fragment0257782Field007Key00, fragment0257782Field007Value00) :: fragment0257782Acc00700
noncomputable def fragment0257782Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '9', '6', '4', '8', '9', '0', '9', '5', '9', '3', '4', '6', '9', '8', '2', '2', '6', '1', '0', '7', '1', '3', '6', '7', '6', '8', '7', '0', '6', '5', '9', '6', '5', '6', '3', '6', '5', '5', '0', '5', '6', '6', '3', '4', '2', '1', '3', '2', '1', '4', '2', '6', '9', '0', '3', '2', '8', '9', '3', '2', '0', '5', '8', '1', '3', '0', '7', '2', '3', '8', '6', '1', '7', '8', '1', '8', '1', '6', '4', '8', '5', '9', '7', '0', '9', '7', '9', '1', '0', '1', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '6', '8', '7', '3', '0', '5', '7', '6', '4', '4', '1', '7', '7', '5', '5', '0', '2', '7', '1', '6', '7', '9', '3', '5', '0', '6', '1', '0', '9', '5', '0', '8', '0', '6', '8', '8', '5', '2', '9', '6', '1', '6', '0', '7', '7', '2', '1', '7', '3', '4', '1', '5', '4', '2', '6', '2', '5', '5', '8', '9', '9', '8', '5', '5', '7', '9', '0', '7', '6', '3', '3', '3', '2', '3', '7', '2', '7', '7', '3', '2', '1', '5', '4', '1', '8', '2', '3', '9', '4', '7', '7', '2', '5', '2', '7', '8', '3', '6', '5', '0', '2', '1', '5', '7', '6', '7', '7', '4', '5', '4', '2', '9', '5', '7', '8', '9', '9', '9', '7', '3', '"', ',']

theorem object_fragment0257782_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0257782Field007Chars00 ++ tail)) fragment0257782Acc00700 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0257782Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0257782_object_field_007"
  err.flush

noncomputable def fragment0257782Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0257782Field008Value00 : SourceJson := .str (String.ofList ['4', '1', '2', '0', '2', '9', '4', '2', '7', '2', '4', '7', '1', '3', '0', '6', '2'])
noncomputable def fragment0257782Acc00900 : List (String × SourceJson) := (fragment0257782Field008Key00, fragment0257782Field008Value00) :: fragment0257782Acc00800
noncomputable def fragment0257782Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '1', '2', '0', '2', '9', '4', '2', '7', '2', '4', '7', '1', '3', '0', '6', '2', '"', ',']

theorem object_fragment0257782_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0257782Field008Chars00 ++ tail)) fragment0257782Acc00800 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0257782Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0257782_object_field_008"
  err.flush

noncomputable def fragment0257782Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0257782Field009Value00 : SourceJson := .str (String.ofList ['1', '7', '4', '1', '4', '4', '0', '3', '0', '0', '8', '0', '6', '2', '5', '1', '2', '9'])
noncomputable def fragment0257782Acc01000 : List (String × SourceJson) := (fragment0257782Field009Key00, fragment0257782Field009Value00) :: fragment0257782Acc00900
noncomputable def fragment0257782Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '4', '1', '4', '4', '0', '3', '0', '0', '8', '0', '6', '2', '5', '1', '2', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0257782_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0257782Field009Chars00 ++ tail)) fragment0257782Acc00900 =
      .ok (.obj (fragment0257782Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0257782_object_field_009"
  err.flush

noncomputable def fragment0257782Chars : List Char := '{' :: (fragment0257782Field000Chars00 ++ fragment0257782Field001Chars00 ++ fragment0257782Field002Chars00 ++ fragment0257782Field003Chars00 ++ fragment0257782Field004Chars00 ++ fragment0257782Field005Chars00 ++ fragment0257782Field006Chars00 ++ fragment0257782Field007Chars00 ++ fragment0257782Field008Chars00 ++ fragment0257782Field009Chars00)
noncomputable def fragment0257782Value : SourceJson := .obj (fragment0257782Acc01000.reverse)

theorem value_fragment0257782 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 244) (fragment0257782Chars ++ tail) =
      .ok (fragment0257782Value, tail) := by
  have hinput : fragment0257782Chars ++ tail = '{' :: (fragment0257782Field000Chars00 ++ (fragment0257782Field001Chars00 ++ (fragment0257782Field002Chars00 ++ (fragment0257782Field003Chars00 ++ (fragment0257782Field004Chars00 ++ (fragment0257782Field005Chars00 ++ (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0257782Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 244) (fragment0257782Chars ++ tail) =
        SourceJson.value (fuel + 244) ('{' :: (fragment0257782Field000Chars00 ++ (fragment0257782Field001Chars00 ++ (fragment0257782Field002Chars00 ++ (fragment0257782Field003Chars00 ++ (fragment0257782Field004Chars00 ++ (fragment0257782Field005Chars00 ++ (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 244)) hinput
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0257782Field000Chars00 ++ (fragment0257782Field001Chars00 ++ (fragment0257782Field002Chars00 ++ (fragment0257782Field003Chars00 ++ (fragment0257782Field004Chars00 ++ (fragment0257782Field005Chars00 ++ (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail)))))))))))) fragment0257782Acc00000 := by rfl
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0257782Field001Chars00 ++ (fragment0257782Field002Chars00 ++ (fragment0257782Field003Chars00 ++ (fragment0257782Field004Chars00 ++ (fragment0257782Field005Chars00 ++ (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail))))))))))) fragment0257782Acc00100 := object_fragment0257782_field_000 fuel (fragment0257782Field001Chars00 ++ (fragment0257782Field002Chars00 ++ (fragment0257782Field003Chars00 ++ (fragment0257782Field004Chars00 ++ (fragment0257782Field005Chars00 ++ (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0257782Field002Chars00 ++ (fragment0257782Field003Chars00 ++ (fragment0257782Field004Chars00 ++ (fragment0257782Field005Chars00 ++ (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail)))))))))) fragment0257782Acc00200 := object_fragment0257782_field_001 fuel (fragment0257782Field002Chars00 ++ (fragment0257782Field003Chars00 ++ (fragment0257782Field004Chars00 ++ (fragment0257782Field005Chars00 ++ (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 240) (SourceJson.white (fragment0257782Field003Chars00 ++ (fragment0257782Field004Chars00 ++ (fragment0257782Field005Chars00 ++ (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail))))))))) fragment0257782Acc00300 := object_fragment0257782_field_002 fuel (fragment0257782Field003Chars00 ++ (fragment0257782Field004Chars00 ++ (fragment0257782Field005Chars00 ++ (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0257782Field004Chars00 ++ (fragment0257782Field005Chars00 ++ (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail)))))))) fragment0257782Acc00400 := object_fragment0257782_field_003 fuel (fragment0257782Field004Chars00 ++ (fragment0257782Field005Chars00 ++ (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0257782Field005Chars00 ++ (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail))))))) fragment0257782Acc00500 := object_fragment0257782_field_004 fuel (fragment0257782Field005Chars00 ++ (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail)))))) fragment0257782Acc00600 := object_fragment0257782_field_005 fuel (fragment0257782Field006Chars00 ++ (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail))))) fragment0257782Acc00700 := object_fragment0257782_field_006 fuel (fragment0257782Field007Chars00 ++ (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail)))) fragment0257782Acc00800 := object_fragment0257782_field_007 fuel (fragment0257782Field008Chars00 ++ (fragment0257782Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0257782Field009Chars00 ++ (tail))) fragment0257782Acc00900 := object_fragment0257782_field_008 fuel (fragment0257782Field009Chars00 ++ (tail))
    _ = .ok (fragment0257782Value, tail) := object_fragment0257782_field_009 fuel (tail)

noncomputable def fragment0259419Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0259419Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0259419Field000Value00 : SourceJson := .number (String.ofList ['7', '1'])
noncomputable def fragment0259419Acc00100 : List (String × SourceJson) := (fragment0259419Field000Key00, fragment0259419Field000Value00) :: fragment0259419Acc00000
noncomputable def fragment0259419Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '1', ',']

theorem object_fragment0259419_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 438) (SourceJson.white (fragment0259419Field000Chars00 ++ tail)) fragment0259419Acc00000 =
      SourceJson.object (fuel + 437) (SourceJson.white tail) fragment0259419Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0259419_object_field_000"
  err.flush

noncomputable def fragment0259419Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0259419Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0259419Acc00200 : List (String × SourceJson) := (fragment0259419Field001Key00, fragment0259419Field001Value00) :: fragment0259419Acc00100
noncomputable def fragment0259419Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0259419_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 437) (SourceJson.white (fragment0259419Field001Chars00 ++ tail)) fragment0259419Acc00100 =
      SourceJson.object (fuel + 436) (SourceJson.white tail) fragment0259419Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0259419_object_field_001"
  err.flush

noncomputable def fragment0259419Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0259419Field002Value00 : SourceJson := .str (String.ofList ['1', '3', '0', '2', '9', '9', '0', '2', '5', '9', '9', '5', '4', '9', '9', '6', '5', '1', '1', '0', '0', '4', '5', '8', '1', '8', '8', '0', '2', '3', '7', '8', '6', '5', '3', '5', '1', '/', '2', '3', '4', '1', '1', '0', '6', '3', '4', '5', '2', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0259419Acc00300 : List (String × SourceJson) := (fragment0259419Field002Key00, fragment0259419Field002Value00) :: fragment0259419Acc00200
noncomputable def fragment0259419Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '3', '0', '2', '9', '9', '0', '2', '5', '9', '9', '5', '4', '9', '9', '6', '5', '1', '1', '0', '0', '4', '5', '8', '1', '8', '8', '0', '2', '3', '7', '8', '6', '5', '3', '5', '1', '/', '2', '3', '4', '1', '1', '0', '6', '3', '4', '5', '2', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0259419_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 436) (SourceJson.white (fragment0259419Field002Chars00 ++ tail)) fragment0259419Acc00200 =
      SourceJson.object (fuel + 435) (SourceJson.white tail) fragment0259419Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0259419_object_field_002"
  err.flush

noncomputable def fragment0259419Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0259419Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0259419Acc00400 : List (String × SourceJson) := (fragment0259419Field003Key00, fragment0259419Field003Value00) :: fragment0259419Acc00300
noncomputable def fragment0259419Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0259419_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 435) (SourceJson.white (fragment0259419Field003Chars00 ++ tail)) fragment0259419Acc00300 =
      SourceJson.object (fuel + 434) (SourceJson.white tail) fragment0259419Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0259419_object_field_003"
  err.flush

noncomputable def fragment0259419Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0259419Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0259419Acc00500 : List (String × SourceJson) := (fragment0259419Field004Key00, fragment0259419Field004Value00) :: fragment0259419Acc00400
noncomputable def fragment0259419Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0259419_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 434) (SourceJson.white (fragment0259419Field004Chars00 ++ tail)) fragment0259419Acc00400 =
      SourceJson.object (fuel + 433) (SourceJson.white tail) fragment0259419Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0259419_object_field_004"
  err.flush

noncomputable def fragment0259419Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0259419Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '5', '3', '8', '0', '9', '2', '8', '5', '9', '6', '8', '9', '0', '3', '4', '2', '5', '9', '2', '6', '7', '7', '3', '/', '8', '8', '2', '3', '9', '4', '8', '2', '2', '8', '0', '5', '9', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '8', '1', '8', '9', '6', '5', '2', '1', '1', '6', '5', '4', '7', '7', '4', '1', '2', '6', '7', '9', '/', '2', '9', '3', '1', '5', '4', '4', '2', '6', '1', '8', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '9', '4', '6', '2', '3', '0', '2', '1', '0', '4', '2', '1', '2', '0', '6', '5', '3', '5', '4', '9', '/', '7', '6', '7', '2', '9', '9', '8', '4', '5', '9', '1', '8', '2', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '9', '0', '0', '8', '2', '0', '9', '8', '4', '2', '3', '9', '2', '0', '7', '2', '8', '7', '4', '3', '9', '/', '1', '4', '7', '0', '6', '5', '8', '0', '3', '8', '0', '0', '9', '9', '5', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '1', '0', '1', '6', '4', '4', '0', '9', '2', '4', '9', '9', '9', '8', '9', '9', '3', '2', '9', '9', '9', '/', '1', '4', '7', '0', '6', '5', '8', '0', '3', '8', '0', '0', '9', '9', '5', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '8', '8', '2', '6', '9', '8', '2', '2', '5', '1', '2', '4', '5', '7', '6', '1', '1', '7', '7', '8', '3', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '7', '1', '3', '2', '0', '2', '8', '5', '4', '3', '1', '4', '5', '3', '4', '6', '3', '1', '2', '7', '7', '/', '4', '0', '1', '0', '8', '8', '5', '5', '5', '8', '2', '0', '8', '9', '6', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '7', '4', '0', '1', '4', '6', '9', '9', '0', '1', '3', '1', '7', '9', '2', '6', '0', '2', '5', '4', '9', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '3', '0', '4', '0', '7', '1', '8', '8', '6', '4', '8', '8', '0', '7', '2', '9', '5', '9', '7', '8', '9', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '0', '9', '8', '8', '3', '8', '2', '7', '7', '3', '0', '0', '7', '6', '4', '6', '0', '1', '3', '/', '2', '9', '3', '1', '5', '4', '4', '2', '6', '1', '8', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0259419Acc00600 : List (String × SourceJson) := (fragment0259419Field005Key00, fragment0259419Field005Value00) :: fragment0259419Acc00500
noncomputable def fragment0259419Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '3', '8', '0', '9', '2', '8', '5', '9', '6', '8', '9', '0', '3', '4', '2', '5', '9', '2', '6', '7', '7', '3', '/', '8', '8', '2', '3', '9', '4', '8', '2', '2', '8', '0', '5', '9', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '8', '1', '8', '9', '6', '5', '2', '1', '1', '6', '5', '4', '7', '7', '4', '1', '2', '6', '7', '9', '/', '2', '9', '3', '1', '5', '4', '4', '2', '6', '1', '8', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '4', '6', '2', '3', '0', '2', '1', '0', '4', '2', '1', '2', '0', '6', '5', '3', '5', '4', '9', '/', '7', '6', '7', '2', '9', '9', '8', '4', '5', '9', '1', '8', '2', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '9', '0', '0', '8', '2', '0', '9', '8', '4', '2', '3', '9', '2', '0', '7', '2', '8', '7', '4', '3', '9', '/', '1', '4', '7', '0', '6', '5', '8', '0', '3', '8', '0', '0', '9', '9', '5', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '1', '0', '1', '6', '4', '4', '0', '9', '2', '4', '9', '9', '9', '8', '9', '9', '3', '2', '9', '9', '9', '/', '1', '4', '7', '0', '6', '5', '8', '0', '3', '8', '0', '0', '9', '9', '5', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '8', '8', '2', '6', '9', '8', '2', '2', '5', '1', '2', '4', '5', '7', '6', '1', '1', '7', '7', '8', '3', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '7', '1', '3', '2', '0', '2', '8', '5', '4', '3', '1', '4', '5', '3', '4', '6', '3', '1', '2', '7', '7', '/', '4', '0', '1', '0', '8', '8', '5', '5', '5', '8', '2', '0', '8', '9', '6', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '7', '4', '0', '1', '4', '6', '9', '9', '0', '1', '3', '1', '7', '9', '2', '6', '0', '2', '5', '4', '9', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '3', '0', '4', '0', '7', '1', '8', '8', '6', '4', '8', '8', '0', '7', '2', '9', '5', '9', '7', '8', '9', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '0', '9', '8', '8', '3', '8', '2', '7', '7', '3', '0', '0', '7', '6', '4', '6', '0', '1', '3', '/', '2', '9', '3', '1', '5', '4', '4', '2', '6', '1', '8', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0259419_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 433) (SourceJson.white (fragment0259419Field005Chars00 ++ tail)) fragment0259419Acc00500 =
      SourceJson.object (fuel + 432) (SourceJson.white tail) fragment0259419Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0259419_object_field_005"
  err.flush

noncomputable def fragment0259419Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0259419Field006Value00 : SourceJson := .str (String.ofList ['3', '7', '9', '1', '1', '0', '6', '2', '6', '3', '1', '9', '2', '4', '0', '1', '4', '2', '5', '4', '2', '9', '1', '8', '9', '9', '1', '5', '7', '2', '1', '1', '2', '6', '4', '7', '9', '8', '6', '6', '1', '3', '2', '4', '1', '2', '1', '2', '5', '/', '1', '3', '3', '4', '6', '5', '7', '8', '7', '2', '9', '9', '9', '6', '5', '7', '2', '2', '4', '9', '9', '0', '2', '6', '9', '7', '5', '6', '7', '1', '2', '7', '8', '2', '4', '8', '3', '9', '1', '0', '1', '9', '2', '2', '7', '1', '1', '6', '5', '5', '7', '2', '0', '6', '1', '6', '5', '3', '6', '7', '8', '0', '8', '2', '1', '2', '8'])
noncomputable def fragment0259419Acc00700 : List (String × SourceJson) := (fragment0259419Field006Key00, fragment0259419Field006Value00) :: fragment0259419Acc00600
noncomputable def fragment0259419Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '7', '9', '1', '1', '0', '6', '2', '6', '3', '1', '9', '2', '4', '0', '1', '4', '2', '5', '4', '2', '9', '1', '8', '9', '9', '1', '5', '7', '2', '1', '1', '2', '6', '4', '7', '9', '8', '6', '6', '1', '3', '2', '4', '1', '2', '1', '2', '5', '/', '1', '3', '3', '4', '6', '5', '7', '8', '7', '2', '9', '9', '9', '6', '5', '7', '2', '2', '4', '9', '9', '0', '2', '6', '9', '7', '5', '6', '7', '1', '2', '7', '8', '2', '4', '8', '3', '9', '1', '0', '1', '9', '2', '2', '7', '1', '1', '6', '5', '5', '7', '2', '0', '6', '1', '6', '5', '3', '6', '7', '8', '0', '8', '2', '1', '2', '8', '"', ',']

theorem object_fragment0259419_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 432) (SourceJson.white (fragment0259419Field006Chars00 ++ tail)) fragment0259419Acc00600 =
      SourceJson.object (fuel + 431) (SourceJson.white tail) fragment0259419Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0259419_object_field_006"
  err.flush

noncomputable def fragment0259419Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0259419Field007Value00 : SourceJson := .str (String.ofList ['5', '4', '8', '7', '7', '6', '1', '2', '1', '4', '9', '3', '3', '0', '4', '6', '0', '3', '9', '8', '4', '0', '3', '3', '5', '6', '6', '2', '4', '1', '4', '5', '8', '5', '1', '0', '1', '8', '1', '8', '8', '2', '7', '7', '2', '8', '1', '2', '8', '1', '6', '4', '4', '4', '5', '1', '2', '6', '3', '9', '2', '1', '5', '1', '7', '6', '4', '1', '7', '7', '1', '5', '7', '7', '6', '3', '5', '6', '5', '8', '5', '0', '8', '1', '8', '8', '5', '3', '3', '2', '5', '5', '1', '2', '6', '4', '9', '8', '3', '1', '6', '6', '3', '5', '6', '6', '7', '1', '6', '9', '3', '6', '1', '3', '0', '0', '6', '3', '0', '5', '5', '1', '7', '1', '3', '3', '5', '6', '0', '7', '9', '6', '3', '2', '6', '2', '6', '7', '7', '0', '8', '5', '9', '9', '4', '1', '6', '7', '7', '1', '4', '7', '3', '1', '4', '8', '0', '3', '8', '7', '5', '9', '6', '5', '7', '2', '0', '5', '4', '9', '9', '9', '8', '2', '9', '4', '4', '1', '9', '3', '4', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '4', '4', '8', '7', '4', '2', '7', '7', '3', '9', '1', '1', '6', '5', '2', '9', '7', '9', '5', '1', '5', '4', '7', '9', '3', '3', '5', '8', '1', '4', '0', '6', '9', '2', '5', '1', '8', '2', '0', '0', '8', '1', '1', '8', '2', '9', '8', '9', '1', '7', '7', '4', '2', '1', '3', '9', '5', '8', '7', '4', '4', '0', '4', '6', '2', '9', '5', '3', '8', '1', '4', '9', '4', '4', '9', '3', '1', '4', '6', '4', '9', '5', '4', '3', '0', '3', '4', '4', '1', '6', '7', '9', '8', '5', '7', '3', '8', '7', '3', '9', '1', '6', '0', '9', '7', '5', '6', '2', '8', '9', '5', '1', '4', '7', '8', '2', '6', '5', '9', '1', '2', '5', '5', '1', '6', '2', '8', '1', '8', '4', '6', '0', '4', '6', '0', '2', '3', '5', '1', '9', '4', '2', '8', '4', '4', '9', '0', '0', '5', '0', '4', '8', '0', '5', '6', '3', '7', '6', '4', '2', '3', '6', '2', '0', '2', '9', '6', '1', '0', '2', '2', '6', '3', '5', '2', '6', '5', '4', '3', '9', '5', '1', '0', '0', '4', '6', '1', '1', '9', '0', '2', '4', '4', '4', '4', '7', '9', '9', '6', '4', '3', '8', '1', '7', '4', '9', '3', '1', '1', '4', '0', '7', '7', '5', '2', '1', '2', '6', '3', '9', '3'])
noncomputable def fragment0259419Acc00800 : List (String × SourceJson) := (fragment0259419Field007Key00, fragment0259419Field007Value00) :: fragment0259419Acc00700
noncomputable def fragment0259419Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '4', '8', '7', '7', '6', '1', '2', '1', '4', '9', '3', '3', '0', '4', '6', '0', '3', '9', '8', '4', '0', '3', '3', '5', '6', '6', '2', '4', '1', '4', '5', '8', '5', '1', '0', '1', '8', '1', '8', '8', '2', '7', '7', '2', '8', '1', '2', '8', '1', '6', '4', '4', '4', '5', '1', '2', '6', '3', '9', '2', '1', '5', '1', '7', '6', '4', '1', '7', '7', '1', '5', '7', '7', '6', '3', '5', '6', '5', '8', '5', '0', '8', '1', '8', '8', '5', '3', '3', '2', '5', '5', '1', '2', '6', '4', '9', '8', '3', '1', '6', '6', '3', '5', '6', '6', '7', '1', '6', '9', '3', '6', '1', '3', '0', '0', '6', '3', '0', '5', '5', '1', '7', '1', '3', '3', '5', '6', '0', '7', '9', '6', '3', '2', '6', '2', '6', '7', '7', '0', '8', '5', '9', '9', '4', '1', '6', '7', '7', '1', '4', '7', '3', '1', '4', '8', '0', '3', '8', '7', '5', '9', '6', '5', '7', '2', '0', '5', '4', '9', '9', '9', '8', '2', '9', '4', '4', '1', '9', '3', '4', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '4', '4', '8', '7', '4', '2', '7', '7', '3', '9', '1', '1', '6', '5', '2', '9', '7', '9', '5', '1', '5', '4', '7', '9', '3', '3', '5', '8', '1', '4', '0', '6', '9', '2', '5', '1', '8', '2', '0', '0', '8', '1', '1', '8', '2', '9', '8', '9', '1', '7', '7', '4', '2', '1', '3', '9', '5', '8', '7', '4', '4', '0', '4', '6', '2', '9', '5', '3', '8', '1', '4', '9', '4', '4', '9', '3', '1', '4', '6', '4', '9', '5', '4', '3', '0', '3', '4', '4', '1', '6', '7', '9', '8', '5', '7', '3', '8', '7', '3', '9', '1', '6', '0', '9', '7', '5', '6', '2', '8', '9', '5', '1', '4', '7', '8', '2', '6', '5', '9', '1', '2', '5', '5', '1', '6', '2', '8', '1', '8', '4', '6', '0', '4', '6', '0', '2', '3', '5', '1', '9', '4', '2', '8', '4', '4', '9', '0', '0', '5', '0', '4', '8', '0', '5', '6', '3', '7', '6', '4', '2', '3', '6', '2', '0', '2', '9', '6', '1', '0', '2', '2', '6', '3', '5', '2', '6', '5', '4', '3', '9', '5', '1', '0', '0', '4', '6', '1', '1', '9', '0', '2', '4', '4', '4', '4', '7', '9', '9', '6', '4', '3', '8', '1', '7', '4', '9', '3', '1', '1', '4', '0', '7', '7', '5', '2', '1', '2', '6', '3', '9', '3', '"', ',']

theorem object_fragment0259419_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 431) (SourceJson.white (fragment0259419Field007Chars00 ++ tail)) fragment0259419Acc00700 =
      SourceJson.object (fuel + 430) (SourceJson.white tail) fragment0259419Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0259419_object_field_007"
  err.flush

noncomputable def fragment0259419Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0259419Field008Value00 : SourceJson := .str (String.ofList ['2', '2', '5', '0', '4', '8', '2', '2', '3', '3', '7', '2'])
noncomputable def fragment0259419Acc00900 : List (String × SourceJson) := (fragment0259419Field008Key00, fragment0259419Field008Value00) :: fragment0259419Acc00800
noncomputable def fragment0259419Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '5', '0', '4', '8', '2', '2', '3', '3', '7', '2', '"', ',']

theorem object_fragment0259419_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 430) (SourceJson.white (fragment0259419Field008Chars00 ++ tail)) fragment0259419Acc00800 =
      SourceJson.object (fuel + 429) (SourceJson.white tail) fragment0259419Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0259419_object_field_008"
  err.flush

noncomputable def fragment0259419Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0259419Field009Value00 : SourceJson := .str (String.ofList ['5', '8', '3', '7', '0', '2', '8', '4', '8', '3', '5', '0'])
noncomputable def fragment0259419Acc01000 : List (String × SourceJson) := (fragment0259419Field009Key00, fragment0259419Field009Value00) :: fragment0259419Acc00900
noncomputable def fragment0259419Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '8', '3', '7', '0', '2', '8', '4', '8', '3', '5', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0259419_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 429) (SourceJson.white (fragment0259419Field009Chars00 ++ tail)) fragment0259419Acc00900 =
      .ok (.obj (fragment0259419Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0259419_object_field_009"
  err.flush

noncomputable def fragment0259419Chars : List Char := '{' :: (fragment0259419Field000Chars00 ++ fragment0259419Field001Chars00 ++ fragment0259419Field002Chars00 ++ fragment0259419Field003Chars00 ++ fragment0259419Field004Chars00 ++ fragment0259419Field005Chars00 ++ fragment0259419Field006Chars00 ++ fragment0259419Field007Chars00 ++ fragment0259419Field008Chars00 ++ fragment0259419Field009Chars00)
noncomputable def fragment0259419Value : SourceJson := .obj (fragment0259419Acc01000.reverse)

theorem value_fragment0259419 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 439) (fragment0259419Chars ++ tail) =
      .ok (fragment0259419Value, tail) := by
  have hinput : fragment0259419Chars ++ tail = '{' :: (fragment0259419Field000Chars00 ++ (fragment0259419Field001Chars00 ++ (fragment0259419Field002Chars00 ++ (fragment0259419Field003Chars00 ++ (fragment0259419Field004Chars00 ++ (fragment0259419Field005Chars00 ++ (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0259419Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 439) (fragment0259419Chars ++ tail) =
        SourceJson.value (fuel + 439) ('{' :: (fragment0259419Field000Chars00 ++ (fragment0259419Field001Chars00 ++ (fragment0259419Field002Chars00 ++ (fragment0259419Field003Chars00 ++ (fragment0259419Field004Chars00 ++ (fragment0259419Field005Chars00 ++ (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 439)) hinput
    _ = SourceJson.object (fuel + 438) (SourceJson.white (fragment0259419Field000Chars00 ++ (fragment0259419Field001Chars00 ++ (fragment0259419Field002Chars00 ++ (fragment0259419Field003Chars00 ++ (fragment0259419Field004Chars00 ++ (fragment0259419Field005Chars00 ++ (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail)))))))))))) fragment0259419Acc00000 := by rfl
    _ = SourceJson.object (fuel + 437) (SourceJson.white (fragment0259419Field001Chars00 ++ (fragment0259419Field002Chars00 ++ (fragment0259419Field003Chars00 ++ (fragment0259419Field004Chars00 ++ (fragment0259419Field005Chars00 ++ (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail))))))))))) fragment0259419Acc00100 := object_fragment0259419_field_000 fuel (fragment0259419Field001Chars00 ++ (fragment0259419Field002Chars00 ++ (fragment0259419Field003Chars00 ++ (fragment0259419Field004Chars00 ++ (fragment0259419Field005Chars00 ++ (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 436) (SourceJson.white (fragment0259419Field002Chars00 ++ (fragment0259419Field003Chars00 ++ (fragment0259419Field004Chars00 ++ (fragment0259419Field005Chars00 ++ (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail)))))))))) fragment0259419Acc00200 := object_fragment0259419_field_001 fuel (fragment0259419Field002Chars00 ++ (fragment0259419Field003Chars00 ++ (fragment0259419Field004Chars00 ++ (fragment0259419Field005Chars00 ++ (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 435) (SourceJson.white (fragment0259419Field003Chars00 ++ (fragment0259419Field004Chars00 ++ (fragment0259419Field005Chars00 ++ (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail))))))))) fragment0259419Acc00300 := object_fragment0259419_field_002 fuel (fragment0259419Field003Chars00 ++ (fragment0259419Field004Chars00 ++ (fragment0259419Field005Chars00 ++ (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 434) (SourceJson.white (fragment0259419Field004Chars00 ++ (fragment0259419Field005Chars00 ++ (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail)))))))) fragment0259419Acc00400 := object_fragment0259419_field_003 fuel (fragment0259419Field004Chars00 ++ (fragment0259419Field005Chars00 ++ (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 433) (SourceJson.white (fragment0259419Field005Chars00 ++ (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail))))))) fragment0259419Acc00500 := object_fragment0259419_field_004 fuel (fragment0259419Field005Chars00 ++ (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 432) (SourceJson.white (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail)))))) fragment0259419Acc00600 := object_fragment0259419_field_005 fuel (fragment0259419Field006Chars00 ++ (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 431) (SourceJson.white (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail))))) fragment0259419Acc00700 := object_fragment0259419_field_006 fuel (fragment0259419Field007Chars00 ++ (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 430) (SourceJson.white (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail)))) fragment0259419Acc00800 := object_fragment0259419_field_007 fuel (fragment0259419Field008Chars00 ++ (fragment0259419Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 429) (SourceJson.white (fragment0259419Field009Chars00 ++ (tail))) fragment0259419Acc00900 := object_fragment0259419_field_008 fuel (fragment0259419Field009Chars00 ++ (tail))
    _ = .ok (fragment0259419Value, tail) := object_fragment0259419_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0064_before_reader"
  err.flush

noncomputable def chunk0064LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0064SuffixChars00 : List Char := [',']
noncomputable def chunk0064Chars00 : List Char := chunk0064LeadChars00 ++ fragment0246486Chars ++ chunk0064SuffixChars00
noncomputable def chunk0064Push00 (acc : List SourceJson) : List SourceJson := fragment0246486Value :: acc

noncomputable def chunk0064AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0064_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 593)
      (SourceJson.white (chunk0064LeadChars00 ++ (fragment0246486Chars ++ rest))) acc =
      (SourceJson.value (fuel + 592) (fragment0246486Chars ++ rest)).bind
        (chunk0064AfterValue00 (fuel + 592) acc) := by rfl

theorem array_chunk0064 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 593) (SourceJson.white (chunk0064Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 592) (SourceJson.white tail) (chunk0064Push00 acc) := by
  have hinput : chunk0064Chars00 ++ tail = chunk0064LeadChars00 ++ (fragment0246486Chars ++ (chunk0064SuffixChars00 ++ tail)) := by
    simp only [chunk0064Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 593) (SourceJson.white (chunk0064Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 593)
          (SourceJson.white (chunk0064LeadChars00 ++ (fragment0246486Chars ++ (chunk0064SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 593) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 592) (fragment0246486Chars ++ (chunk0064SuffixChars00 ++ tail))).bind
        (chunk0064AfterValue00 (fuel + 592) acc) := array_chunk0064_head fuel (chunk0064SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0246486Value, chunk0064SuffixChars00 ++ tail)).bind
        (chunk0064AfterValue00 (fuel + 592) acc) :=
      congrArg (fun result => result.bind (chunk0064AfterValue00 (fuel + 592) acc))
        (value_fragment0246486 (fuel + 355) (chunk0064SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 592) (SourceJson.white tail) (chunk0064Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0064_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0065_before_reader"
  err.flush

noncomputable def chunk0065LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0065SuffixChars00 : List Char := [',']
noncomputable def chunk0065Chars00 : List Char := chunk0065LeadChars00 ++ fragment0248090Chars ++ chunk0065SuffixChars00
noncomputable def chunk0065Push00 (acc : List SourceJson) : List SourceJson := fragment0248090Value :: acc

noncomputable def chunk0065AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0065_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 592)
      (SourceJson.white (chunk0065LeadChars00 ++ (fragment0248090Chars ++ rest))) acc =
      (SourceJson.value (fuel + 591) (fragment0248090Chars ++ rest)).bind
        (chunk0065AfterValue00 (fuel + 591) acc) := by rfl

theorem array_chunk0065 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 592) (SourceJson.white (chunk0065Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 591) (SourceJson.white tail) (chunk0065Push00 acc) := by
  have hinput : chunk0065Chars00 ++ tail = chunk0065LeadChars00 ++ (fragment0248090Chars ++ (chunk0065SuffixChars00 ++ tail)) := by
    simp only [chunk0065Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 592) (SourceJson.white (chunk0065Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 592)
          (SourceJson.white (chunk0065LeadChars00 ++ (fragment0248090Chars ++ (chunk0065SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 592) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 591) (fragment0248090Chars ++ (chunk0065SuffixChars00 ++ tail))).bind
        (chunk0065AfterValue00 (fuel + 591) acc) := array_chunk0065_head fuel (chunk0065SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0248090Value, chunk0065SuffixChars00 ++ tail)).bind
        (chunk0065AfterValue00 (fuel + 591) acc) :=
      congrArg (fun result => result.bind (chunk0065AfterValue00 (fuel + 591) acc))
        (value_fragment0248090 (fuel + 151) (chunk0065SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 591) (SourceJson.white tail) (chunk0065Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0065_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0066_before_reader"
  err.flush

noncomputable def chunk0066LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0066SuffixChars00 : List Char := [',']
noncomputable def chunk0066Chars00 : List Char := chunk0066LeadChars00 ++ fragment0250111Chars ++ chunk0066SuffixChars00
noncomputable def chunk0066Push00 (acc : List SourceJson) : List SourceJson := fragment0250111Value :: acc

noncomputable def chunk0066AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0066_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 591)
      (SourceJson.white (chunk0066LeadChars00 ++ (fragment0250111Chars ++ rest))) acc =
      (SourceJson.value (fuel + 590) (fragment0250111Chars ++ rest)).bind
        (chunk0066AfterValue00 (fuel + 590) acc) := by rfl

theorem array_chunk0066 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 591) (SourceJson.white (chunk0066Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 590) (SourceJson.white tail) (chunk0066Push00 acc) := by
  have hinput : chunk0066Chars00 ++ tail = chunk0066LeadChars00 ++ (fragment0250111Chars ++ (chunk0066SuffixChars00 ++ tail)) := by
    simp only [chunk0066Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 591) (SourceJson.white (chunk0066Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 591)
          (SourceJson.white (chunk0066LeadChars00 ++ (fragment0250111Chars ++ (chunk0066SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 591) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 590) (fragment0250111Chars ++ (chunk0066SuffixChars00 ++ tail))).bind
        (chunk0066AfterValue00 (fuel + 590) acc) := array_chunk0066_head fuel (chunk0066SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0250111Value, chunk0066SuffixChars00 ++ tail)).bind
        (chunk0066AfterValue00 (fuel + 590) acc) :=
      congrArg (fun result => result.bind (chunk0066AfterValue00 (fuel + 590) acc))
        (value_fragment0250111 (fuel + 341) (chunk0066SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 590) (SourceJson.white tail) (chunk0066Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0066_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0067_before_reader"
  err.flush

noncomputable def chunk0067LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0067SuffixChars00 : List Char := [',']
noncomputable def chunk0067Chars00 : List Char := chunk0067LeadChars00 ++ fragment0251756Chars ++ chunk0067SuffixChars00
noncomputable def chunk0067Push00 (acc : List SourceJson) : List SourceJson := fragment0251756Value :: acc

noncomputable def chunk0067AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0067_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 590)
      (SourceJson.white (chunk0067LeadChars00 ++ (fragment0251756Chars ++ rest))) acc =
      (SourceJson.value (fuel + 589) (fragment0251756Chars ++ rest)).bind
        (chunk0067AfterValue00 (fuel + 589) acc) := by rfl

theorem array_chunk0067 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 590) (SourceJson.white (chunk0067Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 589) (SourceJson.white tail) (chunk0067Push00 acc) := by
  have hinput : chunk0067Chars00 ++ tail = chunk0067LeadChars00 ++ (fragment0251756Chars ++ (chunk0067SuffixChars00 ++ tail)) := by
    simp only [chunk0067Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 590) (SourceJson.white (chunk0067Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 590)
          (SourceJson.white (chunk0067LeadChars00 ++ (fragment0251756Chars ++ (chunk0067SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 590) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 589) (fragment0251756Chars ++ (chunk0067SuffixChars00 ++ tail))).bind
        (chunk0067AfterValue00 (fuel + 589) acc) := array_chunk0067_head fuel (chunk0067SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0251756Value, chunk0067SuffixChars00 ++ tail)).bind
        (chunk0067AfterValue00 (fuel + 589) acc) :=
      congrArg (fun result => result.bind (chunk0067AfterValue00 (fuel + 589) acc))
        (value_fragment0251756 (fuel + 167) (chunk0067SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 589) (SourceJson.white tail) (chunk0067Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0067_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0068_before_reader"
  err.flush

noncomputable def chunk0068LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0068SuffixChars00 : List Char := [',']
noncomputable def chunk0068Chars00 : List Char := chunk0068LeadChars00 ++ fragment0253745Chars ++ chunk0068SuffixChars00
noncomputable def chunk0068Push00 (acc : List SourceJson) : List SourceJson := fragment0253745Value :: acc

noncomputable def chunk0068AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0068_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 589)
      (SourceJson.white (chunk0068LeadChars00 ++ (fragment0253745Chars ++ rest))) acc =
      (SourceJson.value (fuel + 588) (fragment0253745Chars ++ rest)).bind
        (chunk0068AfterValue00 (fuel + 588) acc) := by rfl

theorem array_chunk0068 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 589) (SourceJson.white (chunk0068Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 588) (SourceJson.white tail) (chunk0068Push00 acc) := by
  have hinput : chunk0068Chars00 ++ tail = chunk0068LeadChars00 ++ (fragment0253745Chars ++ (chunk0068SuffixChars00 ++ tail)) := by
    simp only [chunk0068Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 589) (SourceJson.white (chunk0068Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 589)
          (SourceJson.white (chunk0068LeadChars00 ++ (fragment0253745Chars ++ (chunk0068SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 589) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 588) (fragment0253745Chars ++ (chunk0068SuffixChars00 ++ tail))).bind
        (chunk0068AfterValue00 (fuel + 588) acc) := array_chunk0068_head fuel (chunk0068SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0253745Value, chunk0068SuffixChars00 ++ tail)).bind
        (chunk0068AfterValue00 (fuel + 588) acc) :=
      congrArg (fun result => result.bind (chunk0068AfterValue00 (fuel + 588) acc))
        (value_fragment0253745 (fuel + 113) (chunk0068SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 588) (SourceJson.white tail) (chunk0068Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0068_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0069_before_reader"
  err.flush

noncomputable def chunk0069LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0069SuffixChars00 : List Char := [',']
noncomputable def chunk0069Chars00 : List Char := chunk0069LeadChars00 ++ fragment0255834Chars ++ chunk0069SuffixChars00
noncomputable def chunk0069Push00 (acc : List SourceJson) : List SourceJson := fragment0255834Value :: acc

noncomputable def chunk0069AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0069_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 588)
      (SourceJson.white (chunk0069LeadChars00 ++ (fragment0255834Chars ++ rest))) acc =
      (SourceJson.value (fuel + 587) (fragment0255834Chars ++ rest)).bind
        (chunk0069AfterValue00 (fuel + 587) acc) := by rfl

theorem array_chunk0069 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 588) (SourceJson.white (chunk0069Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 587) (SourceJson.white tail) (chunk0069Push00 acc) := by
  have hinput : chunk0069Chars00 ++ tail = chunk0069LeadChars00 ++ (fragment0255834Chars ++ (chunk0069SuffixChars00 ++ tail)) := by
    simp only [chunk0069Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 588) (SourceJson.white (chunk0069Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 588)
          (SourceJson.white (chunk0069LeadChars00 ++ (fragment0255834Chars ++ (chunk0069SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 588) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 587) (fragment0255834Chars ++ (chunk0069SuffixChars00 ++ tail))).bind
        (chunk0069AfterValue00 (fuel + 587) acc) := array_chunk0069_head fuel (chunk0069SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0255834Value, chunk0069SuffixChars00 ++ tail)).bind
        (chunk0069AfterValue00 (fuel + 587) acc) :=
      congrArg (fun result => result.bind (chunk0069AfterValue00 (fuel + 587) acc))
        (value_fragment0255834 (fuel + 184) (chunk0069SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 587) (SourceJson.white tail) (chunk0069Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0069_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0070_before_reader"
  err.flush

noncomputable def chunk0070LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0070SuffixChars00 : List Char := [',']
noncomputable def chunk0070Chars00 : List Char := chunk0070LeadChars00 ++ fragment0257782Chars ++ chunk0070SuffixChars00
noncomputable def chunk0070Push00 (acc : List SourceJson) : List SourceJson := fragment0257782Value :: acc

noncomputable def chunk0070AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0070_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 587)
      (SourceJson.white (chunk0070LeadChars00 ++ (fragment0257782Chars ++ rest))) acc =
      (SourceJson.value (fuel + 586) (fragment0257782Chars ++ rest)).bind
        (chunk0070AfterValue00 (fuel + 586) acc) := by rfl

theorem array_chunk0070 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 587) (SourceJson.white (chunk0070Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 586) (SourceJson.white tail) (chunk0070Push00 acc) := by
  have hinput : chunk0070Chars00 ++ tail = chunk0070LeadChars00 ++ (fragment0257782Chars ++ (chunk0070SuffixChars00 ++ tail)) := by
    simp only [chunk0070Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 587) (SourceJson.white (chunk0070Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 587)
          (SourceJson.white (chunk0070LeadChars00 ++ (fragment0257782Chars ++ (chunk0070SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 587) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 586) (fragment0257782Chars ++ (chunk0070SuffixChars00 ++ tail))).bind
        (chunk0070AfterValue00 (fuel + 586) acc) := array_chunk0070_head fuel (chunk0070SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0257782Value, chunk0070SuffixChars00 ++ tail)).bind
        (chunk0070AfterValue00 (fuel + 586) acc) :=
      congrArg (fun result => result.bind (chunk0070AfterValue00 (fuel + 586) acc))
        (value_fragment0257782 (fuel + 342) (chunk0070SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 586) (SourceJson.white tail) (chunk0070Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0070_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0071_before_reader"
  err.flush

noncomputable def chunk0071LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0071SuffixChars00 : List Char := [',']
noncomputable def chunk0071Chars00 : List Char := chunk0071LeadChars00 ++ fragment0259419Chars ++ chunk0071SuffixChars00
noncomputable def chunk0071Push00 (acc : List SourceJson) : List SourceJson := fragment0259419Value :: acc

noncomputable def chunk0071AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0071_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 586)
      (SourceJson.white (chunk0071LeadChars00 ++ (fragment0259419Chars ++ rest))) acc =
      (SourceJson.value (fuel + 585) (fragment0259419Chars ++ rest)).bind
        (chunk0071AfterValue00 (fuel + 585) acc) := by rfl

theorem array_chunk0071 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 586) (SourceJson.white (chunk0071Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 585) (SourceJson.white tail) (chunk0071Push00 acc) := by
  have hinput : chunk0071Chars00 ++ tail = chunk0071LeadChars00 ++ (fragment0259419Chars ++ (chunk0071SuffixChars00 ++ tail)) := by
    simp only [chunk0071Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 586) (SourceJson.white (chunk0071Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 586)
          (SourceJson.white (chunk0071LeadChars00 ++ (fragment0259419Chars ++ (chunk0071SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 586) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 585) (fragment0259419Chars ++ (chunk0071SuffixChars00 ++ tail))).bind
        (chunk0071AfterValue00 (fuel + 585) acc) := array_chunk0071_head fuel (chunk0071SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0259419Value, chunk0071SuffixChars00 ++ tail)).bind
        (chunk0071AfterValue00 (fuel + 585) acc) :=
      congrArg (fun result => result.bind (chunk0071AfterValue00 (fuel + 585) acc))
        (value_fragment0259419 (fuel + 146) (chunk0071SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 585) (SourceJson.white tail) (chunk0071Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0071_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0064Chars00 ++ chunk0065Chars00 ++ chunk0066Chars00 ++ chunk0067Chars00 ++ chunk0068Chars00 ++ chunk0069Chars00 ++ chunk0070Chars00 ++ chunk0071Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0071Push00 (chunk0070Push00 (chunk0069Push00 (chunk0068Push00 (chunk0067Push00 (chunk0066Push00 (chunk0065Push00 (chunk0064Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 593) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 585) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0064Chars00 ++ (chunk0065Chars00 ++ (chunk0066Chars00 ++ (chunk0067Chars00 ++ (chunk0068Chars00 ++ (chunk0069Chars00 ++ (chunk0070Chars00 ++ (chunk0071Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 593) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 593) (SourceJson.white (chunk0064Chars00 ++ (chunk0065Chars00 ++ (chunk0066Chars00 ++ (chunk0067Chars00 ++ (chunk0068Chars00 ++ (chunk0069Chars00 ++ (chunk0070Chars00 ++ (chunk0071Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 593) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 592) (SourceJson.white (chunk0065Chars00 ++ (chunk0066Chars00 ++ (chunk0067Chars00 ++ (chunk0068Chars00 ++ (chunk0069Chars00 ++ (chunk0070Chars00 ++ (chunk0071Chars00 ++ (tail))))))))) (chunk0064Push00 (acc)) := array_chunk0064 fuel (chunk0065Chars00 ++ (chunk0066Chars00 ++ (chunk0067Chars00 ++ (chunk0068Chars00 ++ (chunk0069Chars00 ++ (chunk0070Chars00 ++ (chunk0071Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 591) (SourceJson.white (chunk0066Chars00 ++ (chunk0067Chars00 ++ (chunk0068Chars00 ++ (chunk0069Chars00 ++ (chunk0070Chars00 ++ (chunk0071Chars00 ++ (tail)))))))) (chunk0065Push00 (chunk0064Push00 (acc))) := array_chunk0065 fuel (chunk0066Chars00 ++ (chunk0067Chars00 ++ (chunk0068Chars00 ++ (chunk0069Chars00 ++ (chunk0070Chars00 ++ (chunk0071Chars00 ++ (tail))))))) (chunk0064Push00 (acc))
    _ = SourceJson.array (fuel + 590) (SourceJson.white (chunk0067Chars00 ++ (chunk0068Chars00 ++ (chunk0069Chars00 ++ (chunk0070Chars00 ++ (chunk0071Chars00 ++ (tail))))))) (chunk0066Push00 (chunk0065Push00 (chunk0064Push00 (acc)))) := array_chunk0066 fuel (chunk0067Chars00 ++ (chunk0068Chars00 ++ (chunk0069Chars00 ++ (chunk0070Chars00 ++ (chunk0071Chars00 ++ (tail)))))) (chunk0065Push00 (chunk0064Push00 (acc)))
    _ = SourceJson.array (fuel + 589) (SourceJson.white (chunk0068Chars00 ++ (chunk0069Chars00 ++ (chunk0070Chars00 ++ (chunk0071Chars00 ++ (tail)))))) (chunk0067Push00 (chunk0066Push00 (chunk0065Push00 (chunk0064Push00 (acc))))) := array_chunk0067 fuel (chunk0068Chars00 ++ (chunk0069Chars00 ++ (chunk0070Chars00 ++ (chunk0071Chars00 ++ (tail))))) (chunk0066Push00 (chunk0065Push00 (chunk0064Push00 (acc))))
    _ = SourceJson.array (fuel + 588) (SourceJson.white (chunk0069Chars00 ++ (chunk0070Chars00 ++ (chunk0071Chars00 ++ (tail))))) (chunk0068Push00 (chunk0067Push00 (chunk0066Push00 (chunk0065Push00 (chunk0064Push00 (acc)))))) := array_chunk0068 fuel (chunk0069Chars00 ++ (chunk0070Chars00 ++ (chunk0071Chars00 ++ (tail)))) (chunk0067Push00 (chunk0066Push00 (chunk0065Push00 (chunk0064Push00 (acc)))))
    _ = SourceJson.array (fuel + 587) (SourceJson.white (chunk0070Chars00 ++ (chunk0071Chars00 ++ (tail)))) (chunk0069Push00 (chunk0068Push00 (chunk0067Push00 (chunk0066Push00 (chunk0065Push00 (chunk0064Push00 (acc))))))) := array_chunk0069 fuel (chunk0070Chars00 ++ (chunk0071Chars00 ++ (tail))) (chunk0068Push00 (chunk0067Push00 (chunk0066Push00 (chunk0065Push00 (chunk0064Push00 (acc))))))
    _ = SourceJson.array (fuel + 586) (SourceJson.white (chunk0071Chars00 ++ (tail))) (chunk0070Push00 (chunk0069Push00 (chunk0068Push00 (chunk0067Push00 (chunk0066Push00 (chunk0065Push00 (chunk0064Push00 (acc)))))))) := array_chunk0070 fuel (chunk0071Chars00 ++ (tail)) (chunk0069Push00 (chunk0068Push00 (chunk0067Push00 (chunk0066Push00 (chunk0065Push00 (chunk0064Push00 (acc)))))))
    _ = SourceJson.array (fuel + 585) (SourceJson.white tail) (blockPush acc) := array_chunk0071 fuel (tail) (chunk0070Push00 (chunk0069Push00 (chunk0068Push00 (chunk0067Push00 (chunk0066Push00 (chunk0065Push00 (chunk0064Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 246480).take 14941 = blockChars := by rfl

theorem block_original_split : sourceRest 246480 = blockChars ++ sourceRest 261421 := by
  calc
    sourceRest 246480 = (sourceRest 246480).take 14941 ++ (sourceRest 246480).drop 14941 :=
      (List.take_append_drop 14941 (sourceRest 246480)).symm
    _ = blockChars ++ (sourceRest 246480).drop 14941 :=
      congrArg (fun part => part ++ (sourceRest 246480).drop 14941) block_original_prefix
    _ = blockChars ++ sourceRest 261421 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 246480 14941)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 593) (SourceJson.white (sourceRest 246480)) acc =
      SourceJson.array (fuel + 585) (SourceJson.white (sourceRest 261421)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 593) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 261421) acc)

#print axioms object_fragment0246486_field_000
#print axioms object_fragment0246486_field_001
#print axioms object_fragment0246486_field_002
#print axioms object_fragment0246486_field_003
#print axioms object_fragment0246486_field_004
#print axioms object_fragment0246486_field_005
#print axioms object_fragment0246486_field_006
#print axioms object_fragment0246486_field_007
#print axioms object_fragment0246486_field_008
#print axioms object_fragment0246486_field_009
#print axioms value_fragment0246486
#print axioms object_fragment0248090_field_000
#print axioms object_fragment0248090_field_001
#print axioms object_fragment0248090_field_002
#print axioms object_fragment0248090_field_003
#print axioms object_fragment0248090_field_004
#print axioms object_fragment0248090_field_005
#print axioms object_fragment0248090_field_006
#print axioms object_fragment0248090_field_007
#print axioms object_fragment0248090_field_008
#print axioms object_fragment0248090_field_009
#print axioms value_fragment0248090
#print axioms object_fragment0250111_field_000
#print axioms object_fragment0250111_field_001
#print axioms object_fragment0250111_field_002
#print axioms object_fragment0250111_field_003
#print axioms object_fragment0250111_field_004
#print axioms object_fragment0250111_field_005
#print axioms object_fragment0250111_field_006
#print axioms object_fragment0250111_field_007
#print axioms object_fragment0250111_field_008
#print axioms object_fragment0250111_field_009
#print axioms value_fragment0250111
#print axioms object_fragment0251756_field_000
#print axioms object_fragment0251756_field_001
#print axioms object_fragment0251756_field_002
#print axioms object_fragment0251756_field_003
#print axioms object_fragment0251756_field_004
#print axioms object_fragment0251756_field_005
#print axioms object_fragment0251756_field_006
#print axioms object_fragment0251756_field_007
#print axioms object_fragment0251756_field_008
#print axioms object_fragment0251756_field_009
#print axioms value_fragment0251756
#print axioms object_fragment0253745_field_000
#print axioms object_fragment0253745_field_001
#print axioms object_fragment0253745_field_002
#print axioms object_fragment0253745_field_003
#print axioms object_fragment0253745_field_004
#print axioms object_fragment0253745_field_005
#print axioms object_fragment0253745_field_006
#print axioms object_fragment0253745_field_007
#print axioms object_fragment0253745_field_008
#print axioms object_fragment0253745_field_009
#print axioms value_fragment0253745
#print axioms object_fragment0255834_field_000
#print axioms object_fragment0255834_field_001
#print axioms object_fragment0255834_field_002
#print axioms object_fragment0255834_field_003
#print axioms object_fragment0255834_field_004
#print axioms object_fragment0255834_field_005
#print axioms object_fragment0255834_field_006
#print axioms object_fragment0255834_field_007
#print axioms object_fragment0255834_field_008
#print axioms object_fragment0255834_field_009
#print axioms value_fragment0255834
#print axioms object_fragment0257782_field_000
#print axioms object_fragment0257782_field_001
#print axioms object_fragment0257782_field_002
#print axioms object_fragment0257782_field_003
#print axioms object_fragment0257782_field_004
#print axioms object_fragment0257782_field_005
#print axioms object_fragment0257782_field_006
#print axioms object_fragment0257782_field_007
#print axioms object_fragment0257782_field_008
#print axioms object_fragment0257782_field_009
#print axioms value_fragment0257782
#print axioms object_fragment0259419_field_000
#print axioms object_fragment0259419_field_001
#print axioms object_fragment0259419_field_002
#print axioms object_fragment0259419_field_003
#print axioms object_fragment0259419_field_004
#print axioms object_fragment0259419_field_005
#print axioms object_fragment0259419_field_006
#print axioms object_fragment0259419_field_007
#print axioms object_fragment0259419_field_008
#print axioms object_fragment0259419_field_009
#print axioms value_fragment0259419
#print axioms array_chunk0064_head
#print axioms array_chunk0064
#print axioms array_chunk0065_head
#print axioms array_chunk0065
#print axioms array_chunk0066_head
#print axioms array_chunk0066
#print axioms array_chunk0067_head
#print axioms array_chunk0067
#print axioms array_chunk0068_head
#print axioms array_chunk0068
#print axioms array_chunk0069_head
#print axioms array_chunk0069
#print axioms array_chunk0070_head
#print axioms array_chunk0070
#print axioms array_chunk0071_head
#print axioms array_chunk0071
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock008

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
