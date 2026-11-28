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

namespace SimplicesBlock014

noncomputable def fragment0333884Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0333884Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0333884Field000Value00 : SourceJson := .number (String.ofList ['1', '1', '2'])
noncomputable def fragment0333884Acc00100 : List (String × SourceJson) := (fragment0333884Field000Key00, fragment0333884Field000Value00) :: fragment0333884Acc00000
noncomputable def fragment0333884Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '2', ',']

theorem object_fragment0333884_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0333884Field000Chars00 ++ tail)) fragment0333884Acc00000 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0333884Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333884_object_field_000"
  err.flush

noncomputable def fragment0333884Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0333884Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7'])]
noncomputable def fragment0333884Acc00200 : List (String × SourceJson) := (fragment0333884Field001Key00, fragment0333884Field001Value00) :: fragment0333884Acc00100
noncomputable def fragment0333884Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0333884_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0333884Field001Chars00 ++ tail)) fragment0333884Acc00100 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0333884Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333884_object_field_001"
  err.flush

noncomputable def fragment0333884Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0333884Field002Value00 : SourceJson := .str (String.ofList ['4', '2', '9', '6', '2', '9', '8', '0', '9', '7', '2', '1', '3', '3', '8', '7', '6', '2', '8', '6', '2', '5', '3', '7', '3', '2', '2', '5', '8', '3', '7', '4', '0', '3', '7', '3', '4', '3', '/', '5', '3', '0', '1', '4', '1', '1', '5', '1', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0333884Acc00300 : List (String × SourceJson) := (fragment0333884Field002Key00, fragment0333884Field002Value00) :: fragment0333884Acc00200
noncomputable def fragment0333884Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '2', '9', '6', '2', '9', '8', '0', '9', '7', '2', '1', '3', '3', '8', '7', '6', '2', '8', '6', '2', '5', '3', '7', '3', '2', '2', '5', '8', '3', '7', '4', '0', '3', '7', '3', '4', '3', '/', '5', '3', '0', '1', '4', '1', '1', '5', '1', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0333884_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0333884Field002Chars00 ++ tail)) fragment0333884Acc00200 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0333884Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333884_object_field_002"
  err.flush

noncomputable def fragment0333884Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0333884Field003Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0333884Acc00400 : List (String × SourceJson) := (fragment0333884Field003Key00, fragment0333884Field003Value00) :: fragment0333884Acc00300
noncomputable def fragment0333884Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0333884_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0333884Field003Chars00 ++ tail)) fragment0333884Acc00300 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0333884Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333884_object_field_003"
  err.flush

noncomputable def fragment0333884Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0333884Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0333884Acc00500 : List (String × SourceJson) := (fragment0333884Field004Key00, fragment0333884Field004Value00) :: fragment0333884Acc00400
noncomputable def fragment0333884Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0333884_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0333884Field004Chars00 ++ tail)) fragment0333884Acc00400 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0333884Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333884_object_field_004"
  err.flush

noncomputable def fragment0333884Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0333884Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '3', '8', '6', '7', '6', '1', '1', '9', '7', '7', '7', '9', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '3', '2', '9', '2', '2', '6', '4', '4', '7', '1', '9', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '4', '7', '6', '1', '1', '7', '9', '9', '7', '3', '3', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '7', '5', '2', '2', '0', '7', '7', '9', '1', '7', '/', '3', '0', '9', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '6', '1', '6', '2', '5', '3', '7', '9', '7', '2', '9', '/', '1', '2', '3', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '9', '9', '6', '7', '7', '2', '7', '6', '7', '4', '7', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '5', '3', '3', '9', '6', '4', '8', '8', '7', '/', '1', '3', '2', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '7', '8', '0', '1', '4', '5', '0', '0', '2', '7', '/', '4', '6', '4', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '9', '7', '4', '6', '5', '2', '4', '5', '2', '9', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '9', '7', '4', '4', '0', '4', '8', '2', '0', '9', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0333884Acc00600 : List (String × SourceJson) := (fragment0333884Field005Key00, fragment0333884Field005Value00) :: fragment0333884Acc00500
noncomputable def fragment0333884Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '8', '6', '7', '6', '1', '1', '9', '7', '7', '7', '9', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '3', '2', '9', '2', '2', '6', '4', '4', '7', '1', '9', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '4', '7', '6', '1', '1', '7', '9', '9', '7', '3', '3', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '7', '5', '2', '2', '0', '7', '7', '9', '1', '7', '/', '3', '0', '9', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '1', '6', '2', '5', '3', '7', '9', '7', '2', '9', '/', '1', '2', '3', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '9', '9', '6', '7', '7', '2', '7', '6', '7', '4', '7', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '5', '3', '3', '9', '6', '4', '8', '8', '7', '/', '1', '3', '2', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '8', '0', '1', '4', '5', '0', '0', '2', '7', '/', '4', '6', '4', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '9', '7', '4', '6', '5', '2', '4', '5', '2', '9', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '9', '7', '4', '4', '0', '4', '8', '2', '0', '9', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0333884_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0333884Field005Chars00 ++ tail)) fragment0333884Acc00500 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0333884Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333884_object_field_005"
  err.flush

noncomputable def fragment0333884Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0333884Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '8', '2', '4', '0', '8', '5', '5', '2', '5', '9', '8', '5', '2', '6', '3', '2', '1', '3', '5', '0', '7', '6', '4', '7', '8', '9', '6', '6', '3', '8', '4', '0', '7', '2', '4', '1', '5', '1', '7', '4', '6', '8', '7', '5', '/', '2', '9', '1', '7', '1', '5', '7', '3', '2', '7', '2', '2', '0', '4', '8', '4', '4', '3', '7', '7', '1', '9', '1', '4', '8', '4', '0', '9', '7', '7', '6', '1', '8', '5', '4', '1', '8', '0', '1', '9', '0', '2', '5', '3', '9', '4', '6', '4', '4', '0', '6', '8', '1', '1', '5', '0', '0', '0', '2', '7', '9', '7'])
noncomputable def fragment0333884Acc00700 : List (String × SourceJson) := (fragment0333884Field006Key00, fragment0333884Field006Value00) :: fragment0333884Acc00600
noncomputable def fragment0333884Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '8', '2', '4', '0', '8', '5', '5', '2', '5', '9', '8', '5', '2', '6', '3', '2', '1', '3', '5', '0', '7', '6', '4', '7', '8', '9', '6', '6', '3', '8', '4', '0', '7', '2', '4', '1', '5', '1', '7', '4', '6', '8', '7', '5', '/', '2', '9', '1', '7', '1', '5', '7', '3', '2', '7', '2', '2', '0', '4', '8', '4', '4', '3', '7', '7', '1', '9', '1', '4', '8', '4', '0', '9', '7', '7', '6', '1', '8', '5', '4', '1', '8', '0', '1', '9', '0', '2', '5', '3', '9', '4', '6', '4', '4', '0', '6', '8', '1', '1', '5', '0', '0', '0', '2', '7', '9', '7', '"', ',']

theorem object_fragment0333884_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0333884Field006Chars00 ++ tail)) fragment0333884Acc00600 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0333884Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333884_object_field_006"
  err.flush

noncomputable def fragment0333884Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0333884Field007Value00 : SourceJson := .str (String.ofList ['1', '5', '2', '4', '9', '6', '5', '7', '7', '6', '2', '5', '4', '2', '3', '9', '5', '4', '5', '3', '5', '4', '9', '5', '2', '8', '0', '2', '9', '8', '4', '0', '5', '4', '8', '9', '8', '1', '7', '9', '4', '6', '2', '7', '8', '7', '2', '5', '8', '2', '2', '9', '0', '1', '4', '1', '7', '7', '1', '0', '4', '6', '0', '6', '5', '5', '2', '8', '1', '1', '1', '5', '7', '0', '2', '6', '3', '2', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '6', '6', '3', '7', '7', '8', '6', '2', '3', '1', '1', '8', '7', '0', '4', '2', '2', '0', '5', '2', '5', '3', '6', '6', '2', '0', '0', '2', '2', '0', '3', '6', '1', '4', '9', '1', '7', '2', '6', '7', '2', '2', '5', '3', '2', '6', '7', '1', '4', '8', '4', '7', '5', '2', '8', '9', '7', '9', '6', '6', '8', '8', '2', '3', '8', '7', '7', '4', '5', '8', '9', '0', '3', '3', '5', '1', '6', '6', '7', '0', '6', '5', '4', '9', '0', '7', '8', '9', '7', '9', '8', '5', '7', '6', '0', '4', '4', '4', '0', '6', '5', '7', '9', '4', '2', '6', '6', '9', '3', '4', '8', '3', '9', '3', '0', '9', '7'])
noncomputable def fragment0333884Acc00800 : List (String × SourceJson) := (fragment0333884Field007Key00, fragment0333884Field007Value00) :: fragment0333884Acc00700
noncomputable def fragment0333884Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '2', '4', '9', '6', '5', '7', '7', '6', '2', '5', '4', '2', '3', '9', '5', '4', '5', '3', '5', '4', '9', '5', '2', '8', '0', '2', '9', '8', '4', '0', '5', '4', '8', '9', '8', '1', '7', '9', '4', '6', '2', '7', '8', '7', '2', '5', '8', '2', '2', '9', '0', '1', '4', '1', '7', '7', '1', '0', '4', '6', '0', '6', '5', '5', '2', '8', '1', '1', '1', '5', '7', '0', '2', '6', '3', '2', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '6', '6', '3', '7', '7', '8', '6', '2', '3', '1', '1', '8', '7', '0', '4', '2', '2', '0', '5', '2', '5', '3', '6', '6', '2', '0', '0', '2', '2', '0', '3', '6', '1', '4', '9', '1', '7', '2', '6', '7', '2', '2', '5', '3', '2', '6', '7', '1', '4', '8', '4', '7', '5', '2', '8', '9', '7', '9', '6', '6', '8', '8', '2', '3', '8', '7', '7', '4', '5', '8', '9', '0', '3', '3', '5', '1', '6', '6', '7', '0', '6', '5', '4', '9', '0', '7', '8', '9', '7', '9', '8', '5', '7', '6', '0', '4', '4', '4', '0', '6', '5', '7', '9', '4', '2', '6', '6', '9', '3', '4', '8', '3', '9', '3', '0', '9', '7', '"', ',']

theorem object_fragment0333884_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0333884Field007Chars00 ++ tail)) fragment0333884Acc00700 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0333884Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333884_object_field_007"
  err.flush

noncomputable def fragment0333884Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0333884Field008Value00 : SourceJson := .str (String.ofList ['5', '1', '1', '2', '5', '0', '3', '5', '0', '9', '2', '1', '6'])
noncomputable def fragment0333884Acc00900 : List (String × SourceJson) := (fragment0333884Field008Key00, fragment0333884Field008Value00) :: fragment0333884Acc00800
noncomputable def fragment0333884Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '1', '1', '2', '5', '0', '3', '5', '0', '9', '2', '1', '6', '"', ',']

theorem object_fragment0333884_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0333884Field008Chars00 ++ tail)) fragment0333884Acc00800 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0333884Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333884_object_field_008"
  err.flush

noncomputable def fragment0333884Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0333884Field009Value00 : SourceJson := .str (String.ofList ['2', '1', '3', '3', '2', '0', '9', '0', '1', '8', '0', '3', '2', '4'])
noncomputable def fragment0333884Acc01000 : List (String × SourceJson) := (fragment0333884Field009Key00, fragment0333884Field009Value00) :: fragment0333884Acc00900
noncomputable def fragment0333884Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '1', '3', '3', '2', '0', '9', '0', '1', '8', '0', '3', '2', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0333884_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0333884Field009Chars00 ++ tail)) fragment0333884Acc00900 =
      .ok (.obj (fragment0333884Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0333884_object_field_009"
  err.flush

noncomputable def fragment0333884Chars : List Char := '{' :: (fragment0333884Field000Chars00 ++ fragment0333884Field001Chars00 ++ fragment0333884Field002Chars00 ++ fragment0333884Field003Chars00 ++ fragment0333884Field004Chars00 ++ fragment0333884Field005Chars00 ++ fragment0333884Field006Chars00 ++ fragment0333884Field007Chars00 ++ fragment0333884Field008Chars00 ++ fragment0333884Field009Chars00)
noncomputable def fragment0333884Value : SourceJson := .obj (fragment0333884Acc01000.reverse)

theorem value_fragment0333884 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 233) (fragment0333884Chars ++ tail) =
      .ok (fragment0333884Value, tail) := by
  have hinput : fragment0333884Chars ++ tail = '{' :: (fragment0333884Field000Chars00 ++ (fragment0333884Field001Chars00 ++ (fragment0333884Field002Chars00 ++ (fragment0333884Field003Chars00 ++ (fragment0333884Field004Chars00 ++ (fragment0333884Field005Chars00 ++ (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0333884Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 233) (fragment0333884Chars ++ tail) =
        SourceJson.value (fuel + 233) ('{' :: (fragment0333884Field000Chars00 ++ (fragment0333884Field001Chars00 ++ (fragment0333884Field002Chars00 ++ (fragment0333884Field003Chars00 ++ (fragment0333884Field004Chars00 ++ (fragment0333884Field005Chars00 ++ (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 233)) hinput
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0333884Field000Chars00 ++ (fragment0333884Field001Chars00 ++ (fragment0333884Field002Chars00 ++ (fragment0333884Field003Chars00 ++ (fragment0333884Field004Chars00 ++ (fragment0333884Field005Chars00 ++ (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail)))))))))))) fragment0333884Acc00000 := by rfl
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0333884Field001Chars00 ++ (fragment0333884Field002Chars00 ++ (fragment0333884Field003Chars00 ++ (fragment0333884Field004Chars00 ++ (fragment0333884Field005Chars00 ++ (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail))))))))))) fragment0333884Acc00100 := object_fragment0333884_field_000 fuel (fragment0333884Field001Chars00 ++ (fragment0333884Field002Chars00 ++ (fragment0333884Field003Chars00 ++ (fragment0333884Field004Chars00 ++ (fragment0333884Field005Chars00 ++ (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0333884Field002Chars00 ++ (fragment0333884Field003Chars00 ++ (fragment0333884Field004Chars00 ++ (fragment0333884Field005Chars00 ++ (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail)))))))))) fragment0333884Acc00200 := object_fragment0333884_field_001 fuel (fragment0333884Field002Chars00 ++ (fragment0333884Field003Chars00 ++ (fragment0333884Field004Chars00 ++ (fragment0333884Field005Chars00 ++ (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0333884Field003Chars00 ++ (fragment0333884Field004Chars00 ++ (fragment0333884Field005Chars00 ++ (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail))))))))) fragment0333884Acc00300 := object_fragment0333884_field_002 fuel (fragment0333884Field003Chars00 ++ (fragment0333884Field004Chars00 ++ (fragment0333884Field005Chars00 ++ (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0333884Field004Chars00 ++ (fragment0333884Field005Chars00 ++ (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail)))))))) fragment0333884Acc00400 := object_fragment0333884_field_003 fuel (fragment0333884Field004Chars00 ++ (fragment0333884Field005Chars00 ++ (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0333884Field005Chars00 ++ (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail))))))) fragment0333884Acc00500 := object_fragment0333884_field_004 fuel (fragment0333884Field005Chars00 ++ (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail)))))) fragment0333884Acc00600 := object_fragment0333884_field_005 fuel (fragment0333884Field006Chars00 ++ (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail))))) fragment0333884Acc00700 := object_fragment0333884_field_006 fuel (fragment0333884Field007Chars00 ++ (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail)))) fragment0333884Acc00800 := object_fragment0333884_field_007 fuel (fragment0333884Field008Chars00 ++ (fragment0333884Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0333884Field009Chars00 ++ (tail))) fragment0333884Acc00900 := object_fragment0333884_field_008 fuel (fragment0333884Field009Chars00 ++ (tail))
    _ = .ok (fragment0333884Value, tail) := object_fragment0333884_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0112_before_reader"
  err.flush

noncomputable def chunk0112LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0112SuffixChars00 : List Char := ['\r', '\n', ' ', ' ', ']']
noncomputable def chunk0112Chars00 : List Char := chunk0112LeadChars00 ++ fragment0333884Chars ++ chunk0112SuffixChars00
noncomputable def chunk0112Push00 (acc : List SourceJson) : List SourceJson := fragment0333884Value :: acc

noncomputable def chunk0112AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0112_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 545)
      (SourceJson.white (chunk0112LeadChars00 ++ (fragment0333884Chars ++ rest))) acc =
      (SourceJson.value (fuel + 544) (fragment0333884Chars ++ rest)).bind
        (chunk0112AfterValue00 (fuel + 544) acc) := by rfl

theorem array_chunk0112 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 545) (SourceJson.white (chunk0112Chars00 ++ tail)) acc =
      .ok (.arr ((chunk0112Push00 acc).reverse), tail) := by
  have hinput : chunk0112Chars00 ++ tail = chunk0112LeadChars00 ++ (fragment0333884Chars ++ (chunk0112SuffixChars00 ++ tail)) := by
    simp only [chunk0112Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 545) (SourceJson.white (chunk0112Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 545)
          (SourceJson.white (chunk0112LeadChars00 ++ (fragment0333884Chars ++ (chunk0112SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 545) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 544) (fragment0333884Chars ++ (chunk0112SuffixChars00 ++ tail))).bind
        (chunk0112AfterValue00 (fuel + 544) acc) := array_chunk0112_head fuel (chunk0112SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0333884Value, chunk0112SuffixChars00 ++ tail)).bind
        (chunk0112AfterValue00 (fuel + 544) acc) :=
      congrArg (fun result => result.bind (chunk0112AfterValue00 (fuel + 544) acc))
        (value_fragment0333884 (fuel + 311) (chunk0112SuffixChars00 ++ tail))
    _ = .ok (.arr ((chunk0112Push00 acc).reverse), tail) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0112_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0112Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0112Push00 (acc)

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 545) (SourceJson.white (blockChars ++ tail)) acc =
      .ok (.arr ((blockPush acc).reverse), tail) := by
  have hinput : blockChars ++ tail = chunk0112Chars00 ++ (tail) := by simp only [blockChars]
  calc
    SourceJson.array (fuel + 545) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 545) (SourceJson.white (chunk0112Chars00 ++ (tail))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 545) (SourceJson.white chars) acc) hinput
    _ = .ok (.arr ((blockPush acc).reverse), tail) := array_chunk0112 fuel (tail) (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 333878).take 1590 = blockChars := by rfl

theorem block_original_split : sourceRest 333878 = blockChars ++ sourceRest 335468 := by
  calc
    sourceRest 333878 = (sourceRest 333878).take 1590 ++ (sourceRest 333878).drop 1590 :=
      (List.take_append_drop 1590 (sourceRest 333878)).symm
    _ = blockChars ++ (sourceRest 333878).drop 1590 :=
      congrArg (fun part => part ++ (sourceRest 333878).drop 1590) block_original_prefix
    _ = blockChars ++ sourceRest 335468 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 333878 1590)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 545) (SourceJson.white (sourceRest 333878)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 335468) :=
  (congrArg (fun chars => SourceJson.array (fuel + 545) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 335468) acc)

#print axioms object_fragment0333884_field_000
#print axioms object_fragment0333884_field_001
#print axioms object_fragment0333884_field_002
#print axioms object_fragment0333884_field_003
#print axioms object_fragment0333884_field_004
#print axioms object_fragment0333884_field_005
#print axioms object_fragment0333884_field_006
#print axioms object_fragment0333884_field_007
#print axioms object_fragment0333884_field_008
#print axioms object_fragment0333884_field_009
#print axioms value_fragment0333884
#print axioms array_chunk0112_head
#print axioms array_chunk0112
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock014

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
