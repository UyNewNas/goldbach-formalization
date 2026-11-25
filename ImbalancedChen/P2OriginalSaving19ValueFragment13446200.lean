import ImbalancedChen.P2OriginalSaving19SourceJson

/-! Self-delimiting original value fragment, raw candidate span [134462,135918). This owner is independent of geometryChars00; its arbitrary-tail theorem can be reused after a separately proved byte binding.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def fragment134462Acc00000 : List (String × SourceJson) := []

noncomputable def fragment134462Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment134462Field000Value00 : SourceJson := .number (String.ofList ['2', '0'])
noncomputable def fragment134462Acc00100 : List (String × SourceJson) := (fragment134462Field000Key00, fragment134462Field000Value00) :: fragment134462Acc00000
noncomputable def fragment134462Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '0', ',']

theorem object_fragment134462_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 165) (SourceJson.white (fragment134462Field000Chars00 ++ tail)) fragment134462Acc00000 =
      SourceJson.object (fuel + 164) (SourceJson.white tail) fragment134462Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment134462_object_field_000"
  err.flush

noncomputable def fragment134462Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment134462Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '7']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment134462Acc00200 : List (String × SourceJson) := (fragment134462Field001Key00, fragment134462Field001Value00) :: fragment134462Acc00100
noncomputable def fragment134462Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment134462_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 164) (SourceJson.white (fragment134462Field001Chars00 ++ tail)) fragment134462Acc00100 =
      SourceJson.object (fuel + 163) (SourceJson.white tail) fragment134462Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment134462_object_field_001"
  err.flush

noncomputable def fragment134462Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment134462Field002Value00 : SourceJson := .str (String.ofList ['1', '2', '5', '1', '2', '8', '7', '0', '5', '0', '0', '6', '3', '9', '3', '9', '5', '0', '9', '5', '5', '1', '6', '5', '3', '8', '7', '3', '3', '/', '8', '6', '3', '9', '5', '1', '4', '5', '4', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment134462Acc00300 : List (String × SourceJson) := (fragment134462Field002Key00, fragment134462Field002Value00) :: fragment134462Acc00200
noncomputable def fragment134462Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '2', '5', '1', '2', '8', '7', '0', '5', '0', '0', '6', '3', '9', '3', '9', '5', '0', '9', '5', '5', '1', '6', '5', '3', '8', '7', '3', '3', '/', '8', '6', '3', '9', '5', '1', '4', '5', '4', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment134462_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 163) (SourceJson.white (fragment134462Field002Chars00 ++ tail)) fragment134462Acc00200 =
      SourceJson.object (fuel + 162) (SourceJson.white tail) fragment134462Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment134462_object_field_002"
  err.flush

noncomputable def fragment134462Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment134462Field003Value00 : SourceJson := .str (String.ofList ['1', '6', '4', '0', '2', '6', '9', '/', '3', '7', '4', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment134462Acc00400 : List (String × SourceJson) := (fragment134462Field003Key00, fragment134462Field003Value00) :: fragment134462Acc00300
noncomputable def fragment134462Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '6', '4', '0', '2', '6', '9', '/', '3', '7', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment134462_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 162) (SourceJson.white (fragment134462Field003Chars00 ++ tail)) fragment134462Acc00300 =
      SourceJson.object (fuel + 161) (SourceJson.white tail) fragment134462Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment134462_object_field_003"
  err.flush

noncomputable def fragment134462Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment134462Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '5', '5', '5', '7', '/', '2', '8', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '7', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment134462Acc00500 : List (String × SourceJson) := (fragment134462Field004Key00, fragment134462Field004Value00) :: fragment134462Acc00400
noncomputable def fragment134462Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '1', '5', '5', '5', '7', '/', '2', '8', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '0', '3', '0', '7', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment134462_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 161) (SourceJson.white (fragment134462Field004Chars00 ++ tail)) fragment134462Acc00400 =
      SourceJson.object (fuel + 160) (SourceJson.white tail) fragment134462Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment134462_object_field_004"
  err.flush

noncomputable def fragment134462Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment134462Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '8', '4', '2', '8', '7', '6', '3', '7', '4', '7', '/', '6', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '4', '7', '2', '7', '2', '4', '2', '4', '1', '/', '3', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '2', '7', '1', '1', '8', '1', '7', '9', '/', '1', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '5', '7', '8', '1', '7', '0', '6', '7', '/', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '7', '3', '9', '1', '3', '1', '1', '/', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '5', '5', '6', '5', '7', '/', '8', '3', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '1', '1', '9', '1', '5', '3', '/', '9', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '9', '2', '0', '5', '3', '1', '/', '2', '9', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '9', '5', '0', '2', '1', '6', '1', '/', '1', '0', '2', '3', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '5', '1', '6', '8', '8', '0', '2', '7', '/', '3', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment134462Acc00600 : List (String × SourceJson) := (fragment134462Field005Key00, fragment134462Field005Value00) :: fragment134462Acc00500
noncomputable def fragment134462Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '4', '2', '8', '7', '6', '3', '7', '4', '7', '/', '6', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '4', '7', '2', '7', '2', '4', '2', '4', '1', '/', '3', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '2', '7', '1', '1', '8', '1', '7', '9', '/', '1', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '5', '7', '8', '1', '7', '0', '6', '7', '/', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '0', '7', '3', '9', '1', '3', '1', '1', '/', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '5', '5', '6', '5', '7', '/', '8', '3', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '1', '1', '9', '1', '5', '3', '/', '9', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '9', '2', '0', '5', '3', '1', '/', '2', '9', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '9', '5', '0', '2', '1', '6', '1', '/', '1', '0', '2', '3', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '5', '1', '6', '8', '8', '0', '2', '7', '/', '3', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment134462_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 160) (SourceJson.white (fragment134462Field005Chars00 ++ tail)) fragment134462Acc00500 =
      SourceJson.object (fuel + 159) (SourceJson.white tail) fragment134462Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment134462_object_field_005"
  err.flush

noncomputable def fragment134462Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment134462Field006Value00 : SourceJson := .str (String.ofList ['2', '2', '0', '3', '7', '9', '8', '5', '7', '0', '1', '8', '7', '9', '2', '4', '2', '9', '9', '8', '7', '5', '3', '0', '9', '0', '6', '9', '5', '6', '9', '2', '6', '7', '3', '0', '8', '7', '4', '3', '8', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '8', '1', '3', '1', '5', '0', '4', '5', '7', '4', '1', '5', '1', '7', '4', '1', '3', '3', '8', '3', '2', '9', '4', '3', '8', '0', '9', '6', '2', '7', '5', '5', '5', '8', '6', '6', '1', '3', '6', '8', '9', '2', '7', '6', '0', '5', '8', '2', '7', '4', '3', '7', '3', '9', '9', '6', '3', '8', '2', '1', '6', '5', '0', '5', '6', '1', '7'])
noncomputable def fragment134462Acc00700 : List (String × SourceJson) := (fragment134462Field006Key00, fragment134462Field006Value00) :: fragment134462Acc00600
noncomputable def fragment134462Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '2', '0', '3', '7', '9', '8', '5', '7', '0', '1', '8', '7', '9', '2', '4', '2', '9', '9', '8', '7', '5', '3', '0', '9', '0', '6', '9', '5', '6', '9', '2', '6', '7', '3', '0', '8', '7', '4', '3', '8', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '8', '1', '3', '1', '5', '0', '4', '5', '7', '4', '1', '5', '1', '7', '4', '1', '3', '3', '8', '3', '2', '9', '4', '3', '8', '0', '9', '6', '2', '7', '5', '5', '5', '8', '6', '6', '1', '3', '6', '8', '9', '2', '7', '6', '0', '5', '8', '2', '7', '4', '3', '7', '3', '9', '9', '6', '3', '8', '2', '1', '6', '5', '0', '5', '6', '1', '7', '"', ',']

theorem object_fragment134462_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 159) (SourceJson.white (fragment134462Field006Chars00 ++ tail)) fragment134462Acc00600 =
      SourceJson.object (fuel + 158) (SourceJson.white tail) fragment134462Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment134462_object_field_006"
  err.flush

noncomputable def fragment134462Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment134462Field007Value00 : SourceJson := .str (String.ofList ['3', '8', '9', '5', '1', '4', '9', '4', '1', '2', '4', '4', '9', '8', '3', '4', '4', '3', '1', '9', '2', '0', '5', '4', '5', '5', '8', '6', '0', '6', '1', '8', '6', '6', '1', '1', '9', '9', '9', '2', '4', '4', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '3', '0', '6', '5', '7', '4', '9', '3', '7', '0', '2', '1', '0', '7', '7', '4', '6', '6', '8', '8', '2', '8', '2', '1', '0', '5', '7', '0', '6', '9', '1', '8', '5', '8', '7', '3', '5', '5', '8', '8', '7', '4', '2', '0', '2', '1', '5', '2', '6', '8', '7', '4', '2', '7', '0', '5', '8', '4', '6', '1', '4', '7', '0', '1', '0', '6', '2', '6', '9', '8', '3', '5', '6', '3', '0', '9', '6', '3', '3', '3', '7', '9', '5', '1'])
noncomputable def fragment134462Acc00800 : List (String × SourceJson) := (fragment134462Field007Key00, fragment134462Field007Value00) :: fragment134462Acc00700
noncomputable def fragment134462Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '8', '9', '5', '1', '4', '9', '4', '1', '2', '4', '4', '9', '8', '3', '4', '4', '3', '1', '9', '2', '0', '5', '4', '5', '5', '8', '6', '0', '6', '1', '8', '6', '6', '1', '1', '9', '9', '9', '2', '4', '4', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '3', '0', '6', '5', '7', '4', '9', '3', '7', '0', '2', '1', '0', '7', '7', '4', '6', '6', '8', '8', '2', '8', '2', '1', '0', '5', '7', '0', '6', '9', '1', '8', '5', '8', '7', '3', '5', '5', '8', '8', '7', '4', '2', '0', '2', '1', '5', '2', '6', '8', '7', '4', '2', '7', '0', '5', '8', '4', '6', '1', '4', '7', '0', '1', '0', '6', '2', '6', '9', '8', '3', '5', '6', '3', '0', '9', '6', '3', '3', '3', '7', '9', '5', '1', '"', ',']

theorem object_fragment134462_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 158) (SourceJson.white (fragment134462Field007Chars00 ++ tail)) fragment134462Acc00700 =
      SourceJson.object (fuel + 157) (SourceJson.white tail) fragment134462Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment134462_object_field_007"
  err.flush

noncomputable def fragment134462Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment134462Field008Value00 : SourceJson := .str (String.ofList ['1', '0', '3', '8', '4', '9', '0', '1', '4', '9', '1', '8', '2'])
noncomputable def fragment134462Acc00900 : List (String × SourceJson) := (fragment134462Field008Key00, fragment134462Field008Value00) :: fragment134462Acc00800
noncomputable def fragment134462Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '3', '8', '4', '9', '0', '1', '4', '9', '1', '8', '2', '"', ',']

theorem object_fragment134462_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 157) (SourceJson.white (fragment134462Field008Chars00 ++ tail)) fragment134462Acc00800 =
      SourceJson.object (fuel + 156) (SourceJson.white tail) fragment134462Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment134462_object_field_008"
  err.flush

noncomputable def fragment134462Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment134462Field009Value00 : SourceJson := .str (String.ofList ['3', '3', '1', '5', '9', '9', '4', '6', '8', '9', '2', '9', '5'])
noncomputable def fragment134462Acc01000 : List (String × SourceJson) := (fragment134462Field009Key00, fragment134462Field009Value00) :: fragment134462Acc00900
noncomputable def fragment134462Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '1', '5', '9', '9', '4', '6', '8', '9', '2', '9', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment134462_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 156) (SourceJson.white (fragment134462Field009Chars00 ++ tail)) fragment134462Acc00900 =
      .ok (.obj (fragment134462Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment134462_object_field_009"
  err.flush

noncomputable def fragment134462Chars00 : List Char := '{' :: (fragment134462Field000Chars00 ++ fragment134462Field001Chars00 ++ fragment134462Field002Chars00 ++ fragment134462Field003Chars00 ++ fragment134462Field004Chars00 ++ fragment134462Field005Chars00 ++ fragment134462Field006Chars00 ++ fragment134462Field007Chars00 ++ fragment134462Field008Chars00 ++ fragment134462Field009Chars00)
noncomputable def fragment134462Value00 : SourceJson := .obj (fragment134462Acc01000.reverse)

theorem value_fragment134462 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 166) (fragment134462Chars00 ++ tail) =
      .ok (fragment134462Value00, tail) := by
  have hinput : fragment134462Chars00 ++ tail = '{' :: (fragment134462Field000Chars00 ++ (fragment134462Field001Chars00 ++ (fragment134462Field002Chars00 ++ (fragment134462Field003Chars00 ++ (fragment134462Field004Chars00 ++ (fragment134462Field005Chars00 ++ (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment134462Chars00, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 166) (fragment134462Chars00 ++ tail) =
        SourceJson.value (fuel + 166) ('{' :: (fragment134462Field000Chars00 ++ (fragment134462Field001Chars00 ++ (fragment134462Field002Chars00 ++ (fragment134462Field003Chars00 ++ (fragment134462Field004Chars00 ++ (fragment134462Field005Chars00 ++ (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 166)) hinput
    _ = SourceJson.object (fuel + 165) (SourceJson.white (fragment134462Field000Chars00 ++ (fragment134462Field001Chars00 ++ (fragment134462Field002Chars00 ++ (fragment134462Field003Chars00 ++ (fragment134462Field004Chars00 ++ (fragment134462Field005Chars00 ++ (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail)))))))))))) fragment134462Acc00000 := by rfl
    _ = SourceJson.object (fuel + 164) (SourceJson.white (fragment134462Field001Chars00 ++ (fragment134462Field002Chars00 ++ (fragment134462Field003Chars00 ++ (fragment134462Field004Chars00 ++ (fragment134462Field005Chars00 ++ (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail))))))))))) fragment134462Acc00100 := object_fragment134462_field_000 fuel (fragment134462Field001Chars00 ++ (fragment134462Field002Chars00 ++ (fragment134462Field003Chars00 ++ (fragment134462Field004Chars00 ++ (fragment134462Field005Chars00 ++ (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 163) (SourceJson.white (fragment134462Field002Chars00 ++ (fragment134462Field003Chars00 ++ (fragment134462Field004Chars00 ++ (fragment134462Field005Chars00 ++ (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail)))))))))) fragment134462Acc00200 := object_fragment134462_field_001 fuel (fragment134462Field002Chars00 ++ (fragment134462Field003Chars00 ++ (fragment134462Field004Chars00 ++ (fragment134462Field005Chars00 ++ (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 162) (SourceJson.white (fragment134462Field003Chars00 ++ (fragment134462Field004Chars00 ++ (fragment134462Field005Chars00 ++ (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail))))))))) fragment134462Acc00300 := object_fragment134462_field_002 fuel (fragment134462Field003Chars00 ++ (fragment134462Field004Chars00 ++ (fragment134462Field005Chars00 ++ (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 161) (SourceJson.white (fragment134462Field004Chars00 ++ (fragment134462Field005Chars00 ++ (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail)))))))) fragment134462Acc00400 := object_fragment134462_field_003 fuel (fragment134462Field004Chars00 ++ (fragment134462Field005Chars00 ++ (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 160) (SourceJson.white (fragment134462Field005Chars00 ++ (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail))))))) fragment134462Acc00500 := object_fragment134462_field_004 fuel (fragment134462Field005Chars00 ++ (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 159) (SourceJson.white (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail)))))) fragment134462Acc00600 := object_fragment134462_field_005 fuel (fragment134462Field006Chars00 ++ (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 158) (SourceJson.white (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail))))) fragment134462Acc00700 := object_fragment134462_field_006 fuel (fragment134462Field007Chars00 ++ (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 157) (SourceJson.white (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail)))) fragment134462Acc00800 := object_fragment134462_field_007 fuel (fragment134462Field008Chars00 ++ (fragment134462Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 156) (SourceJson.white (fragment134462Field009Chars00 ++ (tail))) fragment134462Acc00900 := object_fragment134462_field_008 fuel (fragment134462Field009Chars00 ++ (tail))
    _ = .ok (fragment134462Value00, tail) := object_fragment134462_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment134462_value_complete"
  err.flush

#print axioms object_fragment134462_field_000
#print axioms object_fragment134462_field_001
#print axioms object_fragment134462_field_002
#print axioms object_fragment134462_field_003
#print axioms object_fragment134462_field_004
#print axioms object_fragment134462_field_005
#print axioms object_fragment134462_field_006
#print axioms object_fragment134462_field_007
#print axioms object_fragment134462_field_008
#print axioms object_fragment134462_field_009
#print axioms value_fragment134462

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
