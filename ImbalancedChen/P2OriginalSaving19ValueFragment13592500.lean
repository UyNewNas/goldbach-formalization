import ImbalancedChen.P2OriginalSaving19SourceJson

/-! Self-delimiting original value fragment, raw candidate span [135925,137744). This owner is independent of geometryChars00; its arbitrary-tail theorem can be reused after a separately proved byte binding.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def fragment135925Acc00000 : List (String × SourceJson) := []

noncomputable def fragment135925Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment135925Field000Value00 : SourceJson := .number (String.ofList ['2', '1'])
noncomputable def fragment135925Acc00100 : List (String × SourceJson) := (fragment135925Field000Key00, fragment135925Field000Value00) :: fragment135925Acc00000
noncomputable def fragment135925Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '1', ',']

theorem object_fragment135925_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 340) (SourceJson.white (fragment135925Field000Chars00 ++ tail)) fragment135925Acc00000 =
      SourceJson.object (fuel + 339) (SourceJson.white tail) fragment135925Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment135925_object_field_000"
  err.flush

noncomputable def fragment135925Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment135925Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '2']), .number (String.ofList ['2'])]
noncomputable def fragment135925Acc00200 : List (String × SourceJson) := (fragment135925Field001Key00, fragment135925Field001Value00) :: fragment135925Acc00100
noncomputable def fragment135925Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment135925_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 339) (SourceJson.white (fragment135925Field001Chars00 ++ tail)) fragment135925Acc00100 =
      SourceJson.object (fuel + 338) (SourceJson.white tail) fragment135925Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment135925_object_field_001"
  err.flush

noncomputable def fragment135925Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment135925Field002Value00 : SourceJson := .str (String.ofList ['4', '4', '7', '3', '8', '9', '0', '0', '9', '3', '8', '2', '2', '0', '7', '6', '8', '0', '7', '3', '6', '6', '5', '0', '6', '3', '/', '8', '2', '8', '0', '7', '8', '4', '7', '0', '5', '3', '5', '2', '7', '8', '3', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment135925Acc00300 : List (String × SourceJson) := (fragment135925Field002Key00, fragment135925Field002Value00) :: fragment135925Acc00200
noncomputable def fragment135925Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '4', '7', '3', '8', '9', '0', '0', '9', '3', '8', '2', '2', '0', '7', '6', '8', '0', '7', '3', '6', '6', '5', '0', '6', '3', '/', '8', '2', '8', '0', '7', '8', '4', '7', '0', '5', '3', '5', '2', '7', '8', '3', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment135925_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 338) (SourceJson.white (fragment135925Field002Chars00 ++ tail)) fragment135925Acc00200 =
      SourceJson.object (fuel + 337) (SourceJson.white tail) fragment135925Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment135925_object_field_002"
  err.flush

noncomputable def fragment135925Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment135925Field003Value00 : SourceJson := .str (String.ofList ['1', '6', '4', '9', '1', '5', '9', '5', '3', '/', '1', '9', '8', '4', '3', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment135925Acc00400 : List (String × SourceJson) := (fragment135925Field003Key00, fragment135925Field003Value00) :: fragment135925Acc00300
noncomputable def fragment135925Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '6', '4', '9', '1', '5', '9', '5', '3', '/', '1', '9', '8', '4', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment135925_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 337) (SourceJson.white (fragment135925Field003Chars00 ++ tail)) fragment135925Acc00300 =
      SourceJson.object (fuel + 336) (SourceJson.white tail) fragment135925Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment135925_object_field_003"
  err.flush

noncomputable def fragment135925Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment135925Field004Value00 : SourceJson := .arr [.str (String.ofList ['3', '9', '2', '3', '4', '4', '4', '3', '/', '4', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '3', '3', '9', '/', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '1', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '7', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '1', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment135925Acc00500 : List (String × SourceJson) := (fragment135925Field004Key00, fragment135925Field004Value00) :: fragment135925Acc00400
noncomputable def fragment135925Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '2', '3', '4', '4', '4', '3', '/', '4', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '3', '3', '9', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '5', '9', '3', '4', '7', '/', '1', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '0', '3', '0', '7', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '1', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment135925_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 336) (SourceJson.white (fragment135925Field004Chars00 ++ tail)) fragment135925Acc00400 =
      SourceJson.object (fuel + 335) (SourceJson.white tail) fragment135925Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment135925_object_field_004"
  err.flush

noncomputable def fragment135925Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment135925Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '7', '2', '5', '1', '4', '8', '5', '8', '3', '1', '8', '1', '4', '1', '2', '7', '0', '1', '7', '/', '1', '9', '7', '4', '7', '6', '0', '4', '8', '8', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '2', '5', '4', '9', '5', '0', '9', '9', '8', '0', '6', '8', '3', '2', '7', '/', '7', '7', '1', '3', '9', '0', '8', '1', '5', '9', '3', '4', '3', '7', '5', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '8', '0', '9', '9', '6', '7', '9', '1', '5', '8', '3', '7', '2', '8', '9', '9', '/', '1', '9', '7', '4', '7', '6', '0', '4', '8', '8', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '4', '2', '9', '6', '7', '0', '2', '7', '3', '3', '1', '2', '9', '9', '8', '3', '/', '3', '7', '9', '7', '6', '1', '6', '3', '2', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '4', '1', '5', '0', '6', '9', '9', '2', '3', '9', '2', '6', '0', '7', '6', '1', '/', '4', '9', '3', '6', '9', '0', '1', '2', '2', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '5', '1', '2', '1', '7', '5', '2', '9', '1', '7', '9', '3', '5', '4', '3', '/', '1', '4', '1', '0', '5', '4', '3', '2', '0', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '0', '8', '4', '5', '7', '8', '1', '7', '8', '0', '3', '4', '1', '9', '7', '9', '/', '1', '4', '1', '0', '5', '4', '3', '2', '0', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '9', '6', '9', '8', '0', '0', '4', '4', '8', '5', '6', '4', '8', '4', '5', '7', '/', '4', '7', '0', '1', '8', '1', '0', '6', '8', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '9', '4', '1', '5', '1', '6', '7', '7', '9', '0', '2', '8', '7', '6', '5', '3', '/', '1', '0', '9', '7', '0', '8', '9', '1', '6', '0', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '6', '2', '4', '0', '4', '2', '3', '0', '3', '9', '2', '5', '2', '3', '/', '2', '5', '7', '1', '3', '0', '2', '7', '1', '9', '7', '8', '1', '2', '5', '0', '0', '0'])]
noncomputable def fragment135925Acc00600 : List (String × SourceJson) := (fragment135925Field005Key00, fragment135925Field005Value00) :: fragment135925Acc00500
noncomputable def fragment135925Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '5', '1', '4', '8', '5', '8', '3', '1', '8', '1', '4', '1', '2', '7', '0', '1', '7', '/', '1', '9', '7', '4', '7', '6', '0', '4', '8', '8', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '2', '5', '4', '9', '5', '0', '9', '9', '8', '0', '6', '8', '3', '2', '7', '/', '7', '7', '1', '3', '9', '0', '8', '1', '5', '9', '3', '4', '3', '7', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '8', '0', '9', '9', '6', '7', '9', '1', '5', '8', '3', '7', '2', '8', '9', '9', '/', '1', '9', '7', '4', '7', '6', '0', '4', '8', '8', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '2', '9', '6', '7', '0', '2', '7', '3', '3', '1', '2', '9', '9', '8', '3', '/', '3', '7', '9', '7', '6', '1', '6', '3', '2', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '4', '1', '5', '0', '6', '9', '9', '2', '3', '9', '2', '6', '0', '7', '6', '1', '/', '4', '9', '3', '6', '9', '0', '1', '2', '2', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '5', '1', '2', '1', '7', '5', '2', '9', '1', '7', '9', '3', '5', '4', '3', '/', '1', '4', '1', '0', '5', '4', '3', '2', '0', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '0', '8', '4', '5', '7', '8', '1', '7', '8', '0', '3', '4', '1', '9', '7', '9', '/', '1', '4', '1', '0', '5', '4', '3', '2', '0', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '6', '9', '8', '0', '0', '4', '4', '8', '5', '6', '4', '8', '4', '5', '7', '/', '4', '7', '0', '1', '8', '1', '0', '6', '8', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '9', '4', '1', '5', '1', '6', '7', '7', '9', '0', '2', '8', '7', '6', '5', '3', '/', '1', '0', '9', '7', '0', '8', '9', '1', '6', '0', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '6', '2', '4', '0', '4', '2', '3', '0', '3', '9', '2', '5', '2', '3', '/', '2', '5', '7', '1', '3', '0', '2', '7', '1', '9', '7', '8', '1', '2', '5', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment135925_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 335) (SourceJson.white (fragment135925Field005Chars00 ++ tail)) fragment135925Acc00500 =
      SourceJson.object (fuel + 334) (SourceJson.white tail) fragment135925Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment135925_object_field_005"
  err.flush

noncomputable def fragment135925Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment135925Field006Value00 : SourceJson := .str (String.ofList ['1', '1', '5', '8', '4', '8', '7', '1', '4', '7', '1', '0', '5', '6', '6', '5', '8', '9', '8', '4', '6', '7', '7', '7', '4', '9', '0', '7', '5', '2', '2', '6', '5', '1', '3', '5', '6', '9', '7', '4', '2', '1', '2', '9', '9', '3', '5', '1', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '0', '2', '3', '9', '2', '9', '7', '4', '9', '3', '6', '8', '2', '7', '8', '0', '1', '4', '2', '0', '1', '3', '5', '8', '7', '7', '2', '5', '4', '4', '6', '5', '5', '7', '3', '4', '5', '6', '0', '4', '3', '1', '0', '8', '8', '4', '2', '8', '9', '1', '7', '4', '1', '5', '8', '1', '9', '8', '0', '7', '3', '3', '3', '1', '7', '5', '3', '0', '4', '7', '5', '1', '1', '1'])
noncomputable def fragment135925Acc00700 : List (String × SourceJson) := (fragment135925Field006Key00, fragment135925Field006Value00) :: fragment135925Acc00600
noncomputable def fragment135925Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '5', '8', '4', '8', '7', '1', '4', '7', '1', '0', '5', '6', '6', '5', '8', '9', '8', '4', '6', '7', '7', '7', '4', '9', '0', '7', '5', '2', '2', '6', '5', '1', '3', '5', '6', '9', '7', '4', '2', '1', '2', '9', '9', '3', '5', '1', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '0', '2', '3', '9', '2', '9', '7', '4', '9', '3', '6', '8', '2', '7', '8', '0', '1', '4', '2', '0', '1', '3', '5', '8', '7', '7', '2', '5', '4', '4', '6', '5', '5', '7', '3', '4', '5', '6', '0', '4', '3', '1', '0', '8', '8', '4', '2', '8', '9', '1', '7', '4', '1', '5', '8', '1', '9', '8', '0', '7', '3', '3', '3', '1', '7', '5', '3', '0', '4', '7', '5', '1', '1', '1', '"', ',']

theorem object_fragment135925_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 334) (SourceJson.white (fragment135925Field006Chars00 ++ tail)) fragment135925Acc00600 =
      SourceJson.object (fuel + 333) (SourceJson.white tail) fragment135925Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment135925_object_field_006"
  err.flush

noncomputable def fragment135925Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment135925Field007Value00 : SourceJson := .str (String.ofList ['4', '5', '4', '0', '8', '0', '2', '7', '5', '4', '6', '8', '5', '8', '9', '7', '7', '9', '3', '7', '6', '6', '8', '5', '0', '2', '5', '6', '9', '5', '7', '1', '1', '7', '6', '8', '3', '1', '2', '6', '2', '0', '4', '2', '4', '2', '2', '5', '2', '1', '0', '3', '8', '9', '7', '8', '0', '9', '1', '6', '8', '1', '4', '4', '4', '5', '0', '7', '1', '2', '5', '0', '5', '7', '6', '3', '9', '7', '0', '3', '7', '4', '5', '1', '1', '3', '1', '6', '3', '1', '1', '2', '1', '3', '4', '3', '1', '7', '6', '2', '1', '8', '1', '6', '8', '5', '6', '4', '6', '8', '7', '3', '3', '7', '3', '1', '8', '7', '2', '7', '8', '0', '7', '5', '8', '0', '2', '4', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '4', '4', '4', '8', '2', '9', '1', '1', '6', '8', '1', '1', '4', '9', '6', '8', '4', '0', '9', '6', '3', '7', '9', '7', '5', '8', '3', '9', '6', '0', '8', '1', '5', '2', '2', '3', '3', '8', '7', '6', '7', '4', '4', '9', '8', '8', '4', '2', '0', '9', '9', '2', '1', '1', '4', '5', '9', '2', '6', '3', '7', '9', '2', '3', '5', '5', '7', '7', '0', '3', '5', '5', '1', '1', '1', '7', '3', '1', '3', '7', '9', '3', '6', '4', '6', '6', '6', '2', '9', '4', '7', '9', '8', '9', '2', '4', '0', '2', '5', '7', '0', '4', '5', '6', '5', '3', '9', '0', '4', '1', '4', '2', '7', '9', '0', '6', '2', '6', '2', '9', '5', '8', '7', '5', '1', '4', '0', '6', '6', '0', '4', '2', '1', '3', '7', '0', '4', '1', '5', '9', '4', '1', '2', '2', '2', '4', '8', '1', '8', '4', '2', '8', '5', '7', '2', '4', '6', '3', '4', '9', '3', '8', '4', '0', '2', '1', '1', '6', '5', '5', '9'])
noncomputable def fragment135925Acc00800 : List (String × SourceJson) := (fragment135925Field007Key00, fragment135925Field007Value00) :: fragment135925Acc00700
noncomputable def fragment135925Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '5', '4', '0', '8', '0', '2', '7', '5', '4', '6', '8', '5', '8', '9', '7', '7', '9', '3', '7', '6', '6', '8', '5', '0', '2', '5', '6', '9', '5', '7', '1', '1', '7', '6', '8', '3', '1', '2', '6', '2', '0', '4', '2', '4', '2', '2', '5', '2', '1', '0', '3', '8', '9', '7', '8', '0', '9', '1', '6', '8', '1', '4', '4', '4', '5', '0', '7', '1', '2', '5', '0', '5', '7', '6', '3', '9', '7', '0', '3', '7', '4', '5', '1', '1', '3', '1', '6', '3', '1', '1', '2', '1', '3', '4', '3', '1', '7', '6', '2', '1', '8', '1', '6', '8', '5', '6', '4', '6', '8', '7', '3', '3', '7', '3', '1', '8', '7', '2', '7', '8', '0', '7', '5', '8', '0', '2', '4', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '4', '4', '4', '8', '2', '9', '1', '1', '6', '8', '1', '1', '4', '9', '6', '8', '4', '0', '9', '6', '3', '7', '9', '7', '5', '8', '3', '9', '6', '0', '8', '1', '5', '2', '2', '3', '3', '8', '7', '6', '7', '4', '4', '9', '8', '8', '4', '2', '0', '9', '9', '2', '1', '1', '4', '5', '9', '2', '6', '3', '7', '9', '2', '3', '5', '5', '7', '7', '0', '3', '5', '5', '1', '1', '1', '7', '3', '1', '3', '7', '9', '3', '6', '4', '6', '6', '6', '2', '9', '4', '7', '9', '8', '9', '2', '4', '0', '2', '5', '7', '0', '4', '5', '6', '5', '3', '9', '0', '4', '1', '4', '2', '7', '9', '0', '6', '2', '6', '2', '9', '5', '8', '7', '5', '1', '4', '0', '6', '6', '0', '4', '2', '1', '3', '7', '0', '4', '1', '5', '9', '4', '1', '2', '2', '2', '4', '8', '1', '8', '4', '2', '8', '5', '7', '2', '4', '6', '3', '4', '9', '3', '8', '4', '0', '2', '1', '1', '6', '5', '5', '9', '"', ',']

theorem object_fragment135925_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 333) (SourceJson.white (fragment135925Field007Chars00 ++ tail)) fragment135925Acc00700 =
      SourceJson.object (fuel + 332) (SourceJson.white tail) fragment135925Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment135925_object_field_007"
  err.flush

noncomputable def fragment135925Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment135925Field008Value00 : SourceJson := .str (String.ofList ['1', '0', '1', '7', '1', '2', '6', '8', '0', '0', '7', '4', '8'])
noncomputable def fragment135925Acc00900 : List (String × SourceJson) := (fragment135925Field008Key00, fragment135925Field008Value00) :: fragment135925Acc00800
noncomputable def fragment135925Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '1', '7', '1', '2', '6', '8', '0', '0', '7', '4', '8', '"', ',']

theorem object_fragment135925_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 332) (SourceJson.white (fragment135925Field008Chars00 ++ tail)) fragment135925Acc00800 =
      SourceJson.object (fuel + 331) (SourceJson.white tail) fragment135925Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment135925_object_field_008"
  err.flush

noncomputable def fragment135925Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment135925Field009Value00 : SourceJson := .str (String.ofList ['2', '4', '9', '0', '5', '7', '6', '0', '7', '8', '7', '0', '7'])
noncomputable def fragment135925Acc01000 : List (String × SourceJson) := (fragment135925Field009Key00, fragment135925Field009Value00) :: fragment135925Acc00900
noncomputable def fragment135925Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '9', '0', '5', '7', '6', '0', '7', '8', '7', '0', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment135925_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 331) (SourceJson.white (fragment135925Field009Chars00 ++ tail)) fragment135925Acc00900 =
      .ok (.obj (fragment135925Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment135925_object_field_009"
  err.flush

noncomputable def fragment135925Chars00 : List Char := '{' :: (fragment135925Field000Chars00 ++ fragment135925Field001Chars00 ++ fragment135925Field002Chars00 ++ fragment135925Field003Chars00 ++ fragment135925Field004Chars00 ++ fragment135925Field005Chars00 ++ fragment135925Field006Chars00 ++ fragment135925Field007Chars00 ++ fragment135925Field008Chars00 ++ fragment135925Field009Chars00)
noncomputable def fragment135925Value00 : SourceJson := .obj (fragment135925Acc01000.reverse)

theorem value_fragment135925 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 341) (fragment135925Chars00 ++ tail) =
      .ok (fragment135925Value00, tail) := by
  have hinput : fragment135925Chars00 ++ tail = '{' :: (fragment135925Field000Chars00 ++ (fragment135925Field001Chars00 ++ (fragment135925Field002Chars00 ++ (fragment135925Field003Chars00 ++ (fragment135925Field004Chars00 ++ (fragment135925Field005Chars00 ++ (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment135925Chars00, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 341) (fragment135925Chars00 ++ tail) =
        SourceJson.value (fuel + 341) ('{' :: (fragment135925Field000Chars00 ++ (fragment135925Field001Chars00 ++ (fragment135925Field002Chars00 ++ (fragment135925Field003Chars00 ++ (fragment135925Field004Chars00 ++ (fragment135925Field005Chars00 ++ (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 341)) hinput
    _ = SourceJson.object (fuel + 340) (SourceJson.white (fragment135925Field000Chars00 ++ (fragment135925Field001Chars00 ++ (fragment135925Field002Chars00 ++ (fragment135925Field003Chars00 ++ (fragment135925Field004Chars00 ++ (fragment135925Field005Chars00 ++ (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail)))))))))))) fragment135925Acc00000 := by rfl
    _ = SourceJson.object (fuel + 339) (SourceJson.white (fragment135925Field001Chars00 ++ (fragment135925Field002Chars00 ++ (fragment135925Field003Chars00 ++ (fragment135925Field004Chars00 ++ (fragment135925Field005Chars00 ++ (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail))))))))))) fragment135925Acc00100 := object_fragment135925_field_000 fuel (fragment135925Field001Chars00 ++ (fragment135925Field002Chars00 ++ (fragment135925Field003Chars00 ++ (fragment135925Field004Chars00 ++ (fragment135925Field005Chars00 ++ (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 338) (SourceJson.white (fragment135925Field002Chars00 ++ (fragment135925Field003Chars00 ++ (fragment135925Field004Chars00 ++ (fragment135925Field005Chars00 ++ (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail)))))))))) fragment135925Acc00200 := object_fragment135925_field_001 fuel (fragment135925Field002Chars00 ++ (fragment135925Field003Chars00 ++ (fragment135925Field004Chars00 ++ (fragment135925Field005Chars00 ++ (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 337) (SourceJson.white (fragment135925Field003Chars00 ++ (fragment135925Field004Chars00 ++ (fragment135925Field005Chars00 ++ (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail))))))))) fragment135925Acc00300 := object_fragment135925_field_002 fuel (fragment135925Field003Chars00 ++ (fragment135925Field004Chars00 ++ (fragment135925Field005Chars00 ++ (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 336) (SourceJson.white (fragment135925Field004Chars00 ++ (fragment135925Field005Chars00 ++ (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail)))))))) fragment135925Acc00400 := object_fragment135925_field_003 fuel (fragment135925Field004Chars00 ++ (fragment135925Field005Chars00 ++ (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 335) (SourceJson.white (fragment135925Field005Chars00 ++ (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail))))))) fragment135925Acc00500 := object_fragment135925_field_004 fuel (fragment135925Field005Chars00 ++ (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 334) (SourceJson.white (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail)))))) fragment135925Acc00600 := object_fragment135925_field_005 fuel (fragment135925Field006Chars00 ++ (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 333) (SourceJson.white (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail))))) fragment135925Acc00700 := object_fragment135925_field_006 fuel (fragment135925Field007Chars00 ++ (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 332) (SourceJson.white (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail)))) fragment135925Acc00800 := object_fragment135925_field_007 fuel (fragment135925Field008Chars00 ++ (fragment135925Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 331) (SourceJson.white (fragment135925Field009Chars00 ++ (tail))) fragment135925Acc00900 := object_fragment135925_field_008 fuel (fragment135925Field009Chars00 ++ (tail))
    _ = .ok (fragment135925Value00, tail) := object_fragment135925_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment135925_value_complete"
  err.flush

#print axioms object_fragment135925_field_000
#print axioms object_fragment135925_field_001
#print axioms object_fragment135925_field_002
#print axioms object_fragment135925_field_003
#print axioms object_fragment135925_field_004
#print axioms object_fragment135925_field_005
#print axioms object_fragment135925_field_006
#print axioms object_fragment135925_field_007
#print axioms object_fragment135925_field_008
#print axioms object_fragment135925_field_009
#print axioms value_fragment135925

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
