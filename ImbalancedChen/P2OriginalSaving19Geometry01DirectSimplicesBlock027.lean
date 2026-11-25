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

namespace SimplicesBlock027

noncomputable def fragment0317071Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0317071Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0317071Field000Value00 : SourceJson := .number (String.ofList ['5', '3'])
noncomputable def fragment0317071Acc00100 : List (String × SourceJson) := (fragment0317071Field000Key00, fragment0317071Field000Value00) :: fragment0317071Acc00000
noncomputable def fragment0317071Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '3', ',']

theorem object_fragment0317071_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0317071Field000Chars00 ++ tail)) fragment0317071Acc00000 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0317071Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317071_object_field_000"
  err.flush

noncomputable def fragment0317071Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0317071Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '5']), .number (String.ofList ['7']), .number (String.ofList ['0'])]
noncomputable def fragment0317071Acc00200 : List (String × SourceJson) := (fragment0317071Field001Key00, fragment0317071Field001Value00) :: fragment0317071Acc00100
noncomputable def fragment0317071Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0317071_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0317071Field001Chars00 ++ tail)) fragment0317071Acc00100 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0317071Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317071_object_field_001"
  err.flush

noncomputable def fragment0317071Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0317071Field002Value00 : SourceJson := .str (String.ofList ['7', '3', '0', '0', '2', '5', '5', '6', '5', '3', '2', '8', '6', '3', '5', '2', '8', '7', '1', '5', '6', '3', '3', '5', '7', '8', '4', '7', '8', '1', '4', '4', '5', '7', '0', '3', '6', '8', '6', '4', '4', '0', '5', '5', '9', '/', '2', '8', '2', '1', '5', '2', '6', '1', '4', '9', '0', '0', '0', '9', '0', '7', '9', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0317071Acc00300 : List (String × SourceJson) := (fragment0317071Field002Key00, fragment0317071Field002Value00) :: fragment0317071Acc00200
noncomputable def fragment0317071Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '3', '0', '0', '2', '5', '5', '6', '5', '3', '2', '8', '6', '3', '5', '2', '8', '7', '1', '5', '6', '3', '3', '5', '7', '8', '4', '7', '8', '1', '4', '4', '5', '7', '0', '3', '6', '8', '6', '4', '4', '0', '5', '5', '9', '/', '2', '8', '2', '1', '5', '2', '6', '1', '4', '9', '0', '0', '0', '9', '0', '7', '9', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0317071_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0317071Field002Chars00 ++ tail)) fragment0317071Acc00200 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0317071Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317071_object_field_002"
  err.flush

noncomputable def fragment0317071Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0317071Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0317071Acc00400 : List (String × SourceJson) := (fragment0317071Field003Key00, fragment0317071Field003Value00) :: fragment0317071Acc00300
noncomputable def fragment0317071Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0317071_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0317071Field003Chars00 ++ tail)) fragment0317071Acc00300 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0317071Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317071_object_field_003"
  err.flush

noncomputable def fragment0317071Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0317071Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0317071Acc00500 : List (String × SourceJson) := (fragment0317071Field004Key00, fragment0317071Field004Value00) :: fragment0317071Acc00400
noncomputable def fragment0317071Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0317071_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0317071Field004Chars00 ++ tail)) fragment0317071Acc00400 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0317071Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317071_object_field_004"
  err.flush

noncomputable def fragment0317071Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0317071Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '8', '6', '8', '6', '2', '5', '1', '7', '3', '2', '0', '3', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '8', '3', '2', '0', '0', '3', '0', '0', '0', '6', '3', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '1', '4', '5', '2', '8', '1', '9', '6', '0', '1', '7', '1', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '7', '0', '5', '3', '7', '2', '1', '1', '8', '0', '1', '/', '1', '6', '6', '3', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '6', '4', '8', '0', '8', '1', '1', '5', '8', '4', '3', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '7', '1', '9', '1', '5', '8', '2', '0', '3', '8', '8', '9', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '8', '4', '2', '6', '6', '7', '0', '6', '8', '1', '/', '1', '0', '5', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '1', '3', '4', '9', '4', '9', '9', '6', '7', '1', '9', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '6', '0', '1', '6', '2', '5', '0', '2', '3', '2', '9', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '8', '6', '6', '8', '5', '4', '9', '8', '9', '1', '9', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0317071Acc00600 : List (String × SourceJson) := (fragment0317071Field005Key00, fragment0317071Field005Value00) :: fragment0317071Acc00500
noncomputable def fragment0317071Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '6', '8', '6', '2', '5', '1', '7', '3', '2', '0', '3', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '8', '3', '2', '0', '0', '3', '0', '0', '0', '6', '3', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '1', '4', '5', '2', '8', '1', '9', '6', '0', '1', '7', '1', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '7', '0', '5', '3', '7', '2', '1', '1', '8', '0', '1', '/', '1', '6', '6', '3', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '6', '4', '8', '0', '8', '1', '1', '5', '8', '4', '3', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '1', '9', '1', '5', '8', '2', '0', '3', '8', '8', '9', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '8', '4', '2', '6', '6', '7', '0', '6', '8', '1', '/', '1', '0', '5', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '1', '3', '4', '9', '4', '9', '9', '6', '7', '1', '9', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '6', '0', '1', '6', '2', '5', '0', '2', '3', '2', '9', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '8', '6', '6', '8', '5', '4', '9', '8', '9', '1', '9', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0317071_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0317071Field005Chars00 ++ tail)) fragment0317071Acc00500 =
      SourceJson.object (fuel + 240) (SourceJson.white tail) fragment0317071Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317071_object_field_005"
  err.flush

noncomputable def fragment0317071Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0317071Field006Value00 : SourceJson := .str (String.ofList ['4', '5', '9', '7', '7', '9', '4', '1', '5', '1', '6', '3', '2', '5', '6', '2', '8', '2', '9', '9', '0', '9', '3', '0', '8', '9', '2', '5', '7', '3', '9', '8', '7', '9', '2', '2', '6', '2', '6', '9', '0', '5', '2', '2', '8', '9', '8', '9', '4', '7', '/', '2', '2', '0', '0', '0', '2', '1', '5', '6', '3', '0', '5', '7', '1', '5', '2', '9', '6', '2', '3', '8', '1', '0', '8', '1', '5', '3', '7', '2', '6', '6', '6', '3', '9', '7', '3', '2', '2', '9', '5', '2', '4', '2', '3', '8', '2', '8', '6', '7', '2', '7', '3', '3', '9', '5', '5', '6', '1', '5', '9', '8', '9', '9', '6'])
noncomputable def fragment0317071Acc00700 : List (String × SourceJson) := (fragment0317071Field006Key00, fragment0317071Field006Value00) :: fragment0317071Acc00600
noncomputable def fragment0317071Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '5', '9', '7', '7', '9', '4', '1', '5', '1', '6', '3', '2', '5', '6', '2', '8', '2', '9', '9', '0', '9', '3', '0', '8', '9', '2', '5', '7', '3', '9', '8', '7', '9', '2', '2', '6', '2', '6', '9', '0', '5', '2', '2', '8', '9', '8', '9', '4', '7', '/', '2', '2', '0', '0', '0', '2', '1', '5', '6', '3', '0', '5', '7', '1', '5', '2', '9', '6', '2', '3', '8', '1', '0', '8', '1', '5', '3', '7', '2', '6', '6', '6', '3', '9', '7', '3', '2', '2', '9', '5', '2', '4', '2', '3', '8', '2', '8', '6', '7', '2', '7', '3', '3', '9', '5', '5', '6', '1', '5', '9', '8', '9', '9', '6', '"', ',']

theorem object_fragment0317071_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 240) (SourceJson.white (fragment0317071Field006Chars00 ++ tail)) fragment0317071Acc00600 =
      SourceJson.object (fuel + 239) (SourceJson.white tail) fragment0317071Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317071_object_field_006"
  err.flush

noncomputable def fragment0317071Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0317071Field007Value00 : SourceJson := .str (String.ofList ['6', '6', '7', '7', '6', '0', '6', '2', '5', '2', '8', '8', '3', '5', '7', '0', '0', '9', '0', '3', '8', '3', '4', '5', '8', '0', '0', '7', '4', '8', '7', '1', '6', '2', '7', '9', '5', '7', '4', '0', '4', '7', '6', '1', '6', '6', '2', '5', '9', '0', '7', '5', '8', '1', '9', '5', '9', '5', '5', '4', '6', '3', '4', '3', '9', '5', '3', '5', '8', '7', '5', '3', '5', '6', '3', '9', '0', '8', '1', '0', '1', '0', '1', '6', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '5', '7', '6', '0', '7', '8', '9', '0', '9', '7', '6', '6', '0', '3', '4', '6', '5', '0', '6', '1', '1', '3', '7', '3', '4', '5', '8', '0', '7', '1', '9', '5', '1', '5', '5', '3', '7', '7', '2', '1', '1', '3', '6', '5', '7', '8', '9', '0', '0', '5', '3', '4', '2', '7', '1', '9', '8', '5', '2', '6', '7', '9', '0', '0', '3', '3', '8', '5', '1', '0', '1', '0', '8', '6', '3', '0', '9', '7', '4', '0', '0', '3', '2', '5', '7', '4', '5', '3', '7', '1', '1', '5', '2', '0', '0', '2', '7', '7', '8', '6', '6', '3', '0', '7', '1', '7', '5', '0', '4', '9', '1', '9', '2', '3', '7', '5', '8', '2', '4', '2', '0', '7'])
noncomputable def fragment0317071Acc00800 : List (String × SourceJson) := (fragment0317071Field007Key00, fragment0317071Field007Value00) :: fragment0317071Acc00700
noncomputable def fragment0317071Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '6', '7', '7', '6', '0', '6', '2', '5', '2', '8', '8', '3', '5', '7', '0', '0', '9', '0', '3', '8', '3', '4', '5', '8', '0', '0', '7', '4', '8', '7', '1', '6', '2', '7', '9', '5', '7', '4', '0', '4', '7', '6', '1', '6', '6', '2', '5', '9', '0', '7', '5', '8', '1', '9', '5', '9', '5', '5', '4', '6', '3', '4', '3', '9', '5', '3', '5', '8', '7', '5', '3', '5', '6', '3', '9', '0', '8', '1', '0', '1', '0', '1', '6', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '5', '7', '6', '0', '7', '8', '9', '0', '9', '7', '6', '6', '0', '3', '4', '6', '5', '0', '6', '1', '1', '3', '7', '3', '4', '5', '8', '0', '7', '1', '9', '5', '1', '5', '5', '3', '7', '7', '2', '1', '1', '3', '6', '5', '7', '8', '9', '0', '0', '5', '3', '4', '2', '7', '1', '9', '8', '5', '2', '6', '7', '9', '0', '0', '3', '3', '8', '5', '1', '0', '1', '0', '8', '6', '3', '0', '9', '7', '4', '0', '0', '3', '2', '5', '7', '4', '5', '3', '7', '1', '1', '5', '2', '0', '0', '2', '7', '7', '8', '6', '6', '3', '0', '7', '1', '7', '5', '0', '4', '9', '1', '9', '2', '3', '7', '5', '8', '2', '4', '2', '0', '7', '"', ',']

theorem object_fragment0317071_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0317071Field007Chars00 ++ tail)) fragment0317071Acc00700 =
      SourceJson.object (fuel + 238) (SourceJson.white tail) fragment0317071Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317071_object_field_007"
  err.flush

noncomputable def fragment0317071Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0317071Field008Value00 : SourceJson := .str (String.ofList ['1', '6', '5', '5', '7', '7', '8', '2', '3', '5', '8', '5', '7', '2', '9', '8'])
noncomputable def fragment0317071Acc00900 : List (String × SourceJson) := (fragment0317071Field008Key00, fragment0317071Field008Value00) :: fragment0317071Acc00800
noncomputable def fragment0317071Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '5', '5', '7', '7', '8', '2', '3', '5', '8', '5', '7', '2', '9', '8', '"', ',']

theorem object_fragment0317071_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0317071Field008Chars00 ++ tail)) fragment0317071Acc00800 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment0317071Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317071_object_field_008"
  err.flush

noncomputable def fragment0317071Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0317071Field009Value00 : SourceJson := .str (String.ofList ['1', '4', '4', '6', '4', '4', '9', '3', '9', '8', '5', '6', '7', '0', '6', '8', '5'])
noncomputable def fragment0317071Acc01000 : List (String × SourceJson) := (fragment0317071Field009Key00, fragment0317071Field009Value00) :: fragment0317071Acc00900
noncomputable def fragment0317071Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '4', '6', '4', '4', '9', '3', '9', '8', '5', '6', '7', '0', '6', '8', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0317071_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0317071Field009Chars00 ++ tail)) fragment0317071Acc00900 =
      .ok (.obj (fragment0317071Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317071_object_field_009"
  err.flush

noncomputable def fragment0317071Chars : List Char := '{' :: (fragment0317071Field000Chars00 ++ fragment0317071Field001Chars00 ++ fragment0317071Field002Chars00 ++ fragment0317071Field003Chars00 ++ fragment0317071Field004Chars00 ++ fragment0317071Field005Chars00 ++ fragment0317071Field006Chars00 ++ fragment0317071Field007Chars00 ++ fragment0317071Field008Chars00 ++ fragment0317071Field009Chars00)
noncomputable def fragment0317071Value : SourceJson := .obj (fragment0317071Acc01000.reverse)

theorem value_fragment0317071 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 247) (fragment0317071Chars ++ tail) =
      .ok (fragment0317071Value, tail) := by
  have hinput : fragment0317071Chars ++ tail = '{' :: (fragment0317071Field000Chars00 ++ (fragment0317071Field001Chars00 ++ (fragment0317071Field002Chars00 ++ (fragment0317071Field003Chars00 ++ (fragment0317071Field004Chars00 ++ (fragment0317071Field005Chars00 ++ (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0317071Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 247) (fragment0317071Chars ++ tail) =
        SourceJson.value (fuel + 247) ('{' :: (fragment0317071Field000Chars00 ++ (fragment0317071Field001Chars00 ++ (fragment0317071Field002Chars00 ++ (fragment0317071Field003Chars00 ++ (fragment0317071Field004Chars00 ++ (fragment0317071Field005Chars00 ++ (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 247)) hinput
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0317071Field000Chars00 ++ (fragment0317071Field001Chars00 ++ (fragment0317071Field002Chars00 ++ (fragment0317071Field003Chars00 ++ (fragment0317071Field004Chars00 ++ (fragment0317071Field005Chars00 ++ (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail)))))))))))) fragment0317071Acc00000 := by rfl
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0317071Field001Chars00 ++ (fragment0317071Field002Chars00 ++ (fragment0317071Field003Chars00 ++ (fragment0317071Field004Chars00 ++ (fragment0317071Field005Chars00 ++ (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail))))))))))) fragment0317071Acc00100 := object_fragment0317071_field_000 fuel (fragment0317071Field001Chars00 ++ (fragment0317071Field002Chars00 ++ (fragment0317071Field003Chars00 ++ (fragment0317071Field004Chars00 ++ (fragment0317071Field005Chars00 ++ (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0317071Field002Chars00 ++ (fragment0317071Field003Chars00 ++ (fragment0317071Field004Chars00 ++ (fragment0317071Field005Chars00 ++ (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail)))))))))) fragment0317071Acc00200 := object_fragment0317071_field_001 fuel (fragment0317071Field002Chars00 ++ (fragment0317071Field003Chars00 ++ (fragment0317071Field004Chars00 ++ (fragment0317071Field005Chars00 ++ (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0317071Field003Chars00 ++ (fragment0317071Field004Chars00 ++ (fragment0317071Field005Chars00 ++ (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail))))))))) fragment0317071Acc00300 := object_fragment0317071_field_002 fuel (fragment0317071Field003Chars00 ++ (fragment0317071Field004Chars00 ++ (fragment0317071Field005Chars00 ++ (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0317071Field004Chars00 ++ (fragment0317071Field005Chars00 ++ (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail)))))))) fragment0317071Acc00400 := object_fragment0317071_field_003 fuel (fragment0317071Field004Chars00 ++ (fragment0317071Field005Chars00 ++ (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0317071Field005Chars00 ++ (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail))))))) fragment0317071Acc00500 := object_fragment0317071_field_004 fuel (fragment0317071Field005Chars00 ++ (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 240) (SourceJson.white (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail)))))) fragment0317071Acc00600 := object_fragment0317071_field_005 fuel (fragment0317071Field006Chars00 ++ (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail))))) fragment0317071Acc00700 := object_fragment0317071_field_006 fuel (fragment0317071Field007Chars00 ++ (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail)))) fragment0317071Acc00800 := object_fragment0317071_field_007 fuel (fragment0317071Field008Chars00 ++ (fragment0317071Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0317071Field009Chars00 ++ (tail))) fragment0317071Acc00900 := object_fragment0317071_field_008 fuel (fragment0317071Field009Chars00 ++ (tail))
    _ = .ok (fragment0317071Value, tail) := object_fragment0317071_field_009 fuel (tail)

noncomputable def fragment0318710Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0318710Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0318710Field000Value00 : SourceJson := .number (String.ofList ['5', '4'])
noncomputable def fragment0318710Acc00100 : List (String × SourceJson) := (fragment0318710Field000Key00, fragment0318710Field000Value00) :: fragment0318710Acc00000
noncomputable def fragment0318710Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '4', ',']

theorem object_fragment0318710_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0318710Field000Chars00 ++ tail)) fragment0318710Acc00000 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0318710Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318710_object_field_000"
  err.flush

noncomputable def fragment0318710Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0318710Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['7'])]
noncomputable def fragment0318710Acc00200 : List (String × SourceJson) := (fragment0318710Field001Key00, fragment0318710Field001Value00) :: fragment0318710Acc00100
noncomputable def fragment0318710Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0318710_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0318710Field001Chars00 ++ tail)) fragment0318710Acc00100 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0318710Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318710_object_field_001"
  err.flush

noncomputable def fragment0318710Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0318710Field002Value00 : SourceJson := .str (String.ofList ['3', '0', '9', '2', '4', '0', '5', '3', '9', '8', '4', '4', '2', '2', '1', '5', '7', '8', '6', '3', '2', '5', '1', '7', '0', '8', '2', '6', '4', '8', '7', '5', '4', '1', '7', '4', '1', '4', '8', '0', '3', '8', '2', '1', '1', '/', '9', '8', '7', '5', '3', '4', '1', '5', '2', '1', '5', '0', '3', '1', '7', '7', '9', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0318710Acc00300 : List (String × SourceJson) := (fragment0318710Field002Key00, fragment0318710Field002Value00) :: fragment0318710Acc00200
noncomputable def fragment0318710Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '0', '9', '2', '4', '0', '5', '3', '9', '8', '4', '4', '2', '2', '1', '5', '7', '8', '6', '3', '2', '5', '1', '7', '0', '8', '2', '6', '4', '8', '7', '5', '4', '1', '7', '4', '1', '4', '8', '0', '3', '8', '2', '1', '1', '/', '9', '8', '7', '5', '3', '4', '1', '5', '2', '1', '5', '0', '3', '1', '7', '7', '9', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0318710_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0318710Field002Chars00 ++ tail)) fragment0318710Acc00200 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0318710Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318710_object_field_002"
  err.flush

noncomputable def fragment0318710Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0318710Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0318710Acc00400 : List (String × SourceJson) := (fragment0318710Field003Key00, fragment0318710Field003Value00) :: fragment0318710Acc00300
noncomputable def fragment0318710Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0318710_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0318710Field003Chars00 ++ tail)) fragment0318710Acc00300 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0318710Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318710_object_field_003"
  err.flush

noncomputable def fragment0318710Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0318710Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '3', '1', '1', '7', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0318710Acc00500 : List (String × SourceJson) := (fragment0318710Field004Key00, fragment0318710Field004Value00) :: fragment0318710Acc00400
noncomputable def fragment0318710Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '3', '1', '1', '7', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0318710_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0318710Field004Chars00 ++ tail)) fragment0318710Acc00400 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0318710Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318710_object_field_004"
  err.flush

noncomputable def fragment0318710Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0318710Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '1', '5', '6', '3', '0', '4', '0', '2', '6', '9', '/', '5', '9', '4', '2', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '6', '7', '7', '2', '7', '0', '1', '3', '2', '1', '/', '2', '3', '7', '6', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '9', '7', '0', '6', '0', '4', '7', '3', '0', '8', '9', '/', '1', '4', '2', '6', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '6', '5', '1', '9', '2', '7', '8', '8', '2', '8', '7', '/', '3', '3', '2', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '5', '3', '5', '1', '3', '5', '7', '8', '9', '9', '/', '6', '2', '3', '9', '3', '6', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '8', '9', '7', '0', '9', '6', '7', '2', '0', '1', '/', '1', '4', '2', '6', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '8', '3', '3', '4', '5', '8', '0', '5', '3', '/', '5', '2', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '1', '3', '5', '2', '9', '8', '2', '9', '8', '9', '7', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '4', '3', '4', '3', '1', '7', '9', '1', '3', '5', '1', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '1', '3', '8', '8', '4', '9', '9', '3', '4', '7', '1', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0318710Acc00600 : List (String × SourceJson) := (fragment0318710Field005Key00, fragment0318710Field005Value00) :: fragment0318710Acc00500
noncomputable def fragment0318710Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '5', '6', '3', '0', '4', '0', '2', '6', '9', '/', '5', '9', '4', '2', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '6', '7', '7', '2', '7', '0', '1', '3', '2', '1', '/', '2', '3', '7', '6', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '9', '7', '0', '6', '0', '4', '7', '3', '0', '8', '9', '/', '1', '4', '2', '6', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '6', '5', '1', '9', '2', '7', '8', '8', '2', '8', '7', '/', '3', '3', '2', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '5', '3', '5', '1', '3', '5', '7', '8', '9', '9', '/', '6', '2', '3', '9', '3', '6', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '8', '9', '7', '0', '9', '6', '7', '2', '0', '1', '/', '1', '4', '2', '6', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '8', '3', '3', '4', '5', '8', '0', '5', '3', '/', '5', '2', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '1', '3', '5', '2', '9', '8', '2', '9', '8', '9', '7', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '4', '3', '4', '3', '1', '7', '9', '1', '3', '5', '1', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '1', '3', '8', '8', '4', '9', '9', '3', '4', '7', '1', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0318710_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0318710Field005Chars00 ++ tail)) fragment0318710Acc00500 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0318710Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318710_object_field_005"
  err.flush

noncomputable def fragment0318710Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0318710Field006Value00 : SourceJson := .str (String.ofList ['3', '1', '7', '7', '9', '6', '1', '4', '5', '0', '6', '6', '7', '7', '9', '3', '4', '9', '1', '6', '0', '9', '0', '9', '7', '9', '6', '0', '4', '2', '4', '2', '1', '7', '6', '8', '2', '3', '1', '1', '1', '6', '7', '9', '0', '2', '2', '9', '/', '8', '1', '8', '4', '5', '7', '7', '3', '3', '2', '4', '1', '0', '2', '3', '0', '3', '8', '7', '6', '3', '0', '2', '7', '6', '1', '5', '0', '3', '0', '0', '5', '2', '0', '2', '9', '3', '4', '7', '4', '2', '1', '9', '8', '6', '5', '3', '4', '5', '8', '4', '7', '8', '6', '2', '6', '4', '7', '1', '9', '2', '0'])
noncomputable def fragment0318710Acc00700 : List (String × SourceJson) := (fragment0318710Field006Key00, fragment0318710Field006Value00) :: fragment0318710Acc00600
noncomputable def fragment0318710Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '1', '7', '7', '9', '6', '1', '4', '5', '0', '6', '6', '7', '7', '9', '3', '4', '9', '1', '6', '0', '9', '0', '9', '7', '9', '6', '0', '4', '2', '4', '2', '1', '7', '6', '8', '2', '3', '1', '1', '1', '6', '7', '9', '0', '2', '2', '9', '/', '8', '1', '8', '4', '5', '7', '7', '3', '3', '2', '4', '1', '0', '2', '3', '0', '3', '8', '7', '6', '3', '0', '2', '7', '6', '1', '5', '0', '3', '0', '0', '5', '2', '0', '2', '9', '3', '4', '7', '4', '2', '1', '9', '8', '6', '5', '3', '4', '5', '8', '4', '7', '8', '6', '2', '6', '4', '7', '1', '9', '2', '0', '"', ',']

theorem object_fragment0318710_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0318710Field006Chars00 ++ tail)) fragment0318710Acc00600 =
      SourceJson.object (fuel + 222) (SourceJson.white tail) fragment0318710Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318710_object_field_006"
  err.flush

noncomputable def fragment0318710Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0318710Field007Value00 : SourceJson := .str (String.ofList ['2', '4', '2', '3', '7', '2', '3', '1', '5', '9', '6', '0', '1', '2', '3', '7', '9', '2', '0', '4', '4', '0', '3', '2', '0', '8', '1', '5', '2', '3', '3', '4', '9', '4', '3', '8', '0', '7', '7', '8', '2', '6', '7', '6', '4', '3', '6', '1', '0', '8', '4', '3', '0', '5', '5', '5', '9', '0', '8', '1', '8', '9', '7', '2', '6', '8', '4', '2', '0', '3', '6', '5', '3', '3', '9', '0', '4', '5', '5', '1', '8', '3', '9', '8', '2', '8', '4', '9', '1', '2', '1', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '/', '1', '0', '6', '1', '0', '7', '0', '6', '5', '9', '3', '6', '6', '5', '4', '5', '1', '3', '0', '9', '4', '6', '3', '2', '7', '6', '4', '3', '3', '1', '4', '3', '3', '4', '2', '4', '5', '3', '0', '5', '1', '0', '7', '6', '5', '1', '4', '3', '2', '6', '1', '9', '6', '5', '4', '2', '7', '2', '1', '8', '9', '5', '2', '9', '5', '1', '8', '0', '8', '8', '1', '7', '4', '0', '7', '7', '7', '6', '2', '0', '1', '6', '6', '5', '4', '6', '6', '4', '3', '7', '0', '7', '1', '4', '2', '6', '1', '8', '8', '9', '6', '2', '2', '2', '4', '7', '3', '4', '2', '4', '3', '7', '6', '0', '7', '3'])
noncomputable def fragment0318710Acc00800 : List (String × SourceJson) := (fragment0318710Field007Key00, fragment0318710Field007Value00) :: fragment0318710Acc00700
noncomputable def fragment0318710Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '4', '2', '3', '7', '2', '3', '1', '5', '9', '6', '0', '1', '2', '3', '7', '9', '2', '0', '4', '4', '0', '3', '2', '0', '8', '1', '5', '2', '3', '3', '4', '9', '4', '3', '8', '0', '7', '7', '8', '2', '6', '7', '6', '4', '3', '6', '1', '0', '8', '4', '3', '0', '5', '5', '5', '9', '0', '8', '1', '8', '9', '7', '2', '6', '8', '4', '2', '0', '3', '6', '5', '3', '3', '9', '0', '4', '5', '5', '1', '8', '3', '9', '8', '2', '8', '4', '9', '1', '2', '1', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '/', '1', '0', '6', '1', '0', '7', '0', '6', '5', '9', '3', '6', '6', '5', '4', '5', '1', '3', '0', '9', '4', '6', '3', '2', '7', '6', '4', '3', '3', '1', '4', '3', '3', '4', '2', '4', '5', '3', '0', '5', '1', '0', '7', '6', '5', '1', '4', '3', '2', '6', '1', '9', '6', '5', '4', '2', '7', '2', '1', '8', '9', '5', '2', '9', '5', '1', '8', '0', '8', '8', '1', '7', '4', '0', '7', '7', '7', '6', '2', '0', '1', '6', '6', '5', '4', '6', '6', '4', '3', '7', '0', '7', '1', '4', '2', '6', '1', '8', '8', '9', '6', '2', '2', '2', '4', '7', '3', '4', '2', '4', '3', '7', '6', '0', '7', '3', '"', ',']

theorem object_fragment0318710_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment0318710Field007Chars00 ++ tail)) fragment0318710Acc00700 =
      SourceJson.object (fuel + 221) (SourceJson.white tail) fragment0318710Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318710_object_field_007"
  err.flush

noncomputable def fragment0318710Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0318710Field008Value00 : SourceJson := .str (String.ofList ['3', '0', '7', '6', '3', '2', '3', '1', '3', '8', '6', '4', '9', '2', '2'])
noncomputable def fragment0318710Acc00900 : List (String × SourceJson) := (fragment0318710Field008Key00, fragment0318710Field008Value00) :: fragment0318710Acc00800
noncomputable def fragment0318710Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '0', '7', '6', '3', '2', '3', '1', '3', '8', '6', '4', '9', '2', '2', '"', ',']

theorem object_fragment0318710_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 221) (SourceJson.white (fragment0318710Field008Chars00 ++ tail)) fragment0318710Acc00800 =
      SourceJson.object (fuel + 220) (SourceJson.white tail) fragment0318710Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318710_object_field_008"
  err.flush

noncomputable def fragment0318710Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0318710Field009Value00 : SourceJson := .str (String.ofList ['1', '8', '0', '9', '7', '4', '8', '7', '7', '2', '9', '3', '3', '8', '6', '4'])
noncomputable def fragment0318710Acc01000 : List (String × SourceJson) := (fragment0318710Field009Key00, fragment0318710Field009Value00) :: fragment0318710Acc00900
noncomputable def fragment0318710Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '0', '9', '7', '4', '8', '7', '7', '2', '9', '3', '3', '8', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0318710_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment0318710Field009Chars00 ++ tail)) fragment0318710Acc00900 =
      .ok (.obj (fragment0318710Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318710_object_field_009"
  err.flush

noncomputable def fragment0318710Chars : List Char := '{' :: (fragment0318710Field000Chars00 ++ fragment0318710Field001Chars00 ++ fragment0318710Field002Chars00 ++ fragment0318710Field003Chars00 ++ fragment0318710Field004Chars00 ++ fragment0318710Field005Chars00 ++ fragment0318710Field006Chars00 ++ fragment0318710Field007Chars00 ++ fragment0318710Field008Chars00 ++ fragment0318710Field009Chars00)
noncomputable def fragment0318710Value : SourceJson := .obj (fragment0318710Acc01000.reverse)

theorem value_fragment0318710 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 230) (fragment0318710Chars ++ tail) =
      .ok (fragment0318710Value, tail) := by
  have hinput : fragment0318710Chars ++ tail = '{' :: (fragment0318710Field000Chars00 ++ (fragment0318710Field001Chars00 ++ (fragment0318710Field002Chars00 ++ (fragment0318710Field003Chars00 ++ (fragment0318710Field004Chars00 ++ (fragment0318710Field005Chars00 ++ (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0318710Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 230) (fragment0318710Chars ++ tail) =
        SourceJson.value (fuel + 230) ('{' :: (fragment0318710Field000Chars00 ++ (fragment0318710Field001Chars00 ++ (fragment0318710Field002Chars00 ++ (fragment0318710Field003Chars00 ++ (fragment0318710Field004Chars00 ++ (fragment0318710Field005Chars00 ++ (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 230)) hinput
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0318710Field000Chars00 ++ (fragment0318710Field001Chars00 ++ (fragment0318710Field002Chars00 ++ (fragment0318710Field003Chars00 ++ (fragment0318710Field004Chars00 ++ (fragment0318710Field005Chars00 ++ (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail)))))))))))) fragment0318710Acc00000 := by rfl
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0318710Field001Chars00 ++ (fragment0318710Field002Chars00 ++ (fragment0318710Field003Chars00 ++ (fragment0318710Field004Chars00 ++ (fragment0318710Field005Chars00 ++ (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail))))))))))) fragment0318710Acc00100 := object_fragment0318710_field_000 fuel (fragment0318710Field001Chars00 ++ (fragment0318710Field002Chars00 ++ (fragment0318710Field003Chars00 ++ (fragment0318710Field004Chars00 ++ (fragment0318710Field005Chars00 ++ (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0318710Field002Chars00 ++ (fragment0318710Field003Chars00 ++ (fragment0318710Field004Chars00 ++ (fragment0318710Field005Chars00 ++ (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail)))))))))) fragment0318710Acc00200 := object_fragment0318710_field_001 fuel (fragment0318710Field002Chars00 ++ (fragment0318710Field003Chars00 ++ (fragment0318710Field004Chars00 ++ (fragment0318710Field005Chars00 ++ (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0318710Field003Chars00 ++ (fragment0318710Field004Chars00 ++ (fragment0318710Field005Chars00 ++ (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail))))))))) fragment0318710Acc00300 := object_fragment0318710_field_002 fuel (fragment0318710Field003Chars00 ++ (fragment0318710Field004Chars00 ++ (fragment0318710Field005Chars00 ++ (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0318710Field004Chars00 ++ (fragment0318710Field005Chars00 ++ (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail)))))))) fragment0318710Acc00400 := object_fragment0318710_field_003 fuel (fragment0318710Field004Chars00 ++ (fragment0318710Field005Chars00 ++ (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0318710Field005Chars00 ++ (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail))))))) fragment0318710Acc00500 := object_fragment0318710_field_004 fuel (fragment0318710Field005Chars00 ++ (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail)))))) fragment0318710Acc00600 := object_fragment0318710_field_005 fuel (fragment0318710Field006Chars00 ++ (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail))))) fragment0318710Acc00700 := object_fragment0318710_field_006 fuel (fragment0318710Field007Chars00 ++ (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 221) (SourceJson.white (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail)))) fragment0318710Acc00800 := object_fragment0318710_field_007 fuel (fragment0318710Field008Chars00 ++ (fragment0318710Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment0318710Field009Chars00 ++ (tail))) fragment0318710Acc00900 := object_fragment0318710_field_008 fuel (fragment0318710Field009Chars00 ++ (tail))
    _ = .ok (fragment0318710Value, tail) := object_fragment0318710_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0053_before_reader"
  err.flush

noncomputable def chunk0053LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0053SuffixChars00 : List Char := [',']
noncomputable def chunk0053Chars00 : List Char := chunk0053LeadChars00 ++ fragment0317071Chars ++ chunk0053SuffixChars00
noncomputable def chunk0053Push00 (acc : List SourceJson) : List SourceJson := fragment0317071Value :: acc

noncomputable def chunk0053AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0053_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 551)
      (SourceJson.white (chunk0053LeadChars00 ++ (fragment0317071Chars ++ rest))) acc =
      (SourceJson.value (fuel + 550) (fragment0317071Chars ++ rest)).bind
        (chunk0053AfterValue00 (fuel + 550) acc) := by rfl

theorem array_chunk0053 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 551) (SourceJson.white (chunk0053Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 550) (SourceJson.white tail) (chunk0053Push00 acc) := by
  have hinput : chunk0053Chars00 ++ tail = chunk0053LeadChars00 ++ (fragment0317071Chars ++ (chunk0053SuffixChars00 ++ tail)) := by
    simp only [chunk0053Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 551) (SourceJson.white (chunk0053Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 551)
          (SourceJson.white (chunk0053LeadChars00 ++ (fragment0317071Chars ++ (chunk0053SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 551) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 550) (fragment0317071Chars ++ (chunk0053SuffixChars00 ++ tail))).bind
        (chunk0053AfterValue00 (fuel + 550) acc) := array_chunk0053_head fuel (chunk0053SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0317071Value, chunk0053SuffixChars00 ++ tail)).bind
        (chunk0053AfterValue00 (fuel + 550) acc) :=
      congrArg (fun result => result.bind (chunk0053AfterValue00 (fuel + 550) acc))
        (value_fragment0317071 (fuel + 303) (chunk0053SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 550) (SourceJson.white tail) (chunk0053Push00 acc) := by rfl

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
noncomputable def chunk0054Chars00 : List Char := chunk0054LeadChars00 ++ fragment0318710Chars ++ chunk0054SuffixChars00
noncomputable def chunk0054Push00 (acc : List SourceJson) : List SourceJson := fragment0318710Value :: acc

noncomputable def chunk0054AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0054_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 550)
      (SourceJson.white (chunk0054LeadChars00 ++ (fragment0318710Chars ++ rest))) acc =
      (SourceJson.value (fuel + 549) (fragment0318710Chars ++ rest)).bind
        (chunk0054AfterValue00 (fuel + 549) acc) := by rfl

theorem array_chunk0054 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 550) (SourceJson.white (chunk0054Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 549) (SourceJson.white tail) (chunk0054Push00 acc) := by
  have hinput : chunk0054Chars00 ++ tail = chunk0054LeadChars00 ++ (fragment0318710Chars ++ (chunk0054SuffixChars00 ++ tail)) := by
    simp only [chunk0054Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 550) (SourceJson.white (chunk0054Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 550)
          (SourceJson.white (chunk0054LeadChars00 ++ (fragment0318710Chars ++ (chunk0054SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 550) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 549) (fragment0318710Chars ++ (chunk0054SuffixChars00 ++ tail))).bind
        (chunk0054AfterValue00 (fuel + 549) acc) := array_chunk0054_head fuel (chunk0054SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0318710Value, chunk0054SuffixChars00 ++ tail)).bind
        (chunk0054AfterValue00 (fuel + 549) acc) :=
      congrArg (fun result => result.bind (chunk0054AfterValue00 (fuel + 549) acc))
        (value_fragment0318710 (fuel + 319) (chunk0054SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 549) (SourceJson.white tail) (chunk0054Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0054_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0053Chars00 ++ chunk0054Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0054Push00 (chunk0053Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 551) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 549) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0053Chars00 ++ (chunk0054Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 551) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 551) (SourceJson.white (chunk0053Chars00 ++ (chunk0054Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 551) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 550) (SourceJson.white (chunk0054Chars00 ++ (tail))) (chunk0053Push00 (acc)) := array_chunk0053 fuel (chunk0054Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 549) (SourceJson.white tail) (blockPush acc) := array_chunk0054 fuel (tail) (chunk0053Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 317065).take 3236 = blockChars := by rfl

theorem block_original_split : sourceRest 317065 = blockChars ++ sourceRest 320301 := by
  calc
    sourceRest 317065 = (sourceRest 317065).take 3236 ++ (sourceRest 317065).drop 3236 :=
      (List.take_append_drop 3236 (sourceRest 317065)).symm
    _ = blockChars ++ (sourceRest 317065).drop 3236 :=
      congrArg (fun part => part ++ (sourceRest 317065).drop 3236) block_original_prefix
    _ = blockChars ++ sourceRest 320301 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 317065 3236)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 551) (SourceJson.white (sourceRest 317065)) acc =
      SourceJson.array (fuel + 549) (SourceJson.white (sourceRest 320301)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 551) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 320301) acc)

#print axioms object_fragment0317071_field_000
#print axioms object_fragment0317071_field_001
#print axioms object_fragment0317071_field_002
#print axioms object_fragment0317071_field_003
#print axioms object_fragment0317071_field_004
#print axioms object_fragment0317071_field_005
#print axioms object_fragment0317071_field_006
#print axioms object_fragment0317071_field_007
#print axioms object_fragment0317071_field_008
#print axioms object_fragment0317071_field_009
#print axioms value_fragment0317071
#print axioms object_fragment0318710_field_000
#print axioms object_fragment0318710_field_001
#print axioms object_fragment0318710_field_002
#print axioms object_fragment0318710_field_003
#print axioms object_fragment0318710_field_004
#print axioms object_fragment0318710_field_005
#print axioms object_fragment0318710_field_006
#print axioms object_fragment0318710_field_007
#print axioms object_fragment0318710_field_008
#print axioms object_fragment0318710_field_009
#print axioms value_fragment0318710
#print axioms array_chunk0053_head
#print axioms array_chunk0053
#print axioms array_chunk0054_head
#print axioms array_chunk0054
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock027

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
